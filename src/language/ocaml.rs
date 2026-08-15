use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use sha2::{Digest, Sha256};
use tree_sitter::{Node, Parser, Tree};

use super::{FileContext, FrontendResult, LanguageBackend, ProjectContext};
use crate::model::{
    CallLabel, CallSite, CallSiteId, CallSyntax, CallTarget, DispatchCandidate, DispatchEvidence,
    DispatchResolution, FileAnalysis, FunctionInfo, LanguageFact, LanguageId, SourceSpan, SymbolId,
    UnresolvedReason,
};
use crate::source::{collect_files_with_extension, collect_source_files, paths_match};

static OCAML_TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);
const OCAML_EXTRACTOR_SOURCE: &str = include_str!("../../support/ocaml/extract.ml");

thread_local! {
    /// Expression flow performs many small parses during specialization. A
    /// parser is reusable after each returned `Tree`, so keep one per worker
    /// thread instead of rebuilding its language tables for every argument.
    static OCAML_EXPRESSION_PARSER: RefCell<Option<Parser>> = RefCell::new({
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_ocaml::LANGUAGE_OCAML.into())
            .ok()
            .map(|_| parser)
    });
}

fn parse_ocaml_expression(source: &str) -> Option<Tree> {
    OCAML_EXPRESSION_PARSER.with(|parser| parser.borrow_mut().as_mut()?.parse(source, None))
}

/// OCaml's source-label stage. Dune projects overlay compiler-libs Typedtree
/// paths in `analyze_semantic_project`; standalone source sets retain
/// conservative module/local resolution and the same graph contract.
#[derive(Default)]
pub struct OcamlFrontend;

pub static OCAML_BACKEND: OcamlFrontend = OcamlFrontend;

/// Analyze a Dune project from compiler-generated `.cmt` Typedtrees. Source
/// parsing remains responsible for language-shaped labels; resolved `Path.t`
/// values from compiler-libs are authoritative for call identity.
pub fn analyze_semantic_project(root: &Path) -> FrontendResult<FileAnalysis> {
    let root = root.canonicalize()?;
    let build = Command::new("dune")
        .args(["build", "@check", "--display", "quiet"])
        .current_dir(&root)
        .output()
        .map_err(|error| {
            io::Error::new(
                error.kind(),
                format!("failed to run Dune for OCaml semantic analysis: {error}"),
            )
        })?;
    if !build.status.success() {
        let diagnostic = String::from_utf8_lossy(&build.stderr).trim().to_owned();
        return Err(io::Error::other(if diagnostic.is_empty() {
            format!("Dune semantic build exited with {}", build.status)
        } else {
            diagnostic
        })
        .into());
    }

    let helper = OcamlExtractor::compile()?;
    let cmt_files = collect_files_with_extension(&root.join("_build"), "cmt")?;
    let mut events = Vec::new();
    for cmt in cmt_files {
        let output = Command::new(helper.executable()).arg(&cmt).output()?;
        if !output.status.success() {
            let diagnostic = String::from_utf8_lossy(&output.stderr).trim().to_owned();
            return Err(io::Error::other(format!(
                "compiler-libs could not read {}: {}",
                cmt.display(),
                diagnostic
            ))
            .into());
        }
        events.extend(parse_typed_events(
            &root,
            &String::from_utf8(output.stdout)?,
        )?);
    }

    let source_files = collect_source_files(&root, &["ml", "mli"])?;
    let mut analysis = FileAnalysis::default();
    for file in source_files {
        let source = fs::read_to_string(&file)?;
        let module = ocaml_file_module_path(&root, &file);
        let mut file_analysis = analyze_ocaml_syntax(
            &FileContext {
                path: &file,
                module: &module,
            },
            &source,
        )?;
        apply_typed_events(&mut file_analysis, &events);
        analysis.append(file_analysis);
    }
    resolve_ocaml_function_values(&mut analysis);
    Ok(analysis)
}

/// Analyze an OCaml source set without a Dune project. This is used for
/// standalone source trees; Dune projects use `analyze_semantic_project`.
pub fn analyze_source_project(root: &Path) -> FrontendResult<FileAnalysis> {
    let root = root.canonicalize()?;
    let files = collect_source_files(&root, &["ml", "mli"])?;
    let mut analysis = FileAnalysis::default();
    for file in files {
        let source = fs::read_to_string(&file)?;
        let module = ocaml_file_module_path(&root, &file);
        let mut file_analysis = analyze_ocaml_syntax(
            &FileContext {
                path: &file,
                module: &module,
            },
            &source,
        )?;
        if let Some(events) = standalone_typed_events(&file, &source)? {
            apply_typed_events(&mut file_analysis, &events);
        }
        analysis.append(file_analysis);
    }
    resolve_ocaml_function_values(&mut analysis);
    Ok(analysis)
}

struct OcamlExtractor {
    directory: PathBuf,
}

impl OcamlExtractor {
    fn compile() -> FrontendResult<Self> {
        let sequence = OCAML_TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir().join(format!(
            "diffkit-ocaml-extractor-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory)?;
        let extractor = Self { directory };
        let source = extractor.directory.join("extract.ml");
        fs::write(&source, OCAML_EXTRACTOR_SOURCE)?;
        let output = Command::new("ocamlc")
            .args(["-I", "+compiler-libs", "ocamlcommon.cma"])
            .arg(&source)
            .arg("-o")
            .arg(extractor.executable())
            .output()
            .map_err(|error| {
                io::Error::new(
                    error.kind(),
                    format!("failed to start ocamlc for compiler-libs adapter: {error}"),
                )
            })?;
        if !output.status.success() {
            let diagnostic = String::from_utf8_lossy(&output.stderr).trim().to_owned();
            return Err(io::Error::other(format!(
                "failed to compile compiler-libs adapter: {diagnostic}"
            ))
            .into());
        }
        Ok(extractor)
    }

    fn executable(&self) -> PathBuf {
        self.directory.join("extract")
    }
}

impl Drop for OcamlExtractor {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

#[derive(Clone, Debug)]
struct TypedCallEvent {
    target: Option<String>,
    signature: Option<String>,
    span: SourceSpan,
}

impl LanguageBackend for OcamlFrontend {
    fn language(&self) -> LanguageId {
        LanguageId::new("ocaml")
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["ml", "mli"]
    }

    fn analyze_file(
        &self,
        context: &FileContext<'_>,
        source: &str,
    ) -> FrontendResult<FileAnalysis> {
        let mut analysis = analyze_ocaml_syntax(context, source)?;
        if let Some(events) = standalone_typed_events(context.path, source)? {
            apply_typed_events(&mut analysis, &events);
        }
        resolve_ocaml_function_values(&mut analysis);
        Ok(analysis)
    }

    fn analyze_project(&self, context: &ProjectContext<'_>) -> FrontendResult<FileAnalysis> {
        if context.root.join("dune-project").is_file() {
            analyze_semantic_project(context.root)
        } else {
            analyze_source_project(context.root)
        }
    }
}

fn standalone_typed_events(
    source_path: &Path,
    source: &str,
) -> FrontendResult<Option<Vec<TypedCallEvent>>> {
    if Command::new("ocamlc").arg("-version").output().is_err() {
        return Ok(None);
    }
    let sequence = OCAML_TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let directory = std::env::temp_dir().join(format!(
        "diffkit-ocaml-source-{}-{sequence}",
        std::process::id()
    ));
    fs::create_dir(&directory)?;
    let capture = StandaloneOcamlCapture { directory };
    let extension = source_path
        .extension()
        .and_then(|extension| extension.to_str())
        .unwrap_or("ml");
    let temporary_source = capture.directory.join(format!("input.{extension}"));
    fs::write(&temporary_source, source)?;
    let compile = Command::new("ocamlc")
        .args(["-bin-annot", "-c"])
        .arg(&temporary_source)
        .current_dir(&capture.directory)
        .output()?;
    if !compile.status.success() {
        // A standalone snippet may intentionally depend on surrounding
        // modules. Keep the conservative graph, with unresolved calls marked
        // explicitly, instead of pretending the compiler accepted it.
        return Ok(None);
    }
    let annotation = if extension == "mli" {
        capture.directory.join("input.cmti")
    } else {
        capture.directory.join("input.cmt")
    };
    if !annotation.is_file() {
        return Ok(None);
    }
    let helper = OcamlExtractor::compile()?;
    let output = Command::new(helper.executable()).arg(annotation).output()?;
    if !output.status.success() {
        return Ok(None);
    }
    let mut events = parse_typed_events(&capture.directory, &String::from_utf8(output.stdout)?)?;
    for event in &mut events {
        event.span.file = source_path.to_path_buf();
    }
    Ok(Some(events))
}

struct StandaloneOcamlCapture {
    directory: PathBuf,
}

impl Drop for StandaloneOcamlCapture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

fn analyze_ocaml_syntax(context: &FileContext<'_>, source: &str) -> FrontendResult<FileAnalysis> {
    let mut parser = Parser::new();
    let language = if context.path.extension().and_then(|value| value.to_str()) == Some("mli") {
        tree_sitter_ocaml::LANGUAGE_OCAML_INTERFACE
    } else {
        tree_sitter_ocaml::LANGUAGE_OCAML
    };
    parser
        .set_language(&language.into())
        .map_err(|error| io::Error::other(format!("failed to load OCaml grammar: {error}")))?;
    let tree = parser
        .parse(source, None)
        .ok_or_else(|| io::Error::other("OCaml parser returned no syntax tree"))?;
    if tree.root_node().has_error() {
        return Err(io::Error::other(format!(
            "failed to parse OCaml source: {}",
            context.path.display()
        ))
        .into());
    }

    let mut analysis = FileAnalysis::default();
    analysis.source_files.insert(context.path.to_path_buf());
    let module = context
        .module
        .iter()
        .map(|part| ocaml_module_name(part))
        .collect::<Vec<_>>();
    analyze_structure(
        context.path,
        &module,
        tree.root_node(),
        source,
        &mut analysis,
    );
    disambiguate_ocaml_shadowed_bindings(&mut analysis);
    resolve_ocaml_recursive_groups(&mut analysis);
    resolve_local_callables(&mut analysis);
    redact_anonymous_call_arguments(&mut analysis);
    Ok(analysis)
}

#[derive(Clone)]
struct OcamlBindingRemap {
    old: SymbolId,
    new: SymbolId,
    owner_span: SourceSpan,
}

/// OCaml permits a later top-level `let` to shadow an earlier binding with the
/// same source path. `Path.name` deliberately omits compiler-local stamps, so
/// preserve that identity here before Typedtree call events are overlaid.
fn disambiguate_ocaml_shadowed_bindings(analysis: &mut FileAnalysis) {
    let mut groups = BTreeMap::<(PathBuf, Vec<String>, String), Vec<usize>>::new();
    for (index, function) in analysis.functions.iter().enumerate() {
        if function.id.container.is_none() {
            groups
                .entry((
                    function.span.file.clone(),
                    function.id.module.clone(),
                    function.id.name.clone(),
                ))
                .or_default()
                .push(index);
        }
    }

    let mut remaps = Vec::new();
    for indices in groups.values_mut().filter(|indices| indices.len() > 1) {
        indices.sort_by_key(|index| {
            let function = &analysis.functions[*index];
            (
                function.span.start_line,
                function.span.start_column,
                function.span.end_line,
                function.span.end_column,
            )
        });
        for (ordinal, index) in indices.iter().copied().enumerate() {
            let owner = analysis.functions[index].clone();
            let old_owner_text = owner.id.to_string();
            let mut new_owner = owner.id.clone();
            if ordinal + 1 != indices.len() {
                new_owner.name = format!("{}#binding{ordinal}", owner.id.name);
            }
            let new_owner_text = new_owner.to_string();

            for function in &mut analysis.functions {
                if function.span.file != owner.span.file || !owner.span.contains(&function.span) {
                    continue;
                }
                let old = function.id.clone();
                if old == owner.id {
                    function.id = new_owner.clone();
                } else if let Some(container) = &old.container
                    && container.contains(&old_owner_text)
                {
                    function.id.container =
                        Some(container.replacen(&old_owner_text, &new_owner_text, 1));
                } else {
                    continue;
                }
                remaps.push(OcamlBindingRemap {
                    old,
                    new: function.id.clone(),
                    owner_span: owner.span.clone(),
                });
            }
        }
    }

    for fact in &mut analysis.facts {
        if let Some(remap) = remaps.iter().find(|remap| {
            fact.subject == remap.old
                && fact.span.file == remap.owner_span.file
                && remap.owner_span.contains(&fact.span)
        }) {
            fact.subject = remap.new.clone();
        }
    }

    analysis.roots = analysis
        .roots
        .iter()
        .map(|root| {
            remaps
                .iter()
                .find(|remap| remap.old == *root)
                .map_or_else(|| root.clone(), |remap| remap.new.clone())
        })
        .collect();
}

fn resolve_ocaml_recursive_groups(analysis: &mut FileAnalysis) {
    let groups = analysis
        .facts
        .iter()
        .filter(|fact| fact.kind == "recursive-group")
        .fold(
            BTreeMap::<(PathBuf, String), Vec<SymbolId>>::new(),
            |mut groups, fact| {
                groups
                    .entry((fact.span.file.clone(), fact.value.clone()))
                    .or_default()
                    .push(fact.subject.clone());
                groups
            },
        );
    let function_index = analysis.functions.clone();
    for members in groups.values() {
        let owners = members
            .iter()
            .filter_map(|member| {
                function_index
                    .iter()
                    .find(|function| function.id == *member)
            })
            .collect::<Vec<_>>();
        for function in &mut analysis.functions {
            if !owners.iter().any(|owner| {
                owner.span.file == function.span.file && owner.span.contains(&function.span)
            }) {
                continue;
            }
            for call in &mut function.calls {
                let CallSyntax::Path(parts) = call.syntax.visible() else {
                    continue;
                };
                let Some(name) = parts.last() else {
                    continue;
                };
                let mut targets = owners
                    .iter()
                    .filter(|owner| {
                        local_callable_source_name(owner) == name
                            && (parts.len() == 1 || parts[..parts.len() - 1] == owner.id.module)
                    })
                    .map(|owner| owner.id.clone())
                    .collect::<Vec<_>>();
                targets.sort();
                targets.dedup();
                if targets.len() == 1 {
                    call.target = CallTarget::Direct(targets.remove(0));
                }
            }
        }
    }
}

fn ocaml_file_module_path(root: &Path, file: &Path) -> Vec<String> {
    let relative = file.strip_prefix(root).unwrap_or(file);
    relative
        .file_stem()
        .and_then(|stem| stem.to_str())
        .map(|stem| vec![stem.to_owned()])
        .unwrap_or_default()
}

fn parse_typed_events(root: &Path, output: &str) -> FrontendResult<Vec<TypedCallEvent>> {
    output
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let fields = line.split('\t').collect::<Vec<_>>();
            if fields.len() != 8 {
                return Err(
                    io::Error::other(format!("invalid compiler-libs event: {line}")).into(),
                );
            }
            let file = PathBuf::from(fields[2]);
            let file = if file.is_absolute() {
                file
            } else {
                root.join(file)
            };
            let file = dune_source_path(root, &file).unwrap_or(file);
            Ok(TypedCallEvent {
                target: (fields[0] == "direct").then(|| fields[1].to_owned()),
                signature: (!fields[7].is_empty()).then(|| fields[7].to_owned()),
                span: SourceSpan {
                    file,
                    start_line: fields[3].parse()?,
                    start_column: fields[4].parse()?,
                    start_byte: None,
                    end_line: fields[5].parse()?,
                    end_column: fields[6].parse()?,
                    end_byte: None,
                },
            })
        })
        .collect()
}

fn dune_source_path(root: &Path, file: &Path) -> Option<PathBuf> {
    let relative = file
        .strip_prefix(root.join("_build"))
        .ok()
        .or_else(|| file.strip_prefix("_build").ok())?;
    let components = relative.components().collect::<Vec<_>>();
    let skip = if components
        .first()
        .is_some_and(|component| component.as_os_str() == ".sandbox")
    {
        3
    } else {
        1
    };
    let candidate = components
        .get(skip..)?
        .iter()
        .fold(root.to_path_buf(), |path, component| {
            path.join(component.as_os_str())
        });
    candidate.is_file().then_some(candidate)
}

fn apply_typed_events(analysis: &mut FileAnalysis, events: &[TypedCallEvent]) {
    let parameters = ocaml_parameters(&analysis.functions, &analysis.facts);
    let local_values = ocaml_local_values(&analysis.facts);
    let local_symbols = analysis
        .functions
        .iter()
        .map(|function| function.id.clone())
        .collect::<BTreeSet<_>>();
    let mut claimed = BTreeSet::new();
    for function in &mut analysis.functions {
        for call in &mut function.calls {
            if matches!(
                &call.target,
                CallTarget::Direct(target) if local_symbols.contains(target)
            ) {
                continue;
            }
            if matches!(call.target, CallTarget::Dynamic { .. }) {
                continue;
            }
            let Some((event_index, event)) = events
                .iter()
                .enumerate()
                .filter(|(index, _)| !claimed.contains(index))
                .filter(|event| {
                    ocaml_source_files_match(&event.1.span.file, &call.span.file)
                        && event.1.span.overlaps(&call.span)
                })
                .min_by_key(|(_, event)| event.span.boundary_distance(&call.span))
            else {
                continue;
            };
            claimed.insert(event_index);
            if let Some(signature) = &event.signature {
                call.label.typed = Some(annotate_ocaml_call(&call.label.default, call, signature));
            }
            let is_flow_resolved_callable = match call.syntax.visible() {
                CallSyntax::Path(parts) => {
                    parameters.get(&function.id).is_some_and(|bindings| {
                        called_ocaml_parameter_index(parts, bindings, Some(&call.span)).is_some()
                    }) || (parts.len() == 1
                        && unique_ocaml_local_value(
                            &local_values,
                            &function.id,
                            &parts[0],
                            Some(&call.span),
                        )
                        .is_some())
                }
                _ => false,
            };
            call.target = match &event.target {
                _ if is_flow_resolved_callable => CallTarget::Unresolved,
                Some(target) => CallTarget::Direct(ocaml_path_symbol(target)),
                None => CallTarget::Indirect {
                    signature: event.signature.clone(),
                    reason: UnresolvedReason::OpaqueInput,
                },
            };
        }
    }
}

fn annotate_ocaml_call(label: &str, call: &CallSite, signature: &str) -> String {
    let arguments = ocaml_call_arguments(call);
    if arguments.is_empty() {
        return label.to_owned();
    }
    let mut types = split_ocaml_function_type(signature);
    if types.len() <= 1 {
        return label.to_owned();
    }
    types.pop(); // Return type is intentionally not rendered.
    if types.len() < arguments.len() {
        return label.to_owned();
    }
    let callee = match call.syntax.visible() {
        CallSyntax::Path(parts) => parts.join("."),
        CallSyntax::SelfMethod(method) => method.clone(),
        CallSyntax::Method { receiver, method } => format!("{receiver}#{method}"),
        CallSyntax::Expression(expression) => expression.clone(),
        CallSyntax::CompilerConfirmed(syntax) => syntax.key_fragment(),
    };
    let types = &types[types.len() - arguments.len()..];
    let annotated = arguments
        .iter()
        .zip(types)
        .map(|(argument, ty)| {
            let ty = ty.split_once(':').map_or(ty.as_str(), |(_, ty)| ty).trim();
            format!("({argument}: {ty})")
        })
        .collect::<Vec<_>>()
        .join(" ");
    format!("{callee} {annotated}")
}

fn split_ocaml_function_type(signature: &str) -> Vec<String> {
    let mut result = Vec::new();
    let mut start = 0usize;
    let mut depth = 0usize;
    let bytes = signature.as_bytes();
    let mut index = 0usize;
    while index + 1 < bytes.len() {
        match bytes[index] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth = depth.saturating_sub(1),
            b'-' if bytes[index + 1] == b'>' && depth == 0 => {
                result.push(signature[start..index].trim().to_owned());
                start = index + 2;
                index += 1;
            }
            _ => {}
        }
        index += 1;
    }
    result.push(signature[start..].trim().to_owned());
    result
}

fn ocaml_path_symbol(path: &str) -> SymbolId {
    let mut parts = path
        .trim_start_matches("global ")
        .split('.')
        .filter(|part| !part.is_empty())
        .map(|part| part.rsplit("__").next().unwrap_or(part).to_owned())
        .collect::<Vec<_>>();
    let name = parts.pop().unwrap_or_else(|| path.to_owned());
    SymbolId {
        language: LanguageId::new("ocaml"),
        module: parts,
        container: None,
        name,
    }
}

fn ocaml_source_files_match(left: &Path, right: &Path) -> bool {
    paths_match(left, right)
}

fn ocaml_module_name(value: &str) -> String {
    let mut characters = value.chars();
    let Some(first) = characters.next() else {
        return String::new();
    };
    first.to_uppercase().chain(characters).collect()
}

fn analyze_structure(
    file: &Path,
    module: &[String],
    structure: Node<'_>,
    source: &str,
    analysis: &mut FileAnalysis,
) {
    let mut cursor = structure.walk();
    for child in structure.named_children(&mut cursor) {
        match child.kind() {
            "module_definition" => analyze_module_definition(file, module, child, source, analysis),
            "value_definition" => analyze_value_definition(file, module, child, source, analysis),
            _ => {}
        }
    }
}

fn analyze_module_definition(
    file: &Path,
    module: &[String],
    definition: Node<'_>,
    source: &str,
    analysis: &mut FileAnalysis,
) {
    let mut cursor = definition.walk();
    for binding in definition
        .named_children(&mut cursor)
        .filter(|child| child.kind() == "module_binding")
    {
        let Some(name_node) = direct_named_child(binding, "module_name") else {
            continue;
        };
        let Some(body) = binding.child_by_field_name("body") else {
            continue;
        };
        if body.kind() == "module_path" {
            analysis.facts.push(LanguageFact {
                subject: SymbolId {
                    language: LanguageId::new("ocaml"),
                    module: module.to_vec(),
                    container: None,
                    name: node_text(name_node, source).to_owned(),
                },
                namespace: LanguageId::new("ocaml"),
                kind: "module-alias".to_owned(),
                key: "target".to_owned(),
                value: normalize_source(node_text(body, source)),
                span: tree_sitter_span(file, binding),
            });
            continue;
        }
        if body.kind() == "module_application" {
            let Some((functor, arguments)) = ocaml_module_application(body, source) else {
                continue;
            };
            analysis.facts.push(LanguageFact {
                subject: SymbolId {
                    language: LanguageId::new("ocaml"),
                    module: module.to_vec(),
                    container: None,
                    name: node_text(name_node, source).to_owned(),
                },
                namespace: LanguageId::new("ocaml"),
                kind: "functor-instance".to_owned(),
                key: functor,
                value: arguments.join("\t"),
                span: tree_sitter_span(file, binding),
            });
            continue;
        }
        for (index, parameter) in direct_named_children(binding, "module_parameter")
            .into_iter()
            .enumerate()
        {
            let Some(parameter_name) = direct_named_child(parameter, "module_name") else {
                continue;
            };
            analysis.facts.push(LanguageFact {
                subject: SymbolId {
                    language: LanguageId::new("ocaml"),
                    module: module.to_vec(),
                    container: None,
                    name: node_text(name_node, source).to_owned(),
                },
                namespace: LanguageId::new("ocaml"),
                kind: "functor-parameter".to_owned(),
                key: index.to_string(),
                value: node_text(parameter_name, source).to_owned(),
                span: tree_sitter_span(file, parameter),
            });
        }
        let body = if body.kind() == "structure" {
            body
        } else if let Some(structure) = first_descendant_of_kind(body, "structure") {
            structure
        } else {
            continue;
        };

        let mut nested_module = module.to_vec();
        nested_module.push(node_text(name_node, source).to_owned());
        analyze_structure(file, &nested_module, body, source, analysis);
    }
}

fn ocaml_module_application(node: Node<'_>, source: &str) -> Option<(String, Vec<String>)> {
    if node.kind() == "module_path" {
        return Some((normalize_source(node_text(node, source)), Vec::new()));
    }
    if node.kind() != "module_application" {
        return None;
    }
    let functor = node.child_by_field_name("functor")?;
    let (functor, mut arguments) = ocaml_module_application(functor, source)?;
    let argument = node.child_by_field_name("argument")?;
    let argument = if argument.kind() == "module_path" {
        argument
    } else {
        first_descendant_of_kind(argument, "module_path")?
    };
    arguments.push(normalize_source(node_text(argument, source)));
    Some((functor, arguments))
}

fn first_descendant_of_kind<'tree>(node: Node<'tree>, kind: &str) -> Option<Node<'tree>> {
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        if child.kind() == kind {
            return Some(child);
        }
        if let Some(found) = first_descendant_of_kind(child, kind) {
            return Some(found);
        }
    }
    None
}

fn analyze_value_definition(
    file: &Path,
    module: &[String],
    definition: Node<'_>,
    source: &str,
    analysis: &mut FileAnalysis,
) {
    let recursive_group = normalize_source(node_text(definition, source))
        .starts_with("let rec ")
        .then(|| {
            format!(
                "{}:{}-{}:{}",
                definition.start_position().row,
                definition.start_position().column,
                definition.end_position().row,
                definition.end_position().column,
            )
        });
    let mut cursor = definition.walk();
    for binding in definition
        .named_children(&mut cursor)
        .filter(|child| child.kind() == "let_binding")
    {
        if let Some(function) = function_from_binding(file, module, binding, source, analysis) {
            if let Some(group) = &recursive_group {
                analysis.facts.push(LanguageFact {
                    subject: function.id.clone(),
                    namespace: LanguageId::new("ocaml"),
                    kind: "recursive-group".to_owned(),
                    key: local_callable_source_name(&function).to_owned(),
                    value: group.clone(),
                    span: function.span.clone(),
                });
            }
            let owner = function.id.clone();
            analysis.functions.push(function);
            collect_nested_callables_from_binding(file, module, &owner, binding, source, analysis);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn collect_nested_callables(
    file: &Path,
    module: &[String],
    owner: &SymbolId,
    node: Node<'_>,
    source: &str,
    analysis: &mut FileAnalysis,
    ordinal: &mut usize,
) {
    if node.kind() == "let_binding" {
        let facts_start = analysis.facts.len();
        if let Some(mut function) = function_from_binding(file, module, node, source, analysis) {
            let display_name = function.id.name.clone();
            let old_id = function.id.clone();
            let current_ordinal = *ordinal;
            *ordinal += 1;
            function.id.container = Some(owner.to_string());
            function.id.name = format!("{display_name}#closure{current_ordinal}");
            function.label = local_callable_label(&function.label, &display_name, current_ordinal);
            for fact in &mut analysis.facts[facts_start..] {
                if fact.subject == old_id {
                    fact.subject = function.id.clone();
                }
            }
            if let Some(scope) = ocaml_local_callable_scope(node, source) {
                analysis.facts.push(LanguageFact {
                    subject: function.id.clone(),
                    namespace: LanguageId::new("ocaml"),
                    kind: "local-callable-scope".to_owned(),
                    key: display_name.clone(),
                    value: String::new(),
                    span: tree_sitter_span(file, scope),
                });
            }
            let nested_owner = function.id.clone();
            analysis.functions.push(function);
            collect_nested_callables_from_binding(
                file,
                module,
                &nested_owner,
                node,
                source,
                analysis,
            );
            return;
        }
    }

    if matches!(node.kind(), "fun_expression" | "function_expression") {
        let current_ordinal = *ordinal;
        *ordinal += 1;
        let parameters = if node.kind() == "fun_expression" {
            direct_named_children(node, "parameter")
        } else {
            Vec::new()
        };
        let parameter_labels = if parameters.is_empty() {
            vec!["_".to_owned()]
        } else {
            parameters
                .iter()
                .map(|parameter| parameter_default_label(*parameter, source))
                .collect()
        };
        let body = node.child_by_field_name("body").unwrap_or(node);
        let expression = node_text(node, source);
        let base = anonymous_callable_base(expression)
            .unwrap_or_else(|| anonymous_callable_identity(expression));
        let id = SymbolId {
            language: LanguageId::new("ocaml"),
            module: module.to_vec(),
            container: Some(owner.to_string()),
            name: format!("{base}#closure{current_ordinal}"),
        };
        analysis.facts.push(LanguageFact {
            subject: id.clone(),
            namespace: LanguageId::new("ocaml"),
            kind: "closure-expression".to_owned(),
            key: base,
            value: normalize_source(node_text(node, source)),
            span: tree_sitter_span(file, node),
        });
        for (index, parameter) in parameters.iter().enumerate() {
            analysis.facts.push(LanguageFact {
                subject: id.clone(),
                namespace: LanguageId::new("ocaml"),
                kind: "parameter".to_owned(),
                key: parameter_labels[index].clone(),
                value: parameter_pattern_and_type(*parameter)
                    .1
                    .map(|node| normalize_source(node_text(node, source)))
                    .unwrap_or_default(),
                span: tree_sitter_span(file, *parameter),
            });
        }
        collect_ocaml_parameter_refinement_facts(
            file,
            &id,
            body,
            source,
            true,
            &mut analysis.facts,
        );
        let mut calls = Vec::new();
        collect_calls(file, body, source, true, &mut calls);
        let lambda = format!("λ#{}", current_ordinal + 1);
        let label = if parameter_labels.is_empty() {
            lambda
        } else {
            format!("{lambda} {}", parameter_labels.join(" "))
        };
        let nested_owner = id.clone();
        analysis.functions.push(FunctionInfo {
            id,
            label: CallLabel::new(label),
            public: false,
            calls,
            span: tree_sitter_span(file, node),
        });

        let mut nested_ordinal = 0usize;
        let mut cursor = body.walk();
        for child in body.named_children(&mut cursor) {
            collect_nested_callables(
                file,
                module,
                &nested_owner,
                child,
                source,
                analysis,
                &mut nested_ordinal,
            );
        }
        return;
    }

    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_nested_callables(file, module, owner, child, source, analysis, ordinal);
    }
}

fn ocaml_local_callable_scope<'tree>(binding: Node<'tree>, source: &str) -> Option<Node<'tree>> {
    let definition = binding
        .parent()
        .filter(|node| node.kind() == "value_definition")?;
    let expression = definition
        .parent()
        .filter(|node| node.kind() == "let_expression")?;
    if normalize_source(node_text(definition, source)).starts_with("let rec ") {
        Some(expression)
    } else {
        expression.child_by_field_name("body")
    }
}

fn collect_nested_callables_from_binding(
    file: &Path,
    module: &[String],
    owner: &SymbolId,
    binding: Node<'_>,
    source: &str,
    analysis: &mut FileAnalysis,
) {
    let Some(mut body) = binding.child_by_field_name("body") else {
        return;
    };
    while body.kind() == "fun_expression" {
        let Some(next) = body.child_by_field_name("body") else {
            return;
        };
        body = next;
    }
    let mut ordinal = 0usize;
    if body.kind() == "function_expression" {
        let mut cursor = body.walk();
        for child in body.named_children(&mut cursor) {
            collect_nested_callables(file, module, owner, child, source, analysis, &mut ordinal);
        }
    } else {
        collect_nested_callables(file, module, owner, body, source, analysis, &mut ordinal);
    }
}

fn anonymous_callable_base(expression: &str) -> Option<String> {
    let expression = normalize_ocaml_callable_argument(expression);
    if !expression.starts_with("fun ") && expression != "fun" && !expression.starts_with("function")
    {
        return None;
    }
    Some(anonymous_callable_identity(expression))
}

fn anonymous_callable_identity(expression: &str) -> String {
    let normalized = expression.split_whitespace().collect::<Vec<_>>().join(" ");
    let mut hasher = Sha256::new();
    hasher.update(normalized.as_bytes());
    let digest = format!("{:x}", hasher.finalize());
    format!("{{lambda:{}}}", &digest[..12])
}

fn local_callable_label(label: &CallLabel, name: &str, ordinal: usize) -> CallLabel {
    let rewrite = |text: &str| {
        let arguments = text
            .find(char::is_whitespace)
            .map_or("", |start| &text[start..]);
        format!("{name}{arguments} [closure#{ordinal}]")
    };
    CallLabel {
        default: rewrite(&label.default),
        typed: label.typed.as_deref().map(rewrite),
    }
}

fn resolve_local_callables(analysis: &mut FileAnalysis) {
    let functions = analysis.functions.clone();
    let symbols = OcamlSymbols::new(&functions);
    let scopes = ocaml_local_callable_scopes(&analysis.facts);
    for function in &mut analysis.functions {
        for call in &mut function.calls {
            if !matches!(call.target, CallTarget::Unresolved) {
                continue;
            }
            if let CallSyntax::Expression(expression) = call.syntax.visible()
                && let Some(candidate) = anonymous_callable_symbol_at(
                    expression,
                    &function.id,
                    &symbols,
                    Some(&call.span),
                )
                && let Some(target) = symbols.get(&candidate)
            {
                let arguments = ocaml_call_arguments(call);
                call.target = CallTarget::Direct(candidate);
                call.label = CallLabel::new(ocaml_candidate_call_label(target, &arguments));
                continue;
            }
            let Some(name) = (match call.syntax.visible() {
                CallSyntax::Path(parts) if parts.len() == 1 => parts.first(),
                CallSyntax::Path(_)
                | CallSyntax::SelfMethod(_)
                | CallSyntax::Method { .. }
                | CallSyntax::Expression(_)
                | CallSyntax::CompilerConfirmed(_) => None,
            }) else {
                continue;
            };
            let candidate =
                local_callable_at(name, &function.id, &symbols, &scopes, Some(&call.span))
                    .and_then(|id| symbols.get(&id));
            let Some(candidate) = candidate else {
                continue;
            };
            call.target = CallTarget::Direct(candidate.id.clone());
            if let Some(ordinal) = candidate
                .id
                .name
                .rsplit_once("#closure")
                .map(|(_, ordinal)| ordinal)
            {
                call.label = call.label.with_suffix(&format!(" [closure#{ordinal}]"));
            }
        }
    }
}

fn local_callable_at(
    name: &str,
    caller: &SymbolId,
    symbols: &OcamlSymbols<'_>,
    scopes: &BTreeMap<SymbolId, SourceSpan>,
    position: Option<&SourceSpan>,
) -> Option<SymbolId> {
    let direct_owner = caller.to_string();
    let sibling_owner = caller.container.as_deref();
    let mut candidates = symbols
        .named(name)
        .filter(|candidate| {
            candidate.id.module == caller.module
                && candidate.id.container.is_some()
                && (candidate.id.container.as_deref() == Some(direct_owner.as_str())
                    || candidate.id.container.as_deref() == sibling_owner
                    || candidate.id == *caller)
                && (candidate.id == *caller
                    || position.is_none_or(|position| {
                        scopes
                            .get(&candidate.id)
                            .is_some_and(|scope| scope.contains(position))
                    }))
        })
        .collect::<Vec<_>>();
    candidates.sort_by_key(|candidate| {
        let scope = scopes.get(&candidate.id).unwrap_or(&candidate.span);
        (
            scope.start_line,
            scope.start_column,
            candidate.span.start_line,
            candidate.span.start_column,
            candidate.id.clone(),
        )
    });
    candidates.last().map(|candidate| candidate.id.clone())
}

fn local_callable_source_name(function: &FunctionInfo) -> &str {
    ocaml_source_name(&function.id.name)
}

fn ocaml_source_name(name: &str) -> &str {
    let name = name.split_once("#ctx[").map_or(name, |(name, _)| name);
    let name = strip_ocaml_numeric_suffix(name, "#closure");
    strip_ocaml_numeric_suffix(name, "#binding")
}

fn strip_ocaml_numeric_suffix<'a>(name: &'a str, marker: &str) -> &'a str {
    name.rsplit_once(marker).map_or(name, |(base, suffix)| {
        if suffix.chars().all(|character| character.is_ascii_digit()) {
            base
        } else {
            name
        }
    })
}

fn redact_anonymous_call_arguments(analysis: &mut FileAnalysis) {
    let labels = analysis
        .functions
        .iter()
        .filter(|function| local_callable_source_name(function).starts_with("{lambda:"))
        .filter_map(|function| {
            let expression = analysis
                .facts
                .iter()
                .find(|fact| fact.subject == function.id && fact.kind == "closure-expression")?;
            let lambda = function.label.default.split_whitespace().next()?.to_owned();
            Some((expression.value.clone(), lambda))
        })
        .collect::<Vec<_>>();
    for function in &mut analysis.functions {
        for call in &mut function.calls {
            for (expression, lambda) in &labels {
                call.label.default = call.label.default.replace(expression, lambda);
                if let Some(typed) = &mut call.label.typed {
                    *typed = typed.replace(expression, lambda);
                }
            }
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct CallableFlow {
    candidates: BTreeSet<SymbolId>,
    unresolved_reasons: BTreeSet<UnresolvedReason>,
}

#[derive(Clone, Debug)]
struct OcamlCallFlow {
    caller: SymbolId,
    target: SymbolId,
    arguments: Vec<String>,
    span: SourceSpan,
}

struct OcamlSymbols<'a> {
    functions: &'a [FunctionInfo],
    by_id: BTreeMap<SymbolId, usize>,
    by_name: BTreeMap<String, Vec<usize>>,
    by_file: BTreeMap<PathBuf, Vec<usize>>,
}

impl<'a> OcamlSymbols<'a> {
    fn new(functions: &'a [FunctionInfo]) -> Self {
        let mut by_id = BTreeMap::new();
        let mut by_name = BTreeMap::<String, Vec<usize>>::new();
        let mut by_file = BTreeMap::<PathBuf, Vec<usize>>::new();
        for (index, function) in functions.iter().enumerate() {
            by_id.insert(function.id.clone(), index);
            by_name
                .entry(local_callable_source_name(function).to_owned())
                .or_default()
                .push(index);
            by_file
                .entry(function.span.file.clone())
                .or_default()
                .push(index);
        }
        let canonical_files = by_file
            .iter()
            .filter_map(|(file, functions)| {
                let canonical = file.canonicalize().ok()?;
                (canonical != *file).then(|| (canonical, functions.clone()))
            })
            .collect::<Vec<_>>();
        for (file, functions) in canonical_files {
            by_file.entry(file).or_default().extend(functions);
        }
        for functions in by_file.values_mut() {
            functions.sort_unstable();
            functions.dedup();
        }
        Self {
            functions,
            by_id,
            by_name,
            by_file,
        }
    }

    fn get(&self, symbol: &SymbolId) -> Option<&'a FunctionInfo> {
        self.by_id
            .get(symbol)
            .and_then(|index| self.functions.get(*index))
    }

    fn named(&self, name: &str) -> impl Iterator<Item = &'a FunctionInfo> + '_ {
        self.by_name
            .get(name)
            .into_iter()
            .flatten()
            .filter_map(|index| self.functions.get(*index))
    }

    fn resolve(
        &self,
        parts: &[String],
        caller: &SymbolId,
        position: Option<&SourceSpan>,
    ) -> Option<SymbolId> {
        let name = parts.last()?;
        let indices = self.by_name.get(name)?;
        let mut candidates = indices
            .iter()
            .filter_map(|index| self.functions.get(*index))
            .filter(|candidate| {
                if parts.len() == 1 {
                    candidate.id.module == caller.module && candidate.id.container.is_none()
                } else {
                    let requested_module = &parts[..parts.len() - 1];
                    candidate.id.container.is_none()
                        && requested_module.len() <= candidate.id.module.len()
                        && candidate.id.module[candidate.id.module.len() - requested_module.len()..]
                            == *requested_module
                }
            })
            .collect::<Vec<_>>();
        if candidates.len() == 1 {
            return Some(candidates[0].id.clone());
        }

        if let Some(position) = position {
            let same_file = self
                .functions_in_file(&position.file)
                .filter(|candidate| candidates.iter().any(|item| item.id == candidate.id))
                .collect::<Vec<_>>();
            if !same_file.is_empty() {
                candidates = same_file;
                let enclosing_binding = self
                    .functions_in_file(&position.file)
                    .filter(|function| {
                        function.id.container.is_none() && function.span.contains(position)
                    })
                    .min_by_key(|function| function.span.extent());
                let visibility_limit = enclosing_binding
                    .map_or((position.start_line, position.start_column), |function| {
                        (function.span.start_line, function.span.start_column)
                    });
                candidates.retain(|candidate| {
                    (candidate.span.start_line, candidate.span.start_column) < visibility_limit
                });
                candidates.sort_by_key(|candidate| {
                    (
                        candidate.span.start_line,
                        candidate.span.start_column,
                        candidate.span.end_line,
                        candidate.span.end_column,
                    )
                });
                if let Some(candidate) = candidates.last() {
                    return Some(candidate.id.clone());
                }
            }
        }

        let mut candidates = candidates
            .into_iter()
            .map(|candidate| candidate.id.clone())
            .collect::<Vec<_>>();
        candidates.sort();
        candidates.dedup();
        (candidates.len() == 1).then(|| candidates.remove(0))
    }

    fn local_target(&self, target: &CallTarget) -> Option<SymbolId> {
        let CallTarget::Direct(target) = target else {
            return None;
        };
        if self.by_id.contains_key(target) {
            return Some(target.clone());
        }
        let target_parts = target.qualified_parts();
        let mut matches = self
            .functions
            .iter()
            .filter(|function| {
                let parts = function.id.qualified_parts();
                target_parts.len() <= parts.len()
                    && parts[parts.len() - target_parts.len()..] == target_parts
            })
            .map(|function| function.id.clone())
            .collect::<Vec<_>>();
        (matches.len() == 1).then(|| matches.remove(0))
    }

    fn functions_in_file(&self, file: &Path) -> impl Iterator<Item = &'a FunctionInfo> + '_ {
        let functions = self.by_file.get(file).or_else(|| {
            file.canonicalize()
                .ok()
                .and_then(|file| self.by_file.get(&file))
        });
        functions
            .into_iter()
            .flatten()
            .filter_map(|index| self.functions.get(*index))
    }
}

struct OcamlFlowIndex<'a> {
    symbols: OcamlSymbols<'a>,
    parameters: &'a BTreeMap<SymbolId, Vec<OcamlParameterBinding>>,
    return_outcomes: &'a BTreeMap<SymbolId, Vec<String>>,
    module_aliases: &'a BTreeMap<Vec<String>, Vec<String>>,
    local_values: &'a BTreeMap<(SymbolId, String), Vec<OcamlLocalValue>>,
    local_callable_scopes: &'a BTreeMap<SymbolId, SourceSpan>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OcamlParameterKind {
    Value,
    Module,
}

#[derive(Clone, Debug)]
struct OcamlParameterBinding {
    name: String,
    argument_index: usize,
    projection: Vec<OcamlProjection>,
    kind: OcamlParameterKind,
    scope: Option<SourceSpan>,
}

#[derive(Clone, Debug)]
enum OcamlProjection {
    Tuple(usize),
    Constructor(String),
    RecordField(String),
}

#[derive(Clone, Debug)]
struct OcamlLocalValue {
    expression: String,
    scope: SourceSpan,
}

fn called_ocaml_parameter_index(
    parts: &[String],
    bindings: &[OcamlParameterBinding],
    position: Option<&SourceSpan>,
) -> Option<usize> {
    bindings.iter().position(|binding| {
        binding
            .scope
            .as_ref()
            .is_none_or(|scope| position.is_some_and(|position| scope.contains(position)))
            && match binding.kind {
                OcamlParameterKind::Value => parts.len() == 1 && parts[0] == binding.name,
                OcamlParameterKind::Module => parts.len() > 1 && parts[0] == binding.name,
            }
    })
}

fn ocaml_local_values(
    facts: &[LanguageFact],
) -> BTreeMap<(SymbolId, String), Vec<OcamlLocalValue>> {
    facts.iter().filter(|fact| fact.kind == "local-value").fold(
        BTreeMap::new(),
        |mut values, fact| {
            values
                .entry((fact.subject.clone(), fact.key.clone()))
                .or_insert_with(Vec::new)
                .push(OcamlLocalValue {
                    expression: fact.value.clone(),
                    scope: fact.span.clone(),
                });
            values
        },
    )
}

fn ocaml_local_callable_scopes(facts: &[LanguageFact]) -> BTreeMap<SymbolId, SourceSpan> {
    facts
        .iter()
        .filter(|fact| fact.kind == "local-callable-scope")
        .map(|fact| (fact.subject.clone(), fact.span.clone()))
        .collect()
}

fn unique_ocaml_local_value<'a>(
    values: &'a BTreeMap<(SymbolId, String), Vec<OcamlLocalValue>>,
    owner: &SymbolId,
    name: &str,
    position: Option<&SourceSpan>,
) -> Option<&'a str> {
    scoped_ocaml_local_value(values, owner, name, position)
        .map(|candidate| candidate.expression.as_str())
}

fn scoped_ocaml_local_value<'a>(
    values: &'a BTreeMap<(SymbolId, String), Vec<OcamlLocalValue>>,
    owner: &SymbolId,
    name: &str,
    position: Option<&SourceSpan>,
) -> Option<&'a OcamlLocalValue> {
    let candidates = values.get(&(owner.clone(), name.to_owned()))?;
    let mut candidates = candidates
        .iter()
        .filter(|candidate| position.is_none_or(|position| candidate.scope.contains(position)))
        .collect::<Vec<_>>();
    candidates.sort_by_key(|candidate| (candidate.scope.start_line, candidate.scope.start_column));
    candidates.last().copied()
}

fn position_before_ocaml_scope(scope: &SourceSpan) -> SourceSpan {
    let mut position = scope.clone();
    if position.start_column > 0 {
        position.start_column -= 1;
        position.end_column = position.start_column;
    } else if position.start_line > 1 {
        position.start_line -= 1;
        position.end_line = position.start_line;
        position.start_column = usize::MAX;
        position.end_column = usize::MAX;
    }
    position.start_byte = position.start_byte.map(|byte| byte.saturating_sub(1));
    position.end_byte = position.start_byte;
    position
}

fn instantiate_ocaml_functors(analysis: &mut FileAnalysis) {
    let base_functions = analysis.functions.clone();
    let base_facts = analysis.facts.clone();
    let functors = base_facts
        .iter()
        .filter(|fact| fact.kind == "functor-parameter")
        .fold(
            BTreeMap::<Vec<String>, Vec<String>>::new(),
            |mut map, fact| {
                let mut module = fact.subject.module.clone();
                module.push(fact.subject.name.clone());
                map.entry(module).or_default().push(fact.value.clone());
                map
            },
        );
    let instances = base_facts
        .iter()
        .filter(|fact| fact.kind == "functor-instance")
        .cloned()
        .collect::<Vec<_>>();

    for instance in instances {
        let mut instance_module = instance.subject.module.clone();
        instance_module.push(instance.subject.name.clone());
        let raw_functor = instance
            .key
            .split('.')
            .map(ToOwned::to_owned)
            .collect::<Vec<_>>();
        let mut relative_functor = instance.subject.module.clone();
        relative_functor.extend(raw_functor.iter().cloned());
        let functor_module = if functors.contains_key(&relative_functor) {
            relative_functor
        } else {
            raw_functor
        };
        let Some(parameters) = functors.get(&functor_module) else {
            continue;
        };
        let arguments = instance
            .value
            .split('\t')
            .filter(|argument| !argument.is_empty())
            .map(|argument| {
                let raw = argument
                    .split('.')
                    .map(ToOwned::to_owned)
                    .collect::<Vec<_>>();
                let mut relative = instance.subject.module.clone();
                relative.extend(raw.iter().cloned());
                if base_functions
                    .iter()
                    .any(|function| function.id.module.starts_with(&relative))
                {
                    relative
                } else {
                    raw
                }
            })
            .collect::<Vec<_>>();
        if parameters.len() != arguments.len() {
            continue;
        }
        let substitutions = parameters
            .iter()
            .cloned()
            .zip(arguments)
            .collect::<Vec<_>>();

        let selected = base_functions
            .iter()
            .filter(|function| function.id.module.starts_with(&functor_module))
            .cloned()
            .collect::<Vec<_>>();
        let ids = selected
            .iter()
            .map(|function| {
                let mut id = function.id.clone();
                let suffix = id.module[functor_module.len()..].to_vec();
                id.module = instance_module.iter().cloned().chain(suffix).collect();
                (function.id.clone(), id)
            })
            .collect::<BTreeMap<_, _>>();
        let containers = ids
            .iter()
            .map(|(old, new)| (old.to_string(), new.to_string()))
            .collect::<BTreeMap<_, _>>();
        let mut clones = Vec::new();
        for mut function in selected {
            let old_id = function.id.clone();
            let Some(new_id) = ids.get(&old_id).cloned() else {
                continue;
            };
            function.id = new_id;
            if let Some(container) = &function.id.container
                && let Some(rewritten) = containers.get(container)
            {
                function.id.container = Some(rewritten.clone());
            }
            function.label.default = replace_ocaml_module_prefix(
                &function.label.default,
                &functor_module,
                &instance_module,
            );
            if let Some(typed) = &mut function.label.typed {
                *typed = replace_ocaml_module_prefix(typed, &functor_module, &instance_module);
            }
            for call in &mut function.calls {
                for (parameter, argument_module) in &substitutions {
                    rewrite_functor_call(call, parameter, argument_module, &containers, &ids);
                }
            }
            clones.push((old_id, function));
        }
        for (old_id, function) in &clones {
            analysis.facts.extend(
                base_facts
                    .iter()
                    .filter(|fact| fact.subject == *old_id)
                    .cloned()
                    .map(|mut fact| {
                        fact.subject = function.id.clone();
                        fact
                    }),
            );
        }
        let new_functions = clones
            .into_iter()
            .map(|(_, function)| function)
            .filter(|function| {
                !analysis
                    .functions
                    .iter()
                    .any(|existing| existing.id == function.id)
            })
            .collect::<Vec<_>>();
        analysis.functions.extend(new_functions);
    }
}

fn rewrite_functor_call(
    call: &mut CallSite,
    parameter: &str,
    argument_module: &[String],
    containers: &BTreeMap<String, String>,
    ids: &BTreeMap<SymbolId, SymbolId>,
) {
    rewrite_functor_syntax(&mut call.syntax, parameter, argument_module);
    let parameter_prefix = format!("{parameter}.");
    let argument_prefix = format!("{}.", argument_module.join("."));
    call.label.default = call
        .label
        .default
        .replacen(&parameter_prefix, &argument_prefix, 1);
    if let Some(typed) = &mut call.label.typed {
        *typed = typed.replacen(&parameter_prefix, &argument_prefix, 1);
    }
    match &mut call.target {
        CallTarget::Direct(target) => {
            if let Some(rewritten) = ids.get(target) {
                *target = rewritten.clone();
            } else if let Some(container) = &target.container
                && let Some(rewritten) = containers.get(container)
            {
                target.container = Some(rewritten.clone());
            }
        }
        CallTarget::Dynamic {
            dispatch,
            candidates,
            ..
        } => {
            if let Some(rewritten) = ids.get(dispatch) {
                *dispatch = rewritten.clone();
            }
            for candidate in candidates {
                if let Some(rewritten) = ids.get(&candidate.target) {
                    candidate.target = rewritten.clone();
                }
            }
        }
        CallTarget::Indirect { .. } | CallTarget::Unresolved => {}
    }
}

fn rewrite_functor_syntax(syntax: &mut CallSyntax, parameter: &str, argument_module: &[String]) {
    match syntax {
        CallSyntax::Path(parts) if parts.first().is_some_and(|part| part == parameter) => {
            let mut rewritten = argument_module.to_vec();
            rewritten.extend_from_slice(&parts[1..]);
            *parts = rewritten;
        }
        CallSyntax::CompilerConfirmed(syntax) => {
            rewrite_functor_syntax(syntax, parameter, argument_module);
        }
        CallSyntax::Path(_)
        | CallSyntax::SelfMethod(_)
        | CallSyntax::Method { .. }
        | CallSyntax::Expression(_) => {}
    }
}

fn replace_ocaml_module_prefix(label: &str, from: &[String], to: &[String]) -> String {
    let from = format!("{}.", from.join("."));
    let to = format!("{}.", to.join("."));
    label.replacen(&from, &to, 1)
}

fn resolve_ocaml_function_values(analysis: &mut FileAnalysis) {
    instantiate_ocaml_functors(analysis);
    let mut functions = analysis.functions.clone();
    let parameters = ocaml_parameters(&functions, &analysis.facts);
    let return_outcomes = ocaml_return_outcomes(&functions, &analysis.facts);
    let module_aliases = ocaml_module_aliases(&functions, &analysis.facts);
    let local_values = ocaml_local_values(&analysis.facts);
    let local_callable_scopes = ocaml_local_callable_scopes(&analysis.facts);

    // Resolve ordinary local/module calls first. Typedtree paths already in
    // `CallTarget::Direct` remain authoritative.
    let symbol_functions = functions.clone();
    let symbols = OcamlSymbols::new(&symbol_functions);
    for function in &mut functions {
        let parameter_names = parameters.get(&function.id).cloned().unwrap_or_default();
        for call in &mut function.calls {
            if let CallSyntax::Path(parts) = call.syntax.visible()
                && (called_ocaml_parameter_index(parts, &parameter_names, Some(&call.span))
                    .is_some()
                    || (parts.len() == 1
                        && unique_ocaml_local_value(
                            &local_values,
                            &function.id,
                            &parts[0],
                            Some(&call.span),
                        )
                        .is_some()))
            {
                // Typedtree resolves first-class module members to their
                // abstract signature path. The concrete module still comes
                // from the caller, so leave this edge for flow specialization.
                call.target = CallTarget::Unresolved;
                continue;
            }
            if let CallTarget::Direct(target) = &call.target {
                let parts = target
                    .qualified_parts()
                    .into_iter()
                    .map(ToOwned::to_owned)
                    .collect::<Vec<_>>();
                if let Some(expanded) = expand_ocaml_module_alias(&parts, &module_aliases)
                    && let Some(resolved) =
                        symbols.resolve(&expanded, &function.id, Some(&call.span))
                {
                    call.target = CallTarget::Direct(resolved);
                    continue;
                }
            }
            if !matches!(call.target, CallTarget::Unresolved) {
                continue;
            }
            let CallSyntax::Path(parts) = call.syntax.visible() else {
                continue;
            };
            let expanded =
                expand_ocaml_module_alias(parts, &module_aliases).unwrap_or_else(|| parts.to_vec());
            if let Some(target) = symbols.resolve(&expanded, &function.id, Some(&call.span)) {
                call.target = CallTarget::Direct(target);
            }
        }
    }

    let mut called_parameters = functions
        .iter()
        .flat_map(|function| {
            let names = parameters.get(&function.id).cloned().unwrap_or_default();
            function.calls.iter().filter_map(move |call| {
                let CallSyntax::Path(parts) = call.syntax.visible() else {
                    return None;
                };
                called_ocaml_parameter_index(parts, &names, Some(&call.span))
                    .map(|index| (function.id.clone(), index))
            })
        })
        .collect::<BTreeSet<_>>();
    let symbols = OcamlSymbols::new(&functions);
    let return_called = ocaml_return_called_functions(&symbols);
    for (function, outcomes) in &return_outcomes {
        if !return_called.contains(function) {
            continue;
        }
        let names = parameters.get(function).cloned().unwrap_or_default();
        for outcome in outcomes {
            if let Some(index) = names.iter().position(|binding| binding.name == *outcome) {
                called_parameters.insert((function.clone(), index));
            }
        }
    }

    let mut call_flows = Vec::new();
    for function in &functions {
        for call in &function.calls {
            let Some(target) = symbols.local_target(&call.target) else {
                continue;
            };
            call_flows.push(OcamlCallFlow {
                caller: function.id.clone(),
                target,
                arguments: ocaml_call_arguments(call),
                span: call.span.clone(),
            });
        }
    }
    loop {
        let previous_len = called_parameters.len();
        for call in &call_flows {
            let caller_parameters = parameters.get(&call.caller).cloned().unwrap_or_default();
            let target_parameters = parameters.get(&call.target).cloned().unwrap_or_default();
            for (target_parameter, binding) in target_parameters.iter().enumerate() {
                if !called_parameters.contains(&(call.target.clone(), target_parameter)) {
                    continue;
                }
                let Some(argument) = call
                    .arguments
                    .get(binding.argument_index)
                    .and_then(|argument| project_ocaml_argument(argument, &binding.projection))
                else {
                    continue;
                };
                let outcomes = ocaml_callable_outcome_names(&argument);
                let module_argument = ocaml_module_package_path(&argument);
                for (caller_parameter, binding) in caller_parameters.iter().enumerate() {
                    let passes_module_parameter = binding.kind == OcamlParameterKind::Module
                        && module_argument
                            .as_ref()
                            .is_some_and(|parts| parts.len() == 1 && parts[0] == binding.name);
                    if outcomes.contains(&binding.name) || passes_module_parameter {
                        called_parameters.insert((call.caller.clone(), caller_parameter));
                    }
                }
            }
        }
        if called_parameters.len() == previous_len {
            break;
        }
    }
    let flow_index = OcamlFlowIndex {
        symbols,
        parameters: &parameters,
        return_outcomes: &return_outcomes,
        module_aliases: &module_aliases,
        local_values: &local_values,
        local_callable_scopes: &local_callable_scopes,
    };
    let (functions, facts) = specialize_ocaml_function_values(
        &functions,
        &analysis.facts,
        &called_parameters,
        &call_flows,
        &flow_index,
    );
    analysis.functions = functions;
    analysis.facts = facts;
}

fn ocaml_module_aliases(
    functions: &[FunctionInfo],
    facts: &[LanguageFact],
) -> BTreeMap<Vec<String>, Vec<String>> {
    facts
        .iter()
        .filter(|fact| fact.kind == "module-alias")
        .map(|fact| {
            let mut alias = fact.subject.module.clone();
            alias.push(fact.subject.name.clone());
            let target = fact
                .value
                .split('.')
                .map(ToOwned::to_owned)
                .collect::<Vec<_>>();
            let mut relative = fact.subject.module.clone();
            relative.extend(target.iter().cloned());
            let target = if functions
                .iter()
                .any(|function| function.id.module.starts_with(&relative))
            {
                relative
            } else {
                target
            };
            (alias, target)
        })
        .collect()
}

fn expand_ocaml_module_alias(
    parts: &[String],
    aliases: &BTreeMap<Vec<String>, Vec<String>>,
) -> Option<Vec<String>> {
    let mut expanded = parts.to_vec();
    let mut changed = false;
    let mut seen = BTreeSet::new();
    while let Some((alias, target)) = aliases
        .iter()
        .filter(|(alias, _)| expanded.starts_with(alias))
        .max_by_key(|(alias, _)| alias.len())
    {
        if !seen.insert(alias.clone()) {
            break;
        }
        let mut next = target.clone();
        next.extend_from_slice(&expanded[alias.len()..]);
        expanded = next;
        changed = true;
    }
    changed.then_some(expanded)
}

fn ocaml_return_called_functions(symbols: &OcamlSymbols<'_>) -> BTreeSet<SymbolId> {
    symbols
        .functions
        .iter()
        .flat_map(|caller| {
            caller.calls.iter().filter_map(|call| {
                let CallSyntax::Expression(expression) = call.syntax.visible() else {
                    return None;
                };
                let parts = ocaml_applied_function_path(expression)?;
                symbols.resolve(&parts, &caller.id, Some(&call.span))
            })
        })
        .collect()
}

fn ocaml_applied_function_path(expression: &str) -> Option<Vec<String>> {
    let tree = parse_ocaml_expression(expression)?;
    if tree.root_node().has_error() {
        return None;
    }
    let mut node = tree.root_node().named_child(0)?;
    while matches!(
        node.kind(),
        "expression_item"
            | "parenthesized_expression"
            | "typed_expression"
            | "coercion_expression"
            | "local_open_expression"
    ) {
        node = node
            .child_by_field_name("body")
            .or_else(|| node.child_by_field_name("expression"))
            .or_else(|| node.named_child(0))?;
    }
    (node.kind() == "application_expression")
        .then(|| node.child_by_field_name("function"))
        .flatten()
        .and_then(|function| ocaml_value_path(function, expression))
}

fn specialize_ocaml_function_values(
    functions: &[FunctionInfo],
    facts: &[LanguageFact],
    called_parameters: &BTreeSet<(SymbolId, usize)>,
    call_flows: &[OcamlCallFlow],
    flow_index: &OcamlFlowIndex<'_>,
) -> (Vec<FunctionInfo>, Vec<LanguageFact>) {
    let parameters = flow_index.parameters;
    let index = functions
        .iter()
        .enumerate()
        .map(|(index, function)| (function.id.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut incoming = vec![0usize; functions.len()];
    for call in call_flows {
        if let Some(target) = index.get(&call.target) {
            incoming[*target] += 1;
        }
        for argument in &call.arguments {
            if let Some(candidate) = argument_callable_symbol(
                argument,
                &call.caller,
                &flow_index.symbols,
                Some(&call.span),
            ) && let Some(target) = index.get(&candidate)
            {
                incoming[*target] += 1;
            }
        }
    }

    let mut pending = VecDeque::<(usize, Vec<CallableFlow>)>::new();
    for (function, incoming) in incoming.iter().enumerate() {
        if *incoming == 0 {
            pending.push_back((
                function,
                root_ocaml_context(&functions[function], parameters, called_parameters),
            ));
        }
    }
    let mut visited = BTreeSet::new();
    let mut covered = BTreeSet::new();
    let mut specialized = Vec::new();
    let mut specialized_facts = Vec::new();

    loop {
        while let Some((raw_index, context)) = pending.pop_front() {
            let raw = &functions[raw_index];
            let id = specialized_ocaml_id(raw, &context, called_parameters);
            // Distinct source bindings can intentionally shadow to the same
            // OCaml path. Even if their display identity currently collapses,
            // each raw node must be consumed or the disconnected-component
            // fallback below will enqueue it forever.
            covered.insert(raw_index);
            if !visited.insert(id.clone()) {
                continue;
            }
            let names = parameters.get(&raw.id).cloned().unwrap_or_default();
            let mut function = raw.clone();
            function.id = id.clone();

            for call in &mut function.calls {
                if let CallSyntax::Expression(expression) = call.syntax.visible()
                    && !matches!(
                        call.target,
                        CallTarget::Direct(_) | CallTarget::Dynamic { .. }
                    )
                {
                    let flow = argument_callable_flow(
                        expression,
                        raw,
                        &context,
                        flow_index,
                        Some(&call.span),
                    );
                    let arguments = ocaml_call_arguments(call);
                    let candidates = flow
                        .candidates
                        .iter()
                        .filter_map(|target| {
                            let target_index = *index.get(target)?;
                            let target_function = &functions[target_index];
                            let target_context = ocaml_call_context(
                                target_function,
                                &arguments,
                                &call.span,
                                raw,
                                &context,
                                flow_index,
                                called_parameters,
                            );
                            let target = specialized_ocaml_id(
                                target_function,
                                &target_context,
                                called_parameters,
                            );
                            pending.push_back((target_index, target_context));
                            Some(DispatchCandidate {
                                target,
                                label: CallLabel::new(ocaml_candidate_call_label(
                                    target_function,
                                    &arguments,
                                )),
                            })
                        })
                        .collect::<Vec<_>>();
                    call.target = CallTarget::dynamic(
                        SymbolId {
                            language: LanguageId::new("ocaml"),
                            module: raw.id.module.clone(),
                            container: Some(raw.id.name.clone()),
                            name: expression.clone(),
                        },
                        candidates,
                        DispatchEvidence::ExactFlow,
                        flow.unresolved_reasons,
                    );
                    continue;
                }

                let CallSyntax::Path(parts) = call.syntax.visible() else {
                    continue;
                };
                let local_expression = (parts.len() == 1)
                    .then(|| {
                        unique_ocaml_local_value(
                            flow_index.local_values,
                            &raw.id,
                            &parts[0],
                            Some(&call.span),
                        )
                    })
                    .flatten();
                let flow_and_binding =
                    local_expression
                        .map(|expression| {
                            (
                                argument_callable_flow(
                                    expression,
                                    raw,
                                    &context,
                                    flow_index,
                                    Some(&call.span),
                                ),
                                None,
                            )
                        })
                        .or_else(|| {
                            let parameter_index =
                                called_ocaml_parameter_index(parts, &names, Some(&call.span))?;
                            let binding = &names[parameter_index];
                            let flow = context.get(parameter_index).cloned().unwrap_or_else(|| {
                                CallableFlow {
                                    candidates: BTreeSet::new(),
                                    unresolved_reasons: [UnresolvedReason::AnalysisLimit]
                                        .into_iter()
                                        .collect(),
                                }
                            });
                            Some((flow, Some(binding)))
                        });
                if let Some((flow, binding)) = flow_and_binding {
                    let arguments = ocaml_call_arguments(call);
                    let candidates = flow
                        .candidates
                        .iter()
                        .filter_map(|target| {
                            let target = match binding.map(|binding| binding.kind) {
                                None | Some(OcamlParameterKind::Value) => target.clone(),
                                Some(OcamlParameterKind::Module) => {
                                    let mut target_parts = ocaml_module_flow_path(target)?.to_vec();
                                    target_parts.extend_from_slice(&parts[1..]);
                                    flow_index.symbols.resolve(
                                        &target_parts,
                                        &raw.id,
                                        Some(&call.span),
                                    )?
                                }
                            };
                            let target_index = *index.get(&target)?;
                            let target_function = &functions[target_index];
                            let target_context = ocaml_call_context(
                                target_function,
                                &arguments,
                                &call.span,
                                raw,
                                &context,
                                flow_index,
                                called_parameters,
                            );
                            let specialized_target = specialized_ocaml_id(
                                target_function,
                                &target_context,
                                called_parameters,
                            );
                            pending.push_back((target_index, target_context));
                            Some(DispatchCandidate {
                                target: specialized_target,
                                label: CallLabel::new(ocaml_candidate_call_label(
                                    target_function,
                                    &arguments,
                                )),
                            })
                        })
                        .collect::<Vec<_>>();
                    call.target = CallTarget::dynamic(
                        SymbolId {
                            language: LanguageId::new("ocaml"),
                            module: raw.id.module.clone(),
                            container: Some(raw.id.name.clone()),
                            name: parts.join("."),
                        },
                        candidates,
                        DispatchEvidence::ExactFlow,
                        flow.unresolved_reasons,
                    );
                    continue;
                }

                let Some(target) = flow_index.symbols.local_target(&call.target) else {
                    continue;
                };
                let Some(target_index) = index.get(&target).copied() else {
                    continue;
                };
                let target_function = &functions[target_index];
                let arguments = ocaml_call_arguments(call);
                let target_context = ocaml_call_context(
                    target_function,
                    &arguments,
                    &call.span,
                    raw,
                    &context,
                    flow_index,
                    called_parameters,
                );
                let target =
                    specialized_ocaml_id(target_function, &target_context, called_parameters);
                pending.push_back((target_index, target_context));
                call.target = CallTarget::Direct(target);
            }

            specialized_facts.extend(
                facts
                    .iter()
                    .filter(|fact| fact.subject == raw.id)
                    .cloned()
                    .map(|mut fact| {
                        fact.subject = id.clone();
                        fact
                    }),
            );
            specialized.push(function);
        }

        let Some(uncovered) = (0..functions.len()).find(|index| !covered.contains(index)) else {
            break;
        };
        pending.push_back((
            uncovered,
            root_ocaml_context(&functions[uncovered], parameters, called_parameters),
        ));
    }
    (specialized, specialized_facts)
}

fn root_ocaml_context(
    function: &FunctionInfo,
    parameters: &BTreeMap<SymbolId, Vec<OcamlParameterBinding>>,
    called_parameters: &BTreeSet<(SymbolId, usize)>,
) -> Vec<CallableFlow> {
    parameters
        .get(&function.id)
        .into_iter()
        .flatten()
        .enumerate()
        .map(|(index, _)| CallableFlow {
            candidates: BTreeSet::new(),
            unresolved_reasons: called_parameters
                .contains(&(function.id.clone(), index))
                .then_some(UnresolvedReason::OpaqueInput)
                .into_iter()
                .collect(),
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn ocaml_call_context(
    target: &FunctionInfo,
    arguments: &[String],
    call_span: &SourceSpan,
    caller: &FunctionInfo,
    caller_context: &[CallableFlow],
    flow_index: &OcamlFlowIndex<'_>,
    called_parameters: &BTreeSet<(SymbolId, usize)>,
) -> Vec<CallableFlow> {
    flow_index
        .parameters
        .get(&target.id)
        .into_iter()
        .flatten()
        .enumerate()
        .map(|(index, binding)| {
            if !called_parameters.contains(&(target.id.clone(), index)) {
                return CallableFlow::default();
            }
            arguments
                .get(binding.argument_index)
                .and_then(|argument| project_ocaml_argument(argument, &binding.projection))
                .map_or_else(
                    || CallableFlow {
                        candidates: BTreeSet::new(),
                        unresolved_reasons: [UnresolvedReason::AnalysisLimit].into_iter().collect(),
                    },
                    |argument| {
                        argument_callable_flow(
                            &argument,
                            caller,
                            caller_context,
                            flow_index,
                            Some(call_span),
                        )
                    },
                )
        })
        .collect()
}

fn specialized_ocaml_id(
    function: &FunctionInfo,
    context: &[CallableFlow],
    called_parameters: &BTreeSet<(SymbolId, usize)>,
) -> SymbolId {
    let bindings = context
        .iter()
        .enumerate()
        .filter(|(index, _)| called_parameters.contains(&(function.id.clone(), *index)))
        .map(|(index, flow)| {
            let mut values = flow
                .candidates
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>();
            for reason in &flow.unresolved_reasons {
                values.push(format!("?{reason}"));
            }
            format!("{index}={}", values.join("|"))
        })
        .collect::<Vec<_>>();
    if bindings.is_empty() {
        return function.id.clone();
    }
    let mut id = function.id.clone();
    id.name = format!("{}#ctx[{}]", id.name, bindings.join(","));
    id
}

fn ocaml_parameters(
    functions: &[FunctionInfo],
    facts: &[LanguageFact],
) -> BTreeMap<SymbolId, Vec<OcamlParameterBinding>> {
    functions
        .iter()
        .map(|function| {
            let mut parameters = Vec::new();
            for (argument_index, fact) in facts
                .iter()
                .filter(|fact| fact.subject == function.id && fact.kind == "parameter")
                .enumerate()
            {
                collect_ocaml_parameter_bindings(
                    &fact.key,
                    argument_index,
                    &mut Vec::new(),
                    &mut parameters,
                );
            }
            for fact in facts
                .iter()
                .filter(|fact| fact.subject == function.id && fact.kind == "parameter-refinement")
            {
                let Some((source, pattern)) = fact.value.split_once('\n') else {
                    continue;
                };
                let Some(base) = parameters
                    .iter()
                    .find(|binding| binding.scope.is_none() && binding.name == source)
                    .cloned()
                else {
                    continue;
                };
                let mut refined = Vec::new();
                let mut projection = base.projection.clone();
                collect_ocaml_parameter_bindings(
                    pattern,
                    base.argument_index,
                    &mut projection,
                    &mut refined,
                );
                for mut binding in refined {
                    if binding.name != fact.key {
                        continue;
                    }
                    binding.scope = Some(fact.span.clone());
                    parameters.push(binding);
                }
            }
            (function.id.clone(), parameters)
        })
        .collect()
}

fn ocaml_return_outcomes(
    functions: &[FunctionInfo],
    facts: &[LanguageFact],
) -> BTreeMap<SymbolId, Vec<String>> {
    functions
        .iter()
        .map(|function| {
            let outcomes = facts
                .iter()
                .filter(|fact| fact.subject == function.id && fact.kind == "callable-return")
                .map(|fact| fact.value.clone())
                .collect();
            (function.id.clone(), outcomes)
        })
        .collect()
}

fn collect_ocaml_parameter_bindings(
    pattern: &str,
    argument_index: usize,
    projection: &mut Vec<OcamlProjection>,
    bindings: &mut Vec<OcamlParameterBinding>,
) {
    let unwrapped = strip_outer_ocaml_parentheses(pattern).trim();
    if let Some(module) = unwrapped.strip_prefix("module ") {
        let name = module.split([' ', ':']).next().unwrap_or(module).trim();
        if !name.is_empty() {
            bindings.push(OcamlParameterBinding {
                name: name.to_owned(),
                argument_index,
                projection: projection.clone(),
                kind: OcamlParameterKind::Module,
                scope: None,
            });
        }
        return;
    }
    let pattern = normalize_ocaml_pattern(pattern);
    let tuple = split_top_level_ocaml(&pattern, ',');
    if tuple.len() > 1 {
        for (index, element) in tuple.into_iter().enumerate() {
            projection.push(OcamlProjection::Tuple(index));
            collect_ocaml_parameter_bindings(element, argument_index, projection, bindings);
            projection.pop();
        }
        return;
    }
    if let Some(fields) = split_ocaml_record_fields(&pattern) {
        for (field, value) in fields {
            projection.push(OcamlProjection::RecordField(field));
            collect_ocaml_parameter_bindings(&value, argument_index, projection, bindings);
            projection.pop();
        }
        return;
    }
    if let Some((constructor, payload)) = split_ocaml_constructor_application(&pattern) {
        projection.push(OcamlProjection::Constructor(constructor.to_owned()));
        collect_ocaml_parameter_bindings(payload, argument_index, projection, bindings);
        projection.pop();
        return;
    }
    if is_value_identifier(&pattern) && pattern != "_" {
        bindings.push(OcamlParameterBinding {
            name: pattern,
            argument_index,
            projection: projection.clone(),
            kind: OcamlParameterKind::Value,
            scope: None,
        });
    }
}

fn normalize_ocaml_pattern(pattern: &str) -> String {
    let mut pattern = pattern.trim();
    if pattern.starts_with(['~', '?']) {
        let stripped = &pattern[1..];
        pattern = stripped.split_once(':').map_or_else(
            || stripped.split('=').next().unwrap_or(stripped),
            |(_, value)| value,
        );
    }
    strip_outer_ocaml_parentheses(pattern).trim().to_owned()
}

fn project_ocaml_argument(argument: &str, projection: &[OcamlProjection]) -> Option<String> {
    let mut value = argument.trim().to_owned();
    if value.starts_with(['~', '?']) {
        let stripped = &value[1..];
        value = stripped
            .split_once(':')
            .map_or(stripped, |(_, value)| value)
            .to_owned();
    }
    for step in projection {
        let current = strip_outer_ocaml_parentheses(&value).trim();
        match step {
            OcamlProjection::Tuple(index) => {
                let elements = split_top_level_ocaml(current, ',');
                value = elements.get(*index)?.trim().to_owned();
            }
            OcamlProjection::Constructor(expected) => {
                let (constructor, payload) = split_ocaml_constructor_application(current)?;
                if constructor != expected {
                    return None;
                }
                value = payload.to_owned();
            }
            OcamlProjection::RecordField(expected) => {
                let fields = split_ocaml_record_fields(current)?;
                value = fields
                    .into_iter()
                    .find(|(field, _)| field == expected)
                    .map(|(_, value)| value)?;
            }
        }
    }
    Some(normalize_source(
        strip_outer_ocaml_parentheses(&value).trim(),
    ))
}

fn split_ocaml_record_fields(value: &str) -> Option<Vec<(String, String)>> {
    let value = strip_outer_ocaml_parentheses(value).trim();
    let inner = value.strip_prefix('{')?.strip_suffix('}')?.trim();
    if inner.is_empty() || split_top_level_ocaml(inner, ';').contains(&"_") {
        return None;
    }
    let mut fields = Vec::new();
    for field in split_top_level_ocaml(inner, ';') {
        let field = field.trim();
        if field.is_empty() {
            continue;
        }
        let assignment = split_top_level_ocaml(field, '=');
        let (path, value) = match assignment.as_slice() {
            [path] => (*path, *path),
            [path, value] => (*path, *value),
            _ => return None,
        };
        let name = path.rsplit('.').next()?.trim();
        if !is_value_identifier(name) {
            return None;
        }
        fields.push((name.to_owned(), normalize_source(value)));
    }
    (!fields.is_empty()).then_some(fields)
}

fn split_ocaml_constructor_application(value: &str) -> Option<(&str, &str)> {
    let value = strip_outer_ocaml_parentheses(value).trim();
    let mut depth = 0usize;
    let mut split = None;
    for (index, character) in value.char_indices() {
        match character {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            character if character.is_whitespace() && depth == 0 => {
                split = Some(index);
                break;
            }
            _ => {}
        }
    }
    let split = split?;
    let constructor = value[..split].trim();
    let payload = value[split..].trim();
    let leaf = constructor.rsplit('.').next().unwrap_or(constructor);
    ((leaf.starts_with('`')
        || leaf
            .chars()
            .next()
            .is_some_and(|character| character.is_ascii_uppercase()))
        && !payload.is_empty())
    .then_some((constructor, payload))
}

fn strip_outer_ocaml_parentheses(mut value: &str) -> &str {
    loop {
        value = value.trim();
        let Some(inner) = value.strip_prefix('(') else {
            return value;
        };
        let mut depth = 1usize;
        let mut in_string = false;
        let mut escaped = false;
        let mut closing = None;
        for (index, character) in inner.char_indices() {
            if in_string {
                if escaped {
                    escaped = false;
                } else if character == '\\' {
                    escaped = true;
                } else if character == '"' {
                    in_string = false;
                }
                continue;
            }
            match character {
                '"' => in_string = true,
                '(' => depth += 1,
                ')' => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        closing = Some(index);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(closing) = closing else {
            return value;
        };
        if closing + ')'.len_utf8() != inner.len() {
            return value;
        }
        value = &inner[..closing];
    }
}

fn split_top_level_ocaml(value: &str, separator: char) -> Vec<&str> {
    let mut result = Vec::new();
    let mut start = 0usize;
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    for (index, character) in value.char_indices() {
        if in_string {
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                in_string = false;
            }
            continue;
        }
        match character {
            '"' => in_string = true,
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            _ if character == separator && depth == 0 => {
                result.push(value[start..index].trim());
                start = index + character.len_utf8();
            }
            _ => {}
        }
    }
    result.push(value[start..].trim());
    result
}

fn argument_callable_flow(
    argument: &str,
    caller: &FunctionInfo,
    caller_context: &[CallableFlow],
    flow_index: &OcamlFlowIndex<'_>,
    position: Option<&SourceSpan>,
) -> CallableFlow {
    if let Some(mut module) = ocaml_module_package_path(argument) {
        if module.len() == 1
            && let Some(index) = flow_index
                .parameters
                .get(&caller.id)
                .and_then(|parameters| {
                    parameters.iter().position(|parameter| {
                        parameter.kind == OcamlParameterKind::Module && parameter.name == module[0]
                    })
                })
        {
            return caller_context
                .get(index)
                .cloned()
                .unwrap_or_else(opaque_callable_flow);
        }
        if let Some(expanded) = expand_ocaml_module_alias(&module, flow_index.module_aliases) {
            module = expanded;
        }
        return CallableFlow {
            candidates: BTreeSet::from([ocaml_module_flow_candidate(module)]),
            unresolved_reasons: BTreeSet::new(),
        };
    }
    let argument = normalize_ocaml_callable_argument(argument);
    if let Some(flow) =
        parse_ocaml_callable_flow(argument, caller, caller_context, flow_index, position)
    {
        return flow;
    }
    if let Some(candidate) =
        argument_callable_symbol(argument, &caller.id, &flow_index.symbols, position)
    {
        return CallableFlow {
            candidates: BTreeSet::from([candidate]),
            unresolved_reasons: BTreeSet::new(),
        };
    }
    CallableFlow {
        candidates: BTreeSet::new(),
        unresolved_reasons: [UnresolvedReason::UnsupportedConstruct]
            .into_iter()
            .collect(),
    }
}

const OCAML_MODULE_FLOW_MARKER: &str = "{module}";

fn ocaml_module_package_path(argument: &str) -> Option<Vec<String>> {
    let argument = strip_outer_ocaml_parentheses(argument).trim();
    let module = argument.strip_prefix("module ")?.trim();
    let module = split_top_level_ocaml(module, ':')
        .into_iter()
        .next()?
        .trim();
    let parts = module
        .split('.')
        .map(str::trim)
        .filter(|part| !part.is_empty() && part.chars().all(is_ocaml_path_character))
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    (!parts.is_empty()).then_some(parts)
}

fn is_ocaml_path_character(character: char) -> bool {
    character == '_' || character == '\'' || character.is_alphanumeric()
}

fn ocaml_module_flow_candidate(module: Vec<String>) -> SymbolId {
    SymbolId {
        language: LanguageId::new("ocaml"),
        module,
        container: None,
        name: OCAML_MODULE_FLOW_MARKER.to_owned(),
    }
}

fn ocaml_module_flow_path(candidate: &SymbolId) -> Option<&[String]> {
    (candidate.language.0 == "ocaml"
        && candidate.container.is_none()
        && candidate.name == OCAML_MODULE_FLOW_MARKER)
        .then_some(candidate.module.as_slice())
}

fn parse_ocaml_callable_flow(
    expression: &str,
    caller: &FunctionInfo,
    caller_context: &[CallableFlow],
    flow_index: &OcamlFlowIndex<'_>,
    position: Option<&SourceSpan>,
) -> Option<CallableFlow> {
    let tree = parse_ocaml_expression(expression)?;
    if tree.root_node().has_error() {
        return None;
    }
    let node = tree.root_node().named_child(0)?;
    ocaml_callable_node_flow(
        node,
        expression,
        caller,
        caller_context,
        flow_index,
        position,
    )
}

fn ocaml_callable_outcome_names(expression: &str) -> BTreeSet<String> {
    let expression = normalize_ocaml_callable_argument(expression);
    let Some(tree) = parse_ocaml_expression(expression) else {
        return BTreeSet::new();
    };
    if tree.root_node().has_error() {
        return BTreeSet::new();
    }
    let Some(node) = tree.root_node().named_child(0) else {
        return BTreeSet::new();
    };
    let mut names = BTreeSet::new();
    collect_ocaml_callable_outcomes(node, expression, &mut names);
    names
}

fn collect_ocaml_callable_outcomes(node: Node<'_>, source: &str, names: &mut BTreeSet<String>) {
    if matches!(
        node.kind(),
        "value_path" | "value_name" | "parenthesized_operator"
    ) {
        names.insert(normalize_source(node_text(node, source)));
        return;
    }
    if matches!(
        node.kind(),
        "expression_item"
            | "parenthesized_expression"
            | "typed_expression"
            | "coercion_expression"
            | "let_expression"
            | "local_open_expression"
    ) {
        if let Some(expression) = node
            .child_by_field_name("body")
            .or_else(|| node.child_by_field_name("expression"))
            .or_else(|| node.named_child(0))
        {
            collect_ocaml_callable_outcomes(expression, source, names);
        }
        return;
    }
    if node.kind() == "sequence_expression" {
        let mut cursor = node.walk();
        if let Some(last) = node.named_children(&mut cursor).last() {
            collect_ocaml_callable_outcomes(last, source, names);
        }
        return;
    }
    if node.kind() == "if_expression" {
        let mut cursor = node.walk();
        for clause in node
            .named_children(&mut cursor)
            .filter(|child| matches!(child.kind(), "then_clause" | "else_clause"))
        {
            if let Some(expression) = clause.child_by_field_name("expression") {
                collect_ocaml_callable_outcomes(expression, source, names);
            }
        }
        return;
    }
    if matches!(node.kind(), "match_expression" | "function_expression") {
        let mut cursor = node.walk();
        for case in node
            .named_children(&mut cursor)
            .filter(|child| child.kind() == "match_case")
        {
            if let Some(body) = case.child_by_field_name("body") {
                collect_ocaml_callable_outcomes(body, source, names);
            }
        }
    }
}

fn ocaml_callable_node_flow(
    node: Node<'_>,
    source: &str,
    caller: &FunctionInfo,
    caller_context: &[CallableFlow],
    flow_index: &OcamlFlowIndex<'_>,
    position: Option<&SourceSpan>,
) -> Option<CallableFlow> {
    if matches!(node.kind(), "fun_expression" | "function_expression") {
        let target = anonymous_callable_symbol_at(
            node_text(node, source),
            &caller.id,
            &flow_index.symbols,
            position,
        )?;
        return Some(CallableFlow {
            candidates: BTreeSet::from([target]),
            unresolved_reasons: BTreeSet::new(),
        });
    }
    if node.kind() == "application_expression" {
        let function = node.child_by_field_name("function")?;
        let parts = ocaml_value_path(function, source)?;
        let arguments = ocaml_application_arguments(node, function, source);
        let Some(target) = flow_index.symbols.resolve(&parts, &caller.id, position) else {
            let projection = match parts.as_slice() {
                [name] if name == "fst" => Some(0),
                [name] if name == "snd" => Some(1),
                _ => None,
            }?;
            let argument = arguments.first()?;
            return projected_ocaml_callable_flow(
                argument,
                &[OcamlProjection::Tuple(projection)],
                caller,
                caller_context,
                flow_index,
                position,
                0,
            );
        };
        let target_function = flow_index.symbols.get(&target)?;
        let target_context = flow_index
            .parameters
            .get(&target)
            .into_iter()
            .flatten()
            .map(|binding| {
                arguments
                    .get(binding.argument_index)
                    .and_then(|argument| project_ocaml_argument(argument, &binding.projection))
                    .map_or_else(opaque_callable_flow, |argument| {
                        argument_callable_flow(
                            &argument,
                            caller,
                            caller_context,
                            flow_index,
                            position,
                        )
                    })
            })
            .collect::<Vec<_>>();
        let outcomes = flow_index.return_outcomes.get(&target)?;
        let mut flow = CallableFlow::default();
        for outcome in outcomes {
            merge_callable_flow(
                &mut flow,
                argument_callable_flow(
                    outcome,
                    target_function,
                    &target_context,
                    flow_index,
                    position,
                ),
            );
        }
        return (!outcomes.is_empty()).then_some(flow);
    }
    if node.kind() == "field_get_expression" {
        let record = node.child_by_field_name("record")?;
        let field = node.child_by_field_name("field")?;
        return ocaml_record_field_flow(
            node_text(record, source),
            node_text(field, source),
            caller,
            caller_context,
            flow_index,
            position,
            0,
        );
    }
    if matches!(
        node.kind(),
        "value_path" | "value_name" | "parenthesized_operator"
    ) {
        return ocaml_callable_atom_flow(
            node_text(node, source),
            caller,
            caller_context,
            flow_index,
            position,
        );
    }
    if matches!(
        node.kind(),
        "expression_item"
            | "parenthesized_expression"
            | "typed_expression"
            | "coercion_expression"
            | "let_expression"
            | "local_open_expression"
    ) {
        let expression = node
            .child_by_field_name("body")
            .or_else(|| node.child_by_field_name("expression"))
            .or_else(|| node.named_child(0))?;
        return ocaml_callable_node_flow(
            expression,
            source,
            caller,
            caller_context,
            flow_index,
            position,
        );
    }
    if node.kind() == "sequence_expression" {
        let mut cursor = node.walk();
        let last = node.named_children(&mut cursor).last()?;
        return ocaml_callable_node_flow(
            last,
            source,
            caller,
            caller_context,
            flow_index,
            position,
        );
    }
    if node.kind() == "if_expression" {
        let mut flow = CallableFlow::default();
        let mut branches = 0usize;
        let mut cursor = node.walk();
        for clause in node
            .named_children(&mut cursor)
            .filter(|child| matches!(child.kind(), "then_clause" | "else_clause"))
        {
            let Some(expression) = clause.child_by_field_name("expression") else {
                flow.unresolved_reasons
                    .insert(UnresolvedReason::UnsupportedConstruct);
                continue;
            };
            branches += 1;
            merge_callable_flow(
                &mut flow,
                ocaml_callable_node_flow(
                    expression,
                    source,
                    caller,
                    caller_context,
                    flow_index,
                    position,
                )
                .unwrap_or_else(opaque_callable_flow),
            );
        }
        if branches < 2 {
            flow.unresolved_reasons
                .insert(UnresolvedReason::OpaqueInput);
        }
        return Some(flow);
    }
    if matches!(node.kind(), "match_expression" | "function_expression") {
        let mut flow = CallableFlow::default();
        let mut branches = 0usize;
        let mut cursor = node.walk();
        for case in node
            .named_children(&mut cursor)
            .filter(|child| child.kind() == "match_case")
        {
            let Some(body) = case.child_by_field_name("body") else {
                flow.unresolved_reasons
                    .insert(UnresolvedReason::UnsupportedConstruct);
                continue;
            };
            branches += 1;
            merge_callable_flow(
                &mut flow,
                ocaml_callable_node_flow(
                    body,
                    source,
                    caller,
                    caller_context,
                    flow_index,
                    position,
                )
                .unwrap_or_else(opaque_callable_flow),
            );
        }
        return (branches > 0).then_some(flow);
    }
    None
}

#[allow(clippy::too_many_arguments)]
fn projected_ocaml_callable_flow(
    expression: &str,
    projection: &[OcamlProjection],
    caller: &FunctionInfo,
    caller_context: &[CallableFlow],
    flow_index: &OcamlFlowIndex<'_>,
    position: Option<&SourceSpan>,
    depth: usize,
) -> Option<CallableFlow> {
    if depth >= 64 {
        return Some(CallableFlow {
            candidates: BTreeSet::new(),
            unresolved_reasons: [UnresolvedReason::AnalysisLimit].into_iter().collect(),
        });
    }

    let expression = normalize_ocaml_callable_argument(expression);
    if is_value_identifier(expression)
        && let Some(local) =
            scoped_ocaml_local_value(flow_index.local_values, &caller.id, expression, position)
    {
        let definition_position = position_before_ocaml_scope(&local.scope);
        return projected_ocaml_callable_flow(
            &local.expression,
            projection,
            caller,
            caller_context,
            flow_index,
            Some(&definition_position),
            depth + 1,
        );
    }

    let projected = project_ocaml_argument(expression, projection)?;
    Some(argument_callable_flow(
        &projected,
        caller,
        caller_context,
        flow_index,
        position,
    ))
}

fn ocaml_callable_atom_flow(
    argument: &str,
    caller: &FunctionInfo,
    caller_context: &[CallableFlow],
    flow_index: &OcamlFlowIndex<'_>,
    position: Option<&SourceSpan>,
) -> Option<CallableFlow> {
    let argument = normalize_ocaml_callable_argument(argument);
    if let Some(local) =
        scoped_ocaml_local_value(flow_index.local_values, &caller.id, argument, position)
    {
        let definition_position = position_before_ocaml_scope(&local.scope);
        return Some(
            parse_ocaml_callable_flow(
                &local.expression,
                caller,
                caller_context,
                flow_index,
                Some(&definition_position),
            )
            .unwrap_or_else(opaque_callable_flow),
        );
    }
    if let Some(flow) = flow_index
        .parameters
        .get(&caller.id)
        .and_then(|parameters| {
            parameters.iter().position(|parameter| {
                parameter.kind == OcamlParameterKind::Value
                    && parameter.name == argument
                    && parameter.scope.as_ref().is_none_or(|scope| {
                        position.is_some_and(|position| scope.contains(position))
                    })
            })
        })
        .map(|index| {
            caller_context
                .get(index)
                .cloned()
                .unwrap_or_else(opaque_callable_flow)
        })
    {
        return Some(flow);
    }
    if let Some(target) = local_callable_at(
        argument,
        &caller.id,
        &flow_index.symbols,
        flow_index.local_callable_scopes,
        position,
    ) {
        return Some(CallableFlow {
            candidates: BTreeSet::from([target]),
            unresolved_reasons: BTreeSet::new(),
        });
    }
    argument_callable_symbol(argument, &caller.id, &flow_index.symbols, position).map(|target| {
        CallableFlow {
            candidates: BTreeSet::from([target]),
            unresolved_reasons: BTreeSet::new(),
        }
    })
}

#[allow(clippy::too_many_arguments)]
fn ocaml_record_field_flow(
    record_expression: &str,
    requested_field: &str,
    caller: &FunctionInfo,
    caller_context: &[CallableFlow],
    flow_index: &OcamlFlowIndex<'_>,
    position: Option<&SourceSpan>,
    depth: usize,
) -> Option<CallableFlow> {
    if depth >= 64 {
        return Some(CallableFlow {
            candidates: BTreeSet::new(),
            unresolved_reasons: [UnresolvedReason::AnalysisLimit].into_iter().collect(),
        });
    }

    let record_expression = strip_outer_ocaml_parentheses(record_expression).trim();
    if is_value_identifier(record_expression)
        && let Some(local) = scoped_ocaml_local_value(
            flow_index.local_values,
            &caller.id,
            record_expression,
            position,
        )
    {
        let definition_position = position_before_ocaml_scope(&local.scope);
        return ocaml_record_field_flow(
            &local.expression,
            requested_field,
            caller,
            caller_context,
            flow_index,
            Some(&definition_position),
            depth + 1,
        );
    }

    let tree = parse_ocaml_expression(record_expression)?;
    if tree.root_node().has_error() {
        return None;
    }
    let mut record = tree.root_node().named_child(0)?;
    while matches!(
        record.kind(),
        "expression_item" | "parenthesized_expression"
    ) {
        record = record
            .child_by_field_name("expression")
            .or_else(|| record.named_child(0))?;
    }
    if record.kind() != "record_expression" {
        return None;
    }

    let requested_field = normalize_source(requested_field);
    let requested_field = requested_field
        .rsplit('.')
        .next()
        .unwrap_or(&requested_field);
    let mut cursor = record.walk();
    for field in record
        .named_children(&mut cursor)
        .filter(|child| child.kind() == "field_expression")
    {
        let Some(path) = field
            .named_children(&mut field.walk())
            .find(|child| child.kind() == "field_path")
        else {
            continue;
        };
        let field_name = normalize_source(node_text(path, record_expression));
        if field_name.rsplit('.').next() != Some(requested_field) {
            continue;
        }
        if let Some(body) = field.child_by_field_name("body") {
            return ocaml_callable_node_flow(
                body,
                record_expression,
                caller,
                caller_context,
                flow_index,
                position,
            );
        }
        return ocaml_callable_atom_flow(&field_name, caller, caller_context, flow_index, position);
    }

    let base = record.child_by_field_name("record")?;
    ocaml_record_field_flow(
        node_text(base, record_expression),
        requested_field,
        caller,
        caller_context,
        flow_index,
        position,
        depth + 1,
    )
}

fn ocaml_application_arguments(
    application: Node<'_>,
    function: Node<'_>,
    source: &str,
) -> Vec<String> {
    let application = normalize_source(node_text(application, source));
    let function = normalize_source(node_text(function, source));
    application
        .strip_prefix(&function)
        .map(str::trim)
        .map(split_ocaml_arguments)
        .unwrap_or_default()
}

fn opaque_callable_flow() -> CallableFlow {
    CallableFlow {
        candidates: BTreeSet::new(),
        unresolved_reasons: [UnresolvedReason::OpaqueInput].into_iter().collect(),
    }
}

fn merge_callable_flow(destination: &mut CallableFlow, source: CallableFlow) {
    destination.candidates.extend(source.candidates);
    destination
        .unresolved_reasons
        .extend(source.unresolved_reasons);
}

fn argument_callable_symbol(
    argument: &str,
    caller: &SymbolId,
    symbols: &OcamlSymbols<'_>,
    position: Option<&SourceSpan>,
) -> Option<SymbolId> {
    let argument = normalize_ocaml_callable_argument(argument);
    if let Some(candidate) = anonymous_callable_symbol(argument, caller, symbols) {
        return Some(candidate);
    }
    if let Some(candidate) =
        displayed_anonymous_callable_symbol(argument, caller, symbols.functions)
    {
        return Some(candidate);
    }
    let parts = argument
        .split('.')
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    symbols.resolve(&parts, caller, position)
}

fn displayed_anonymous_callable_symbol(
    expression: &str,
    caller: &SymbolId,
    functions: &[FunctionInfo],
) -> Option<SymbolId> {
    let lambda = normalize_ocaml_callable_argument(expression);
    if !lambda.starts_with('λ') {
        return None;
    }
    let direct_owner = caller.to_string();
    let sibling_owner = caller.container.as_deref();
    let mut candidates = functions
        .iter()
        .filter(|candidate| {
            local_callable_source_name(candidate).starts_with("{lambda:")
                && candidate.label.default.split_whitespace().next() == Some(lambda)
                && (candidate.id.container.as_deref() == Some(direct_owner.as_str())
                    || candidate.id.container.as_deref() == sibling_owner)
        })
        .map(|candidate| candidate.id.clone())
        .collect::<Vec<_>>();
    candidates.sort();
    candidates.dedup();
    (candidates.len() == 1).then(|| candidates.remove(0))
}

fn anonymous_callable_symbol(
    expression: &str,
    caller: &SymbolId,
    symbols: &OcamlSymbols<'_>,
) -> Option<SymbolId> {
    anonymous_callable_symbol_at(expression, caller, symbols, None)
}

fn anonymous_callable_symbol_at(
    expression: &str,
    caller: &SymbolId,
    symbols: &OcamlSymbols<'_>,
    position: Option<&SourceSpan>,
) -> Option<SymbolId> {
    let base = anonymous_callable_base(expression)?;
    let direct_owner = caller.to_string();
    let sibling_owner = caller.container.as_deref();
    let mut candidates = symbols
        .named(&base)
        .filter(|candidate| {
            candidate.id.container.as_deref() == Some(direct_owner.as_str())
                || candidate.id.container.as_deref() == sibling_owner
        })
        .map(|candidate| candidate.id.clone())
        .collect::<Vec<_>>();
    if let Some(position) = position {
        let positioned = candidates
            .iter()
            .filter(|candidate| {
                symbols
                    .get(candidate)
                    .is_some_and(|function| position.contains(&function.span))
            })
            .cloned()
            .collect::<Vec<_>>();
        if !positioned.is_empty() {
            candidates = positioned;
        }
    }
    candidates.sort();
    candidates.dedup();
    (candidates.len() == 1).then(|| candidates.remove(0))
}

fn normalize_ocaml_callable_argument(argument: &str) -> &str {
    let argument = argument.trim();
    let argument = argument
        .strip_prefix(['~', '?'])
        .map_or(argument, |argument| {
            argument
                .split_once(':')
                .map_or(argument, |(_, value)| value)
        });
    strip_outer_ocaml_parentheses(argument).trim()
}

fn ocaml_call_arguments(call: &CallSite) -> Vec<String> {
    let callee = match call.syntax.visible() {
        CallSyntax::Path(parts) => parts.join("."),
        CallSyntax::SelfMethod(method) => method.clone(),
        CallSyntax::Method { receiver, method } => format!("{receiver}#{method}"),
        CallSyntax::Expression(expression) => expression.clone(),
        CallSyntax::CompilerConfirmed(syntax) => syntax.key_fragment(),
    };
    let remainder = call
        .label
        .default
        .strip_prefix(&callee)
        .unwrap_or(&call.label.default)
        .trim();
    split_ocaml_arguments(remainder)
}

fn split_ocaml_arguments(arguments: &str) -> Vec<String> {
    let mut result = Vec::new();
    let mut start = None;
    let mut delimiters = Vec::new();
    let mut in_string = false;
    let mut escaped = false;
    for (index, character) in arguments.char_indices() {
        if in_string {
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                in_string = false;
            }
            continue;
        }
        match character {
            '"' => {
                in_string = true;
                start.get_or_insert(index);
            }
            '(' | '[' | '{' => {
                delimiters.push(character);
                start.get_or_insert(index);
            }
            ')' | ']' | '}' => {
                delimiters.pop();
            }
            character if character.is_whitespace() && delimiters.is_empty() => {
                if let Some(argument_start) = start.take() {
                    result.push(arguments[argument_start..index].to_owned());
                }
            }
            _ => {
                start.get_or_insert(index);
            }
        }
    }
    if let Some(argument_start) = start {
        result.push(arguments[argument_start..].to_owned());
    }
    result
}

fn ocaml_candidate_call_label(function: &FunctionInfo, arguments: &[String]) -> String {
    let mut name = local_callable_source_name(function).to_owned();
    let anonymous = name.starts_with("{lambda:");
    if anonymous {
        name = function
            .label
            .default
            .split_whitespace()
            .next()
            .unwrap_or("λ")
            .to_owned();
    }
    if function.id.container.is_none() && !function.id.module.is_empty() {
        name = function
            .id
            .module
            .iter()
            .chain(std::iter::once(&name))
            .cloned()
            .collect::<Vec<_>>()
            .join(".");
    }
    let mut label = if arguments.is_empty() {
        name
    } else {
        format!("{name} {}", arguments.join(" "))
    };
    if !anonymous
        && let Some(ordinal) = function
            .id
            .name
            .rsplit_once("#closure")
            .map(|(_, ordinal)| ordinal)
    {
        label.push_str(&format!(" [closure#{ordinal}]"));
    }
    label
}

fn function_from_binding(
    file: &Path,
    module: &[String],
    binding: Node<'_>,
    source: &str,
    analysis: &mut FileAnalysis,
) -> Option<FunctionInfo> {
    let pattern = binding.child_by_field_name("pattern")?;
    if !matches!(pattern.kind(), "value_name" | "value_pattern") {
        return None;
    }
    let name = node_text(pattern, source).trim();
    if !is_value_identifier(name) {
        return None;
    }

    let binding_body = binding.child_by_field_name("body")?;
    let mut parameters = direct_named_children(binding, "parameter");
    let mut body = binding_body;
    let mut function_expression = false;
    while body.kind() == "fun_expression" {
        function_expression = true;
        parameters.extend(direct_named_children(body, "parameter"));
        body = body.child_by_field_name("body").unwrap_or(body);
    }
    if body.kind() == "function_expression" {
        function_expression = true;
        parameters.push(body);
    }
    if parameters.is_empty() && !function_expression {
        return None;
    }

    let id = SymbolId {
        language: LanguageId::new("ocaml"),
        module: module.to_vec(),
        container: None,
        name: name.to_owned(),
    };
    let parameter_labels = parameters
        .iter()
        .map(|parameter| {
            if parameter.kind() == "function_expression" {
                "_".to_owned()
            } else {
                parameter_default_label(*parameter, source)
            }
        })
        .collect::<Vec<_>>();
    let default_label = ocaml_declaration_label(&id, &parameter_labels);
    let typed_label = typed_declaration_label(&id, &parameters, source);

    for (index, parameter) in parameters.iter().enumerate() {
        if parameter.kind() == "function_expression" {
            continue;
        }
        let key = parameter_labels[index].clone();
        let value = parameter_pattern_and_type(*parameter)
            .1
            .map(|node| normalize_source(node_text(node, source)))
            .unwrap_or_default();
        analysis.facts.push(LanguageFact {
            subject: id.clone(),
            namespace: LanguageId::new("ocaml"),
            kind: "parameter".to_owned(),
            key,
            value,
            span: tree_sitter_span(file, *parameter),
        });
    }

    let mut return_outcomes = BTreeSet::new();
    collect_ocaml_callable_outcomes(body, source, &mut return_outcomes);
    for (index, outcome) in return_outcomes.into_iter().enumerate() {
        analysis.facts.push(LanguageFact {
            subject: id.clone(),
            namespace: LanguageId::new("ocaml"),
            kind: "callable-return".to_owned(),
            key: index.to_string(),
            value: outcome,
            span: tree_sitter_span(file, body),
        });
    }

    collect_ocaml_local_value_facts(file, &id, body, source, true, &mut analysis.facts);
    collect_ocaml_parameter_refinement_facts(file, &id, body, source, true, &mut analysis.facts);

    let mut calls = Vec::new();
    collect_calls(file, body, source, true, &mut calls);

    Some(FunctionInfo {
        id,
        label: match typed_label {
            Some(typed) => CallLabel::with_types(default_label, typed),
            None => CallLabel::new(default_label),
        },
        // Without an .mli index, structure bindings are conservatively treated
        // as exported entry candidates. Explicit --entry remains exact.
        public: true,
        calls,
        span: tree_sitter_span(file, binding),
    })
}

fn collect_ocaml_local_value_facts(
    file: &Path,
    owner: &SymbolId,
    node: Node<'_>,
    source: &str,
    is_root: bool,
    facts: &mut Vec<LanguageFact>,
) {
    if !is_root && matches!(node.kind(), "fun_expression" | "function_expression") {
        return;
    }
    if node.kind() == "let_expression" {
        let bindings = direct_named_children(node, "value_definition")
            .into_iter()
            .flat_map(|definition| direct_named_children(definition, "let_binding"));
        for binding in bindings {
            let Some(body) = binding.child_by_field_name("body") else {
                continue;
            };
            let is_callable_binding = !direct_named_children(binding, "parameter").is_empty()
                || matches!(body.kind(), "fun_expression" | "function_expression");
            if is_callable_binding {
                continue;
            }
            if let Some(pattern) = binding.child_by_field_name("pattern") {
                let mut bindings = Vec::new();
                collect_ocaml_parameter_bindings(
                    node_text(pattern, source),
                    0,
                    &mut Vec::new(),
                    &mut bindings,
                );
                for local in bindings
                    .into_iter()
                    .filter(|binding| binding.kind == OcamlParameterKind::Value)
                {
                    let Some(value) =
                        project_ocaml_argument(node_text(body, source), &local.projection)
                    else {
                        continue;
                    };
                    facts.push(LanguageFact {
                        subject: owner.clone(),
                        namespace: LanguageId::new("ocaml"),
                        kind: "local-value".to_owned(),
                        key: local.name,
                        value,
                        span: tree_sitter_span(
                            file,
                            node.child_by_field_name("body").unwrap_or(node),
                        ),
                    });
                }
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_ocaml_local_value_facts(file, owner, child, source, false, facts);
    }
}

fn collect_ocaml_parameter_refinement_facts(
    file: &Path,
    owner: &SymbolId,
    node: Node<'_>,
    source: &str,
    is_root: bool,
    facts: &mut Vec<LanguageFact>,
) {
    if !is_root && matches!(node.kind(), "fun_expression" | "function_expression") {
        return;
    }
    if node.kind() == "let_binding" && !direct_named_children(node, "parameter").is_empty() {
        return;
    }

    if node.kind() == "match_expression"
        && let Some(scrutinee) = node.child_by_field_name("expression")
    {
        let scrutinee = normalize_source(node_text(scrutinee, source));
        if is_value_identifier(&scrutinee) {
            for case in direct_named_children(node, "match_case") {
                let (Some(pattern), Some(body)) = (
                    case.child_by_field_name("pattern"),
                    case.child_by_field_name("body"),
                ) else {
                    continue;
                };
                push_ocaml_parameter_refinements(
                    file,
                    owner,
                    &scrutinee,
                    node_text(pattern, source),
                    body,
                    facts,
                );
            }
        }
    }

    if node.kind() == "let_expression"
        && let Some(scope) = node.child_by_field_name("body")
    {
        for binding in direct_named_children(node, "value_definition")
            .into_iter()
            .flat_map(|definition| direct_named_children(definition, "let_binding"))
        {
            let (Some(pattern), Some(value)) = (
                binding.child_by_field_name("pattern"),
                binding.child_by_field_name("body"),
            ) else {
                continue;
            };
            let value = normalize_source(node_text(value, source));
            if is_value_identifier(&value) {
                push_ocaml_parameter_refinements(
                    file,
                    owner,
                    &value,
                    node_text(pattern, source),
                    scope,
                    facts,
                );
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_ocaml_parameter_refinement_facts(file, owner, child, source, false, facts);
    }
}

fn push_ocaml_parameter_refinements(
    file: &Path,
    owner: &SymbolId,
    source_name: &str,
    pattern: &str,
    scope: Node<'_>,
    facts: &mut Vec<LanguageFact>,
) {
    let mut bindings = Vec::new();
    collect_ocaml_parameter_bindings(pattern, 0, &mut Vec::new(), &mut bindings);
    for binding in bindings {
        if binding.kind != OcamlParameterKind::Value {
            continue;
        }
        facts.push(LanguageFact {
            subject: owner.clone(),
            namespace: LanguageId::new("ocaml"),
            kind: "parameter-refinement".to_owned(),
            key: binding.name,
            value: format!("{source_name}\n{}", normalize_source(pattern)),
            span: tree_sitter_span(file, scope),
        });
    }
}

fn collect_calls(
    file: &Path,
    node: Node<'_>,
    source: &str,
    is_callable_body: bool,
    calls: &mut Vec<CallSite>,
) {
    if node.kind() == "application_expression" {
        // Evaluate a callable expression and its arguments before recording
        // the enclosing application. This preserves source execution order
        // for `(make_callback x) y` and mirrors the compiler event order.
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            collect_calls(file, child, source, false, calls);
        }
        if let Some(function) = node.child_by_field_name("function") {
            if matches!(
                function.kind(),
                "constructor_path" | "constructor_name" | "tag"
            ) {
                return;
            }
            if let Some(parts) = ocaml_value_path(function, source) {
                if ocaml_path_is_constructor(&parts) {
                    return;
                }
                let label = ocaml_path_call_label(node, function, &parts, source);
                let syntax = CallSyntax::Path(parts);
                let span = tree_sitter_span(file, node);
                calls.push(CallSite {
                    id: CallSiteId::source(&syntax, &span),
                    syntax,
                    target: CallTarget::Unresolved,
                    label: CallLabel::new(label),
                    span,
                });
            } else if function.kind() == "method_invocation" {
                let syntax = CallSyntax::Path(vec![normalize_source(node_text(function, source))]);
                let span = tree_sitter_span(file, node);
                calls.push(CallSite {
                    id: CallSiteId::source(&syntax, &span),
                    syntax,
                    target: CallTarget::Dynamic {
                        dispatch: SymbolId {
                            language: LanguageId::new("ocaml"),
                            module: Vec::new(),
                            container: None,
                            name: format!(
                                "object-method@{}:{}",
                                node.start_position().row + 1,
                                node.start_position().column
                            ),
                        },
                        candidates: Vec::new(),
                        resolution: DispatchResolution::Unresolved,
                        evidence: DispatchEvidence::ExactFlow,
                        unresolved_reasons: [UnresolvedReason::OpaqueInput].into_iter().collect(),
                    },
                    label: CallLabel::new(normalize_source(node_text(node, source))),
                    span,
                });
            } else {
                let syntax = CallSyntax::Expression(normalize_source(node_text(function, source)));
                let span = tree_sitter_span(file, node);
                calls.push(CallSite {
                    id: CallSiteId::source(&syntax, &span),
                    syntax,
                    target: CallTarget::Unresolved,
                    label: CallLabel::new(normalize_source(node_text(node, source))),
                    span,
                });
            }
        }
        return;
    } else if !is_callable_body && matches!(node.kind(), "fun_expression" | "function_expression") {
        // A nested closure owns its calls. It will receive its own callable ID
        // when local callable extraction is added.
        return;
    } else if node.kind() == "let_binding" && !direct_named_children(node, "parameter").is_empty() {
        // Likewise, do not attribute a local function's body to its enclosing
        // function.
        return;
    }

    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_calls(file, child, source, false, calls);
    }
}

fn ocaml_path_is_constructor(parts: &[String]) -> bool {
    parts.last().is_some_and(|name| {
        name.starts_with('`')
            || name
                .chars()
                .next()
                .is_some_and(|character| character.is_ascii_uppercase())
    })
}

fn ocaml_path_call_label(
    application: Node<'_>,
    function: Node<'_>,
    parts: &[String],
    source: &str,
) -> String {
    let application = normalize_source(node_text(application, source));
    let function = normalize_source(node_text(function, source));
    let qualified = parts.join(".");
    application
        .strip_prefix(&function)
        .map_or(application.clone(), |arguments| {
            format!("{qualified}{arguments}")
        })
}

fn ocaml_value_path(function: Node<'_>, source: &str) -> Option<Vec<String>> {
    if !matches!(
        function.kind(),
        "value_path" | "value_name" | "parenthesized_operator"
    ) {
        return None;
    }
    let raw = normalize_source(node_text(function, source));
    let mut parts = raw
        .split('.')
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    let mut opened = Vec::new();
    let mut ancestor = function.parent();
    while let Some(node) = ancestor {
        if node.kind() == "local_open_expression"
            && let Some(module_path) = direct_named_child(node, "module_path")
        {
            let mut prefix = normalize_source(node_text(module_path, source))
                .split('.')
                .map(str::trim)
                .filter(|part| !part.is_empty())
                .map(ToOwned::to_owned)
                .collect::<Vec<_>>();
            prefix.append(&mut opened);
            opened = prefix;
        }
        ancestor = node.parent();
    }
    opened.append(&mut parts);
    let parts = opened;
    (!parts.is_empty()).then_some(parts)
}

fn direct_named_child<'tree>(node: Node<'tree>, kind: &str) -> Option<Node<'tree>> {
    let mut cursor = node.walk();
    node.named_children(&mut cursor)
        .find(|child| child.kind() == kind)
}

fn direct_named_children<'tree>(node: Node<'tree>, kind: &str) -> Vec<Node<'tree>> {
    let mut cursor = node.walk();
    node.named_children(&mut cursor)
        .filter(|child| child.kind() == kind)
        .collect()
}

fn node_text<'a>(node: Node<'_>, source: &'a str) -> &'a str {
    node.utf8_text(source.as_bytes())
        .expect("tree-sitter nodes always point into the parsed UTF-8 source")
}

fn ocaml_declaration_label(id: &SymbolId, parameters: &[String]) -> String {
    let name = id
        .module
        .iter()
        .chain(std::iter::once(&id.name))
        .cloned()
        .collect::<Vec<_>>()
        .join(".");
    if parameters.is_empty() {
        name
    } else {
        format!("{name} {}", parameters.join(" "))
    }
}

fn typed_declaration_label(id: &SymbolId, parameters: &[Node<'_>], source: &str) -> Option<String> {
    let mut found_type = false;
    let labels = parameters
        .iter()
        .map(|parameter| {
            if parameter.kind() == "function_expression" {
                return "_".to_owned();
            }
            let (label, typed) = parameter_typed_label(*parameter, source);
            found_type |= typed;
            label
        })
        .collect::<Vec<_>>();
    found_type.then(|| ocaml_declaration_label(id, &labels))
}

fn parameter_default_label(parameter: Node<'_>, source: &str) -> String {
    let (pattern_node, ty) = parameter_pattern_and_type(parameter);
    if ty.is_none() {
        return normalize_source(node_text(parameter, source));
    }

    let pattern = pattern_node
        .map(|pattern| normalize_source(node_text(pattern, source)))
        .unwrap_or_else(|| "_".to_owned());
    let Some(label) = direct_named_child(parameter, "label_name") else {
        return pattern;
    };
    let marker = node_text(parameter, source)
        .trim_start()
        .chars()
        .next()
        .filter(|marker| matches!(marker, '~' | '?'))
        .unwrap_or('~');
    let label = normalize_source(node_text(label, source));
    if pattern == label {
        format!("{marker}{label}")
    } else {
        format!("{marker}{label}:{pattern}")
    }
}

fn parameter_typed_label(parameter: Node<'_>, source: &str) -> (String, bool) {
    let (pattern_node, ty) = parameter_pattern_and_type(parameter);
    let Some(ty) = ty else {
        return (parameter_default_label(parameter, source), false);
    };
    let pattern = pattern_node
        .map(|pattern| normalize_source(node_text(pattern, source)))
        .unwrap_or_else(|| "_".to_owned());
    let annotated = format!("({pattern} : {})", normalize_source(node_text(ty, source)));
    let Some(label) = direct_named_child(parameter, "label_name") else {
        return (annotated, true);
    };
    let marker = node_text(parameter, source)
        .trim_start()
        .chars()
        .next()
        .filter(|marker| matches!(marker, '~' | '?'))
        .unwrap_or('~');
    (
        format!(
            "{marker}{}:{annotated}",
            normalize_source(node_text(label, source))
        ),
        true,
    )
}

fn parameter_pattern_and_type<'tree>(
    parameter: Node<'tree>,
) -> (Option<Node<'tree>>, Option<Node<'tree>>) {
    let pattern = parameter.child_by_field_name("pattern");
    match pattern {
        Some(pattern) if pattern.kind() == "typed_pattern" => (
            pattern.child_by_field_name("pattern"),
            pattern.child_by_field_name("type"),
        ),
        pattern => (pattern, parameter.child_by_field_name("type")),
    }
}

fn is_value_identifier(value: &str) -> bool {
    let mut chars = value.chars();
    chars
        .next()
        .is_some_and(|first| first == '_' || first.is_ascii_lowercase())
        && chars.all(|character| {
            character == '_' || character == '\'' || character.is_ascii_alphanumeric()
        })
}

fn tree_sitter_span(file: &Path, node: Node<'_>) -> SourceSpan {
    SourceSpan {
        file: file.to_path_buf(),
        start_line: node.start_position().row + 1,
        start_column: node.start_position().column,
        start_byte: Some(node.start_byte()),
        end_line: node.end_position().row + 1,
        end_column: node.end_position().column,
        end_byte: Some(node.end_byte()),
    }
}

fn normalize_source(source: &str) -> String {
    let mut output = String::with_capacity(source.len());
    let mut in_string = false;
    let mut escaped = false;
    let mut pending_space = false;

    for character in source.chars() {
        if in_string {
            output.push(character);
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                in_string = false;
            }
            continue;
        }

        if character == '"' {
            if pending_space && !output.is_empty() {
                output.push(' ');
            }
            pending_space = false;
            in_string = true;
            output.push(character);
        } else if character.is_whitespace() {
            pending_space = true;
        } else {
            if pending_space && !output.is_empty() {
                output.push(' ');
            }
            pending_space = false;
            output.push(character);
        }
    }
    output.trim().to_owned()
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;

    #[test]
    fn extracts_module_functions_and_native_call_labels() {
        let source = include_str!("../../examples/ocaml/after.ml");
        let analysis = OcamlFrontend
            .analyze_file(
                &FileContext {
                    path: Path::new("after.ml"),
                    module: &[],
                },
                source,
            )
            .unwrap();

        let save = analysis
            .functions
            .iter()
            .find(|function| function.id.module == ["Postgres"] && function.id.name == "save")
            .unwrap();
        assert_eq!(save.label.default, "Postgres.save order");
        assert_eq!(
            save.calls
                .iter()
                .map(|call| call.label.default.as_str())
                .collect::<Vec<_>>(),
            ["Sql.begin_tx order", "Sql.insert order", "Sql.commit order"]
        );
    }

    #[test]
    fn keeps_labeled_optional_and_unit_application_syntax() {
        let source = r#"
            let run order =
              charge ~currency:"KRW" order 100;
              find ?limit:None ~tenant:"acme" order;
              commit ()
        "#;
        let analysis = OcamlFrontend
            .analyze_file(
                &FileContext {
                    path: Path::new("calls.ml"),
                    module: &[],
                },
                source,
            )
            .unwrap();
        let calls = &analysis.functions[0].calls;
        assert_eq!(calls[0].label.default, "charge ~currency:\"KRW\" order 100");
        assert_eq!(
            calls[1].label.default,
            "find ?limit:None ~tenant:\"acme\" order"
        );
        assert_eq!(calls[2].label.default, "commit ()");
    }

    #[test]
    fn separates_ocaml_parameter_types_from_the_default_label() {
        let source = "let run (order : Order.t) = validate order";
        let analysis = OcamlFrontend
            .analyze_file(
                &FileContext {
                    path: Path::new("typed.ml"),
                    module: &[],
                },
                source,
            )
            .unwrap();
        let label = &analysis.functions[0].label;
        assert_eq!(label.default, "run order");
        assert_eq!(label.typed.as_deref(), Some("run (order : Order.t)"));
    }

    #[test]
    fn source_project_resolves_calls_across_ocaml_modules() {
        let sequence = OCAML_TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir().join(format!(
            "diffkit-ocaml-source-project-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("a.ml"), "let entry value = B.save value\n").unwrap();
        fs::write(directory.join("b.ml"), "let save value = value\n").unwrap();

        let analysis = analyze_source_project(&directory).unwrap();
        let entry = analysis
            .functions
            .iter()
            .find(|function| function.id.module == ["A"] && function.id.name == "entry")
            .unwrap();
        assert!(matches!(
            &entry.calls[0].target,
            CallTarget::Direct(target) if target.module == ["B"] && target.name == "save"
        ));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn maps_dune_build_locations_back_to_source_files() {
        let sequence = OCAML_TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir().join(format!(
            "diffkit-ocaml-dune-path-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir_all(directory.join("src")).unwrap();
        fs::write(directory.join("src/service.ml"), "let run () = ()\n").unwrap();
        let mapped = dune_source_path(&directory, &directory.join("_build/default/src/service.ml"));
        assert_eq!(mapped, Some(directory.join("src/service.ml")));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn compiler_libs_adapter_compiles_when_ocaml_is_installed() {
        if Command::new("ocamlc").arg("-version").output().is_err() {
            return;
        }
        let extractor = OcamlExtractor::compile().unwrap();
        assert!(extractor.executable().is_file());
    }

    #[test]
    fn splits_curried_inferred_types_without_splitting_nested_arrows() {
        assert_eq!(
            split_ocaml_function_type("('a -> 'b) -> label:int -> 'a -> 'b"),
            ["('a -> 'b)", "label:int", "'a", "'b"]
        );
    }

    #[test]
    fn typedtree_identifiers_do_not_turn_callable_parameters_into_static_functions() {
        let source = "let apply callback value = callback value";
        let path = Path::new("callback.ml");
        let mut analysis =
            analyze_ocaml_syntax(&FileContext { path, module: &[] }, source).unwrap();
        let span = analysis.functions[0].calls[0].span.clone();
        apply_typed_events(
            &mut analysis,
            &[TypedCallEvent {
                target: Some("callback".to_owned()),
                signature: Some("'a -> 'b".to_owned()),
                span,
            }],
        );

        assert!(matches!(
            analysis.functions[0].calls[0].target,
            CallTarget::Unresolved
        ));
    }

    #[test]
    fn one_typedtree_event_cannot_be_reused_by_two_source_calls() {
        let source = "let run value = outer (inner value)";
        let path = Path::new("nested.ml");
        let mut analysis =
            analyze_ocaml_syntax(&FileContext { path, module: &[] }, source).unwrap();
        let span = analysis.functions[0]
            .calls
            .iter()
            .find(|call| call.label.default == "inner value")
            .unwrap()
            .span
            .clone();
        apply_typed_events(
            &mut analysis,
            &[TypedCallEvent {
                target: Some("Inner.target".to_owned()),
                signature: None,
                span,
            }],
        );

        assert_eq!(
            analysis.functions[0]
                .calls
                .iter()
                .filter(|call| matches!(call.target, CallTarget::Direct(_)))
                .count(),
            1
        );
    }

    #[test]
    fn extracts_functions_declared_inside_a_functor_body() {
        let source = r#"
            module Make (Store : sig val save : int -> unit end) = struct
              let run value = Store.save value
            end
        "#;
        let analysis = OcamlFrontend
            .analyze_file(
                &FileContext {
                    path: Path::new("functor.ml"),
                    module: &[],
                },
                source,
            )
            .unwrap();
        assert!(
            analysis
                .functions
                .iter()
                .any(|function| { function.id.module == ["Make"] && function.id.name == "run" })
        );
    }
}
