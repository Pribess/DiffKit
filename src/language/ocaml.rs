use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use tree_sitter::{Node, Parser};

use super::{FileContext, FrontendResult, LanguageFrontend};
use crate::model::{
    CallLabel, CallSite, CallSyntax, CallTarget, DispatchCandidate, DispatchResolution,
    FileAnalysis, FunctionInfo, LanguageFact, LanguageId, SourceSpan, SymbolId,
};

static OCAML_TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);
const OCAML_EXTRACTOR_SOURCE: &str = include_str!("../../support/ocaml/extract.ml");

/// OCaml's source-label stage. Dune projects overlay compiler-libs Typedtree
/// paths in `analyze_semantic_project`; standalone source sets retain
/// conservative module/local resolution and the same graph contract.
#[derive(Default)]
pub struct OcamlFrontend;

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
    let mut cmt_files = Vec::new();
    collect_files_with_extension(&root.join("_build"), "cmt", &mut cmt_files)?;
    cmt_files.sort();
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

    let mut source_files = Vec::new();
    collect_ocaml_sources(&root, &mut source_files)?;
    source_files.sort();
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
        analysis.functions.append(&mut file_analysis.functions);
        analysis.facts.append(&mut file_analysis.facts);
    }
    resolve_ocaml_function_values(&mut analysis);
    Ok(analysis)
}

/// Analyze an OCaml source set without a Dune project. This is used for
/// standalone source trees; Dune projects use `analyze_semantic_project`.
pub fn analyze_source_project(root: &Path) -> FrontendResult<FileAnalysis> {
    let root = root.canonicalize()?;
    let mut files = Vec::new();
    collect_ocaml_sources(&root, &mut files)?;
    files.sort();
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
        analysis.functions.append(&mut file_analysis.functions);
        analysis.facts.append(&mut file_analysis.facts);
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
    span: SourceSpan,
}

impl LanguageFrontend for OcamlFrontend {
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
        resolve_ocaml_function_values(&mut analysis);
        Ok(analysis)
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
    resolve_local_callables(&mut analysis);
    Ok(analysis)
}

fn collect_files_with_extension(
    directory: &Path,
    extension: &str,
    files: &mut Vec<PathBuf>,
) -> std::io::Result<()> {
    if !directory.is_dir() {
        return Ok(());
    }
    let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(std::fs::DirEntry::path);
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            collect_files_with_extension(&path, extension, files)?;
        } else if file_type.is_file()
            && path.extension().and_then(|value| value.to_str()) == Some(extension)
        {
            files.push(path);
        }
    }
    Ok(())
}

fn collect_ocaml_sources(directory: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(std::fs::DirEntry::path);
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            if !matches!(
                path.file_name().and_then(|name| name.to_str()),
                Some("_build" | ".git" | "target" | "node_modules")
            ) {
                collect_ocaml_sources(&path, files)?;
            }
        } else if file_type.is_file()
            && matches!(
                path.extension().and_then(|value| value.to_str()),
                Some("ml" | "mli")
            )
        {
            files.push(path);
        }
    }
    Ok(())
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
            if fields.len() != 7 {
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
    for function in &mut analysis.functions {
        for call in &mut function.calls {
            if matches!(
                &call.target,
                CallTarget::Direct(target) if target.container.is_some()
            ) {
                continue;
            }
            if matches!(call.target, CallTarget::Dynamic { .. }) {
                continue;
            }
            let Some(event) = events
                .iter()
                .filter(|event| {
                    ocaml_source_files_match(&event.span.file, &call.span.file)
                        && ocaml_spans_overlap(&event.span, &call.span)
                })
                .min_by_key(|event| ocaml_span_distance(&event.span, &call.span))
            else {
                continue;
            };
            call.target = match &event.target {
                Some(target) => CallTarget::Direct(ocaml_path_symbol(target)),
                None => CallTarget::Dynamic {
                    dispatch: SymbolId {
                        language: LanguageId::new("ocaml"),
                        module: function.id.module.clone(),
                        container: Some(function.id.name.clone()),
                        name: format!(
                            "indirect@{}:{}",
                            call.span.start_line, call.span.start_column
                        ),
                    },
                    candidates: Vec::new(),
                    resolution: DispatchResolution::Unresolved,
                },
            };
        }
    }
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
    left == right
        || left
            .canonicalize()
            .ok()
            .zip(right.canonicalize().ok())
            .is_some_and(|(left, right)| left == right)
}

fn ocaml_spans_overlap(left: &SourceSpan, right: &SourceSpan) -> bool {
    (left.start_line, left.start_column) <= (right.end_line, right.end_column)
        && (right.start_line, right.start_column) <= (left.end_line, left.end_column)
}

fn ocaml_span_distance(left: &SourceSpan, right: &SourceSpan) -> usize {
    left.start_line.abs_diff(right.start_line) * 10_000
        + left.start_column.abs_diff(right.start_column)
        + left.end_line.abs_diff(right.end_line) * 10_000
        + left.end_column.abs_diff(right.end_column)
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
        if body.kind() != "structure" {
            continue;
        }

        let mut nested_module = module.to_vec();
        nested_module.push(node_text(name_node, source).to_owned());
        analyze_structure(file, &nested_module, body, source, analysis);
    }
}

fn analyze_value_definition(
    file: &Path,
    module: &[String],
    definition: Node<'_>,
    source: &str,
    analysis: &mut FileAnalysis,
) {
    let mut cursor = definition.walk();
    for binding in definition
        .named_children(&mut cursor)
        .filter(|child| child.kind() == "let_binding")
    {
        if let Some(function) = function_from_binding(file, module, binding, source, analysis) {
            let owner = function.id.clone();
            analysis.functions.push(function);
            if let Some(body) = binding.child_by_field_name("body") {
                let mut ordinal = 0usize;
                collect_nested_callables(
                    file,
                    module,
                    &owner,
                    body,
                    source,
                    analysis,
                    &mut ordinal,
                );
            }
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
            let nested_owner = function.id.clone();
            analysis.functions.push(function);
            if let Some(body) = node.child_by_field_name("body") {
                let mut nested_ordinal = 0usize;
                collect_nested_callables(
                    file,
                    module,
                    &nested_owner,
                    body,
                    source,
                    analysis,
                    &mut nested_ordinal,
                );
            }
            return;
        }
    }

    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_nested_callables(file, module, owner, child, source, analysis, ordinal);
    }
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
    for function in &mut analysis.functions {
        for call in &mut function.calls {
            if !matches!(call.target, CallTarget::Unresolved) {
                continue;
            }
            let Some(name) = (match &call.syntax {
                CallSyntax::Path(parts) if parts.len() == 1 => parts.first(),
                CallSyntax::Path(_) | CallSyntax::SelfMethod(_) | CallSyntax::Method { .. } => None,
            }) else {
                continue;
            };
            let direct_owner = function.id.to_string();
            let sibling_owner = function.id.container.as_deref();
            let mut candidates = functions
                .iter()
                .filter(|candidate| {
                    candidate.id.module == function.id.module
                        && candidate.id.container.is_some()
                        && local_callable_source_name(candidate) == name
                        && (candidate.id.container.as_deref() == Some(direct_owner.as_str())
                            || candidate.id.container.as_deref() == sibling_owner
                            || candidate.id == function.id)
                })
                .collect::<Vec<_>>();
            candidates.sort_by_key(|candidate| {
                (
                    candidate.span.start_line,
                    candidate.span.start_column,
                    candidate.id.clone(),
                )
            });
            let candidate = candidates.into_iter().rev().find(|candidate| {
                (candidate.span.start_line, candidate.span.start_column)
                    <= (call.span.start_line, call.span.start_column)
            });
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

fn local_callable_source_name(function: &FunctionInfo) -> &str {
    function
        .id
        .name
        .rsplit_once("#closure")
        .map_or(function.id.name.as_str(), |(name, _)| name)
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct CallableFlow {
    candidates: BTreeSet<SymbolId>,
    opaque: bool,
}

#[derive(Clone, Debug)]
struct OcamlCallFlow {
    caller: SymbolId,
    target: SymbolId,
    arguments: Vec<String>,
}

fn resolve_ocaml_function_values(analysis: &mut FileAnalysis) {
    let mut functions = analysis.functions.clone();
    let parameters = ocaml_parameters(&functions, &analysis.facts);

    // Resolve ordinary local/module calls first. Typedtree paths already in
    // `CallTarget::Direct` remain authoritative.
    let symbol_index = functions.clone();
    for function in &mut functions {
        let parameter_names = parameters.get(&function.id).cloned().unwrap_or_default();
        for call in &mut function.calls {
            if !matches!(call.target, CallTarget::Unresolved) {
                continue;
            }
            let CallSyntax::Path(parts) = &call.syntax else {
                continue;
            };
            if parts.len() == 1 && parameter_names.contains(&parts[0]) {
                continue;
            }
            if let Some(target) = resolve_ocaml_symbol(parts, &function.id, &symbol_index) {
                call.target = CallTarget::Direct(target);
            }
        }
    }

    let mut called_parameters = functions
        .iter()
        .flat_map(|function| {
            let names = parameters.get(&function.id).cloned().unwrap_or_default();
            function.calls.iter().filter_map(move |call| {
                let CallSyntax::Path(parts) = &call.syntax else {
                    return None;
                };
                (parts.len() == 1)
                    .then(|| names.iter().position(|name| name == &parts[0]))
                    .flatten()
                    .map(|index| (function.id.clone(), index))
            })
        })
        .collect::<BTreeSet<_>>();

    let function_index = functions.clone();
    let mut call_flows = Vec::new();
    for function in &functions {
        for call in &function.calls {
            let Some(target) = local_target(&call.target, &function_index) else {
                continue;
            };
            call_flows.push(OcamlCallFlow {
                caller: function.id.clone(),
                target,
                arguments: ocaml_call_arguments(call),
            });
        }
    }
    loop {
        let previous_len = called_parameters.len();
        for call in &call_flows {
            let caller_parameters = parameters.get(&call.caller).cloned().unwrap_or_default();
            for (target_parameter, argument) in call.arguments.iter().enumerate() {
                if !called_parameters.contains(&(call.target.clone(), target_parameter)) {
                    continue;
                }
                let outcomes = ocaml_callable_outcome_names(argument);
                for (caller_parameter, name) in caller_parameters.iter().enumerate() {
                    if outcomes.contains(name) {
                        called_parameters.insert((call.caller.clone(), caller_parameter));
                    }
                }
            }
        }
        if called_parameters.len() == previous_len {
            break;
        }
    }
    let (functions, facts) = specialize_ocaml_function_values(
        &functions,
        &analysis.facts,
        &parameters,
        &called_parameters,
        &call_flows,
    );
    analysis.functions = functions;
    analysis.facts = facts;
}

fn specialize_ocaml_function_values(
    functions: &[FunctionInfo],
    facts: &[LanguageFact],
    parameters: &BTreeMap<SymbolId, Vec<String>>,
    called_parameters: &BTreeSet<(SymbolId, usize)>,
    call_flows: &[OcamlCallFlow],
) -> (Vec<FunctionInfo>, Vec<LanguageFact>) {
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
            if let Some(candidate) = argument_callable_symbol(argument, &call.caller, functions)
                && let Some(target) = index.get(&candidate)
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
            if !visited.insert(id.clone()) {
                continue;
            }
            covered.insert(raw_index);
            let names = parameters.get(&raw.id).cloned().unwrap_or_default();
            let mut function = raw.clone();
            function.id = id.clone();

            for call in &mut function.calls {
                let CallSyntax::Path(parts) = &call.syntax else {
                    continue;
                };
                let parameter_index = (parts.len() == 1)
                    .then(|| names.iter().position(|name| name == &parts[0]))
                    .flatten();
                if let Some(parameter_index) = parameter_index {
                    let flow =
                        context
                            .get(parameter_index)
                            .cloned()
                            .unwrap_or_else(|| CallableFlow {
                                candidates: BTreeSet::new(),
                                opaque: true,
                            });
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
                                raw,
                                &context,
                                functions,
                                parameters,
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
                    let resolution = match (candidates.is_empty(), flow.opaque) {
                        (true, _) => DispatchResolution::Unresolved,
                        (false, true) => DispatchResolution::Partial,
                        (false, false) => DispatchResolution::Complete,
                    };
                    call.target = CallTarget::Dynamic {
                        dispatch: SymbolId {
                            language: LanguageId::new("ocaml"),
                            module: raw.id.module.clone(),
                            container: Some(raw.id.name.clone()),
                            name: parts[0].clone(),
                        },
                        candidates,
                        resolution,
                    };
                    continue;
                }

                let Some(target) = local_target(&call.target, functions) else {
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
                    raw,
                    &context,
                    functions,
                    parameters,
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
    parameters: &BTreeMap<SymbolId, Vec<String>>,
    called_parameters: &BTreeSet<(SymbolId, usize)>,
) -> Vec<CallableFlow> {
    parameters
        .get(&function.id)
        .into_iter()
        .flatten()
        .enumerate()
        .map(|(index, _)| CallableFlow {
            candidates: BTreeSet::new(),
            opaque: called_parameters.contains(&(function.id.clone(), index)),
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn ocaml_call_context(
    target: &FunctionInfo,
    arguments: &[String],
    caller: &FunctionInfo,
    caller_context: &[CallableFlow],
    functions: &[FunctionInfo],
    parameters: &BTreeMap<SymbolId, Vec<String>>,
    called_parameters: &BTreeSet<(SymbolId, usize)>,
) -> Vec<CallableFlow> {
    parameters
        .get(&target.id)
        .into_iter()
        .flatten()
        .enumerate()
        .map(|(index, _)| {
            if !called_parameters.contains(&(target.id.clone(), index)) {
                return CallableFlow::default();
            }
            arguments.get(index).map_or_else(
                || CallableFlow {
                    candidates: BTreeSet::new(),
                    opaque: true,
                },
                |argument| {
                    argument_callable_flow(argument, caller, caller_context, functions, parameters)
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
            if flow.opaque {
                values.push("?".to_owned());
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
) -> BTreeMap<SymbolId, Vec<String>> {
    functions
        .iter()
        .map(|function| {
            let parameters = facts
                .iter()
                .filter(|fact| fact.subject == function.id && fact.kind == "parameter")
                .map(|fact| normalize_ocaml_parameter_name(&fact.key))
                .collect::<Vec<_>>();
            (function.id.clone(), parameters)
        })
        .collect()
}

fn normalize_ocaml_parameter_name(parameter: &str) -> String {
    parameter
        .trim_start_matches(['~', '?'])
        .split([':', '='])
        .next()
        .unwrap_or(parameter)
        .trim_matches(['(', ')', ' '])
        .to_owned()
}

fn resolve_ocaml_symbol(
    parts: &[String],
    caller: &SymbolId,
    functions: &[FunctionInfo],
) -> Option<SymbolId> {
    let name = parts.last()?;
    let mut candidates = functions
        .iter()
        .filter(|candidate| {
            local_callable_source_name(candidate) == name
                && if parts.len() == 1 {
                    candidate.id.module == caller.module && candidate.id.container.is_none()
                } else {
                    let requested_module = &parts[..parts.len() - 1];
                    requested_module.len() <= candidate.id.module.len()
                        && candidate.id.module[candidate.id.module.len() - requested_module.len()..]
                            == *requested_module
                }
        })
        .map(|candidate| candidate.id.clone())
        .collect::<Vec<_>>();
    if candidates.is_empty() && parts.len() == 1 {
        candidates.extend(
            functions
                .iter()
                .filter(|candidate| local_callable_source_name(candidate) == name)
                .map(|candidate| candidate.id.clone()),
        );
    }
    candidates.sort();
    candidates.dedup();
    (candidates.len() == 1).then(|| candidates.remove(0))
}

fn local_target(target: &CallTarget, functions: &[FunctionInfo]) -> Option<SymbolId> {
    let CallTarget::Direct(target) = target else {
        return None;
    };
    if functions.iter().any(|function| function.id == *target) {
        return Some(target.clone());
    }
    let target_parts = target.qualified_parts();
    let mut matches = functions
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

fn argument_callable_flow(
    argument: &str,
    caller: &FunctionInfo,
    caller_context: &[CallableFlow],
    functions: &[FunctionInfo],
    parameters: &BTreeMap<SymbolId, Vec<String>>,
) -> CallableFlow {
    let argument = normalize_ocaml_callable_argument(argument);
    parse_ocaml_callable_flow(argument, caller, caller_context, functions, parameters)
        .unwrap_or_else(|| CallableFlow {
            candidates: BTreeSet::new(),
            opaque: true,
        })
}

fn parse_ocaml_callable_flow(
    expression: &str,
    caller: &FunctionInfo,
    caller_context: &[CallableFlow],
    functions: &[FunctionInfo],
    parameters: &BTreeMap<SymbolId, Vec<String>>,
) -> Option<CallableFlow> {
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_ocaml::LANGUAGE_OCAML.into())
        .ok()?;
    let tree = parser.parse(expression, None)?;
    if tree.root_node().has_error() {
        return None;
    }
    let node = tree.root_node().named_child(0)?;
    ocaml_callable_node_flow(
        node,
        expression,
        caller,
        caller_context,
        functions,
        parameters,
    )
}

fn ocaml_callable_outcome_names(expression: &str) -> BTreeSet<String> {
    let expression = normalize_ocaml_callable_argument(expression);
    let mut parser = Parser::new();
    if parser
        .set_language(&tree_sitter_ocaml::LANGUAGE_OCAML.into())
        .is_err()
    {
        return BTreeSet::new();
    }
    let Some(tree) = parser.parse(expression, None) else {
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
    functions: &[FunctionInfo],
    parameters: &BTreeMap<SymbolId, Vec<String>>,
) -> Option<CallableFlow> {
    if matches!(
        node.kind(),
        "value_path" | "value_name" | "parenthesized_operator"
    ) {
        return ocaml_callable_atom_flow(
            node_text(node, source),
            caller,
            caller_context,
            functions,
            parameters,
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
            functions,
            parameters,
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
            functions,
            parameters,
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
                flow.opaque = true;
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
                    functions,
                    parameters,
                )
                .unwrap_or_else(opaque_callable_flow),
            );
        }
        flow.opaque |= branches < 2;
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
                flow.opaque = true;
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
                    functions,
                    parameters,
                )
                .unwrap_or_else(opaque_callable_flow),
            );
        }
        return (branches > 0).then_some(flow);
    }
    None
}

fn ocaml_callable_atom_flow(
    argument: &str,
    caller: &FunctionInfo,
    caller_context: &[CallableFlow],
    functions: &[FunctionInfo],
    parameters: &BTreeMap<SymbolId, Vec<String>>,
) -> Option<CallableFlow> {
    let argument = normalize_ocaml_callable_argument(argument);
    if let Some(target) = argument_callable_symbol(argument, &caller.id, functions) {
        return Some(CallableFlow {
            candidates: BTreeSet::from([target]),
            opaque: false,
        });
    }
    parameters
        .get(&caller.id)
        .and_then(|parameters| {
            parameters
                .iter()
                .position(|parameter| parameter == argument)
        })
        .map(|index| {
            caller_context
                .get(index)
                .cloned()
                .unwrap_or_else(opaque_callable_flow)
        })
}

fn opaque_callable_flow() -> CallableFlow {
    CallableFlow {
        candidates: BTreeSet::new(),
        opaque: true,
    }
}

fn merge_callable_flow(destination: &mut CallableFlow, source: CallableFlow) {
    destination.candidates.extend(source.candidates);
    destination.opaque |= source.opaque;
}

fn argument_callable_symbol(
    argument: &str,
    caller: &SymbolId,
    functions: &[FunctionInfo],
) -> Option<SymbolId> {
    let argument = normalize_ocaml_callable_argument(argument);
    let parts = argument
        .split('.')
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    resolve_ocaml_symbol(&parts, caller, functions)
}

fn normalize_ocaml_callable_argument(argument: &str) -> &str {
    argument
        .trim_start_matches(['~', '?'])
        .split_once(':')
        .map_or(argument, |(_, value)| value)
        .trim_matches(['(', ')', ' '])
}

fn ocaml_call_arguments(call: &CallSite) -> Vec<String> {
    let callee = match &call.syntax {
        CallSyntax::Path(parts) => parts.join("."),
        CallSyntax::SelfMethod(method) => method.clone(),
        CallSyntax::Method { receiver, method } => format!("{receiver}#{method}"),
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
    if let Some(ordinal) = function
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
    let body = match binding_body.kind() {
        "fun_expression" => {
            parameters.extend(direct_named_children(binding_body, "parameter"));
            binding_body
                .child_by_field_name("body")
                .unwrap_or(binding_body)
        }
        "function_expression" => {
            if parameters.is_empty() {
                parameters.push(binding_body);
            }
            binding_body
        }
        _ if parameters.is_empty() => return None,
        _ => binding_body,
    };

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

fn collect_calls(
    file: &Path,
    node: Node<'_>,
    source: &str,
    is_callable_body: bool,
    calls: &mut Vec<CallSite>,
) {
    if node.kind() == "application_expression" {
        if let Some(function) = node.child_by_field_name("function") {
            if let Some(parts) = ocaml_value_path(function, source) {
                calls.push(CallSite {
                    syntax: CallSyntax::Path(parts),
                    target: CallTarget::Unresolved,
                    label: CallLabel::new(normalize_source(node_text(node, source))),
                    span: tree_sitter_span(file, node),
                });
            } else if function.kind() == "method_invocation" {
                calls.push(CallSite {
                    syntax: CallSyntax::Path(vec![normalize_source(node_text(function, source))]),
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
                    },
                    label: CallLabel::new(normalize_source(node_text(node, source))),
                    span: tree_sitter_span(file, node),
                });
            }
        }
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

fn ocaml_value_path(function: Node<'_>, source: &str) -> Option<Vec<String>> {
    if !matches!(
        function.kind(),
        "value_path" | "value_name" | "parenthesized_operator"
    ) {
        return None;
    }
    let raw = normalize_source(node_text(function, source));
    let parts = raw
        .split('.')
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
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
}
