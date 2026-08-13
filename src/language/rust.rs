use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use proc_macro2::Span;
use quote::ToTokens;
use rustc_public::CompilerError;
use rustc_public::crate_def::CrateDef;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{
    AggregateKind, Body, CastKind, Operand, Place, PointerCoercion, ProjectionElem, Rvalue,
    StatementKind, TerminatorKind,
};
use rustc_public::ty::{
    AssocContainer, ExistentialTraitRef, RigidTy, TraitRef, Ty, TyKind, VtblEntry,
};
use serde::{Deserialize, Serialize};
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{
    Expr, ExprCall, ExprClosure, ExprMethodCall, FnArg, ImplItem, Item, ItemFn, ItemImpl,
    ItemTrait, Pat, ReturnType, Signature, TraitItem, Visibility,
};

use super::{FileContext, FrontendResult, LanguageFrontend};
use crate::model::{
    CallLabel, CallSite, CallSyntax, CallTarget, DispatchCandidate, DispatchResolution,
    FileAnalysis, FunctionInfo, LanguageFact, LanguageId, SourceSpan, SymbolId,
};

#[derive(Default)]
struct RustSourceExtractor;

static RUSTC_DRIVER_LOCK: Mutex<()> = Mutex::new(());
static TEMP_SOURCE_SEQUENCE: AtomicU64 = AtomicU64::new(0);
const RUSTC_CAPTURE_DIRECTORY: &str = "DIFFKIT_RUSTC_CAPTURE_DIRECTORY";

/// Analyze a standalone, compilable Rust source file with rustc's typed MIR.
///
/// Analyze Rust by combining source-shaped labels and spans with rustc's typed
/// MIR. The source extractor is an internal stage, not a separate analysis
/// mode.
pub fn analyze_semantic_file(path: &Path) -> FrontendResult<FileAnalysis> {
    analyze_semantic_file_with_entries(path, &[])
}

pub fn analyze_semantic_file_with_entries(
    path: &Path,
    entries: &[String],
) -> FrontendResult<FileAnalysis> {
    if !path.is_file() {
        return Err(std::io::Error::other(format!(
            "Rust analysis currently requires a standalone .rs file: {}",
            path.display()
        ))
        .into());
    }

    let source = fs::read_to_string(path)?;
    let syntax = RustSourceExtractor.analyze_file(&FileContext { path, module: &[] }, &source)?;
    let semantic = collect_rustc_program(path)?;
    let analysis = merge_semantic_program(syntax.clone(), semantic);
    let missing_entries = entries
        .iter()
        .filter(|entry| entry.contains('<') && !analysis_has_entry(&analysis, entry))
        .cloned()
        .collect::<Vec<_>>();
    if missing_entries.is_empty() {
        return Ok(analysis);
    }

    let Some(seeded_source) = append_entry_seeds(&source, &missing_entries)? else {
        return Ok(analysis);
    };
    let temporary = TemporaryRustSource::create(&seeded_source)?;
    let temporary_path = temporary.path();
    let mut semantic = collect_rustc_program(&temporary_path)?;
    remap_semantic_file(&mut semantic, &temporary_path, path);
    Ok(merge_semantic_program(syntax, semantic))
}

fn remap_semantic_file(program: &mut SemanticProgram, from: &Path, to: &Path) {
    for function in &mut program.functions {
        if source_files_match(&function.body_span.file, from) {
            function.body_span.file = to.to_path_buf();
        }
        for call in &mut function.calls {
            if source_files_match(&call.span.file, from) {
                call.span.file = to.to_path_buf();
            }
        }
    }
}

pub fn analyze_semantic_source(source: &str, entries: &[String]) -> FrontendResult<FileAnalysis> {
    let temporary = TemporaryRustSource::create(source)?;
    analyze_semantic_file_with_entries(&temporary.path(), entries)
}

/// Whether this process was started by Cargo as DiffKit's rustc workspace
/// wrapper. The binary checks this before parsing user-facing CLI arguments.
pub fn rustc_wrapper_requested() -> bool {
    env::var_os(RUSTC_CAPTURE_DIRECTORY).is_some()
}

/// Run one rustc invocation and persist its semantic result for the parent
/// DiffKit process. Dependency crates are not intercepted because the parent
/// uses `RUSTC_WORKSPACE_WRAPPER`, not the broader `RUSTC_WRAPPER`.
pub fn run_rustc_wrapper() -> FrontendResult<()> {
    let mut arguments = env::args_os().skip(1);
    let rustc = arguments
        .next()
        .ok_or_else(|| std::io::Error::other("rustc wrapper did not receive a compiler path"))?;
    let arguments = arguments.collect::<Vec<_>>();
    let mut driver_arguments = vec![rustc.to_string_lossy().into_owned()];
    driver_arguments.extend(
        arguments
            .iter()
            .cloned()
            .map(|argument| {
                argument
                    .into_string()
                    .map_err(|_| std::io::Error::other("rustc argument is not valid UTF-8"))
            })
            .collect::<Result<Vec<_>, _>>()?,
    );

    // rustc_public's traversal can stall in generated test-harness lowering.
    // Cargo still needs that artifact, so compile it with the original rustc.
    // Changed test-only files are handled by the standalone-file fallback.
    if arguments.iter().any(|argument| argument == "--test") {
        let status = Command::new(&rustc).args(&arguments).status()?;
        return if status.success() {
            Ok(())
        } else {
            Err(std::io::Error::other(format!("rustc test target exited with {status}")).into())
        };
    }

    let program = match rustc_public::run!(&driver_arguments, || {
        std::ops::ControlFlow::<(), SemanticProgram>::Continue(collect_instances())
    }) {
        Ok(program) => program,
        Err(CompilerError::Failed) => {
            return Err(std::io::Error::other("rustc failed during semantic capture").into());
        }
        Err(CompilerError::Skipped) => return Ok(()),
        Err(CompilerError::Interrupted(())) => {
            return Err(std::io::Error::other("rustc semantic capture was interrupted").into());
        }
    };

    persist_semantic_program(&program)
}

fn persist_semantic_program(program: &SemanticProgram) -> FrontendResult<()> {
    let directory = PathBuf::from(env::var_os(RUSTC_CAPTURE_DIRECTORY).ok_or_else(|| {
        std::io::Error::other("semantic capture directory disappeared from the environment")
    })?);
    fs::create_dir_all(&directory)?;
    let sequence = TEMP_SOURCE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let destination = directory.join(format!("{}-{sequence}.json", std::process::id()));
    let temporary = destination.with_extension("json.tmp");
    fs::write(&temporary, serde_json::to_vec(program)?)?;
    fs::rename(temporary, destination)?;
    Ok(())
}

/// Analyze every Rust target selected by Cargo under `project_root` using the
/// exact rustc invocations Cargo produced. The returned graph fragment is the
/// only representation that crosses into DiffKit's common engine.
pub fn analyze_semantic_project(
    project_root: &Path,
    wrapper_executable: &Path,
    entries: &[String],
) -> FrontendResult<FileAnalysis> {
    let root = project_root.canonicalize()?;
    if !root.join("Cargo.toml").is_file() {
        return Err(std::io::Error::other(format!(
            "no Cargo.toml at Rust project root {}",
            root.display()
        ))
        .into());
    }
    let generic_entries = entries
        .iter()
        .filter(|entry| entry.contains('<'))
        .cloned()
        .collect::<Vec<_>>();
    if generic_entries.is_empty() {
        return capture_semantic_project(&root, wrapper_executable);
    }

    let seeded = SeededRustProject::create(&root)?;
    seed_project_entries(seeded.root(), &generic_entries)?;
    let mut analysis = capture_semantic_project(seeded.root(), wrapper_executable)?;
    remap_analysis_root(&mut analysis, seeded.root(), &root);
    remove_seed_functions(&mut analysis);
    Ok(analysis)
}

fn capture_semantic_project(
    root: &Path,
    wrapper_executable: &Path,
) -> FrontendResult<FileAnalysis> {
    let wrapper = wrapper_executable.canonicalize()?;
    let capture = RustProjectCapture::create()?;
    let output = Command::new("cargo")
        .args(["check", "--workspace", "--all-targets", "--quiet"])
        .current_dir(root)
        .env("RUSTC_WORKSPACE_WRAPPER", &wrapper)
        .env(RUSTC_CAPTURE_DIRECTORY, capture.results())
        .env("CARGO_TARGET_DIR", capture.target())
        .output()?;
    if !output.status.success() {
        let diagnostic = String::from_utf8_lossy(&output.stderr).trim().to_owned();
        return Err(std::io::Error::other(if diagnostic.is_empty() {
            format!("Cargo semantic analysis exited with {}", output.status)
        } else {
            diagnostic
        })
        .into());
    }

    let mut result_files = fs::read_dir(capture.results())?.collect::<Result<Vec<_>, _>>()?;
    result_files.sort_by_key(std::fs::DirEntry::path);
    let mut semantic = SemanticProgram {
        crate_name: String::new(),
        functions: Vec::new(),
    };
    for result_file in result_files {
        if result_file
            .path()
            .extension()
            .and_then(|value| value.to_str())
            != Some("json")
        {
            continue;
        }
        let mut program: SemanticProgram = serde_json::from_slice(&fs::read(result_file.path())?)?;
        semantic.functions.append(&mut program.functions);
    }
    if semantic.functions.is_empty() {
        return Err(std::io::Error::other(format!(
            "Cargo produced no Rust semantic targets under {}",
            root.display()
        ))
        .into());
    }
    semantic.functions.sort_by(|left, right| {
        (&left.key, &left.body_span.file, left.body_span.start_line).cmp(&(
            &right.key,
            &right.body_span.file,
            right.body_span.start_line,
        ))
    });
    semantic.functions.dedup_by(|left, right| {
        left.key == right.key
            && left.body_span.file == right.body_span.file
            && left.body_span.start_line == right.body_span.start_line
            && left.body_span.start_column == right.body_span.start_column
    });

    let syntax = analyze_project_sources(root)?;
    Ok(deduplicate_analysis(merge_semantic_program(
        syntax, semantic,
    )))
}

struct RustProjectCapture {
    directory: PathBuf,
}

impl RustProjectCapture {
    fn create() -> std::io::Result<Self> {
        let sequence = TEMP_SOURCE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = env::temp_dir().join(format!(
            "diffkit-rust-project-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory)?;
        fs::create_dir(directory.join("results"))?;
        Ok(Self { directory })
    }

    fn results(&self) -> PathBuf {
        self.directory.join("results")
    }

    fn target(&self) -> PathBuf {
        self.directory.join("target")
    }
}

impl Drop for RustProjectCapture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

struct SeededRustProject {
    directory: PathBuf,
    root: PathBuf,
}

impl SeededRustProject {
    fn create(source: &Path) -> std::io::Result<Self> {
        let sequence = TEMP_SOURCE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = env::temp_dir().join(format!(
            "diffkit-rust-seeded-{}-{sequence}",
            std::process::id()
        ));
        let root = directory.join("project");
        fs::create_dir_all(&root)?;
        copy_rust_project(source, source, &root)?;
        Ok(Self { directory, root })
    }

    fn root(&self) -> &Path {
        &self.root
    }
}

impl Drop for SeededRustProject {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

fn copy_rust_project(
    source_root: &Path,
    directory: &Path,
    destination: &Path,
) -> std::io::Result<()> {
    let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(std::fs::DirEntry::path);
    for entry in entries {
        let path = entry.path();
        let relative = path.strip_prefix(source_root).unwrap_or(&path);
        if relative.components().any(|component| {
            matches!(
                component.as_os_str().to_str(),
                Some(".git" | "target" | "node_modules" | "_build" | ".zig-cache" | "zig-out")
            )
        }) {
            continue;
        }
        let target = destination.join(relative);
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            fs::create_dir_all(&target)?;
            copy_rust_project(source_root, &path, destination)?;
        } else if file_type.is_file() {
            if let Some(parent) = target.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::copy(path, target)?;
        } else if file_type.is_symlink() {
            let resolved = fs::canonicalize(path)?;
            if resolved.starts_with(source_root) && resolved.is_file() {
                if let Some(parent) = target.parent() {
                    fs::create_dir_all(parent)?;
                }
                fs::copy(resolved, target)?;
            }
        }
    }
    Ok(())
}

fn seed_project_entries(root: &Path, entries: &[String]) -> FrontendResult<()> {
    let mut files = Vec::new();
    collect_rust_sources(root, &mut files)?;
    files.sort();
    for file in files {
        let source = fs::read_to_string(&file)?;
        if let Some(seeded) = append_entry_seeds(&source, entries)? {
            fs::write(file, seeded)?;
        }
    }
    Ok(())
}

fn remap_analysis_root(analysis: &mut FileAnalysis, from: &Path, to: &Path) {
    let remap = |path: &mut PathBuf| {
        if let Ok(relative) = path.strip_prefix(from) {
            *path = to.join(relative);
        }
    };
    for function in &mut analysis.functions {
        remap(&mut function.span.file);
        for call in &mut function.calls {
            remap(&mut call.span.file);
        }
    }
    for fact in &mut analysis.facts {
        remap(&mut fact.span.file);
    }
}

fn remove_seed_functions(analysis: &mut FileAnalysis) {
    let seeds = analysis
        .functions
        .iter()
        .filter(|function| function.label.default.contains("__diffkit_seed_"))
        .map(|function| function.id.clone())
        .collect::<HashSet<_>>();
    analysis
        .functions
        .retain(|function| !seeds.contains(&function.id));
    analysis.facts.retain(|fact| !seeds.contains(&fact.subject));
}

fn analyze_project_sources(root: &Path) -> FrontendResult<FileAnalysis> {
    let mut files = Vec::new();
    collect_rust_sources(root, &mut files)?;
    files.sort();
    let mut combined = FileAnalysis::default();
    for file in files {
        let source = fs::read_to_string(&file)?;
        let module = rust_module_path(root, &file);
        let mut analysis = RustSourceExtractor.analyze_file(
            &FileContext {
                path: &file,
                module: &module,
            },
            &source,
        )?;
        combined.functions.append(&mut analysis.functions);
        combined.facts.append(&mut analysis.facts);
    }
    Ok(combined)
}

fn collect_rust_sources(directory: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(std::fs::DirEntry::path);
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            if !matches!(
                path.file_name().and_then(|name| name.to_str()),
                Some(".git" | "target" | "node_modules" | ".zig-cache" | "zig-out" | "_build")
            ) {
                collect_rust_sources(&path, files)?;
            }
        } else if file_type.is_file()
            && path.extension().and_then(|extension| extension.to_str()) == Some("rs")
        {
            files.push(path);
        }
    }
    Ok(())
}

fn rust_module_path(root: &Path, file: &Path) -> Vec<String> {
    let source_root = root.join("src");
    let relative = file
        .strip_prefix(&source_root)
        .or_else(|_| file.strip_prefix(root))
        .unwrap_or(file);
    let mut parts = relative
        .parent()
        .into_iter()
        .flat_map(Path::components)
        .filter_map(|component| component.as_os_str().to_str().map(ToOwned::to_owned))
        .collect::<Vec<_>>();
    let stem = file
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or_default();
    if !matches!(stem, "lib" | "main" | "mod") {
        parts.push(stem.to_owned());
    }
    parts
}

fn deduplicate_analysis(analysis: FileAnalysis) -> FileAnalysis {
    let mut functions = BTreeMap::<SymbolId, FunctionInfo>::new();
    for function in analysis.functions {
        functions
            .entry(function.id.clone())
            .and_modify(|existing| {
                for call in &function.calls {
                    if !existing.calls.contains(call) {
                        existing.calls.push(call.clone());
                    }
                }
                existing.calls.sort_by_key(|call| {
                    (
                        call.span.file.clone(),
                        call.span.start_line,
                        call.span.start_column,
                    )
                });
            })
            .or_insert(function);
    }
    FileAnalysis {
        functions: functions.into_values().collect(),
        facts: analysis.facts,
    }
}

fn analysis_has_entry(analysis: &FileAnalysis, entry: &str) -> bool {
    let expected = entry.replace('.', "::").replace("::<", "<");
    analysis.functions.iter().any(|function| {
        let label = &function.label.default;
        let callable =
            outer_call_arguments_start(label).map_or(label.as_str(), |index| &label[..index]);
        callable == expected || callable.ends_with(&format!("::{expected}"))
    })
}

fn append_entry_seeds(source: &str, entries: &[String]) -> FrontendResult<Option<String>> {
    let file = syn::parse_file(source)?;
    let mut functions = Vec::new();
    collect_seedable_functions(&file.items, &[], &mut functions);
    let mut seeds = Vec::new();

    for entry in entries {
        let Some(generic_start) = entry.find('<') else {
            continue;
        };
        if !entry.ends_with('>') || entry.starts_with('<') {
            continue;
        }
        let base = entry[..generic_start]
            .trim_end_matches("::")
            .replace('.', "::");
        let generic_arguments = &entry[generic_start + 1..entry.len() - 1];
        let lookup = base.strip_prefix("crate::").unwrap_or(&base);
        let mut matches = functions
            .iter()
            .filter(|function| {
                lookup == function.qualified_name
                    || (!lookup.contains("::") && lookup == function.name)
            })
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            continue;
        }
        let function = matches.pop().expect("one seedable function matched");
        let arguments = (0..function.argument_count)
            .map(|_| "::core::mem::MaybeUninit::uninit().assume_init()")
            .collect::<Vec<_>>()
            .join(", ");
        seeds.push(format!(
            "\n#[doc(hidden)]\n#[allow(dead_code, invalid_value, unused_unsafe)]\nfn __diffkit_seed_{}() {{\n    unsafe {{ let _ = {}::<{}>({}); }}\n}}\n",
            seeds.len(), function.qualified_name, generic_arguments, arguments
        ));
    }

    if seeds.is_empty() {
        Ok(None)
    } else {
        let mut seeded = source.to_owned();
        seeded.extend(seeds);
        Ok(Some(seeded))
    }
}

struct SeedableFunction {
    name: String,
    qualified_name: String,
    argument_count: usize,
}

fn collect_seedable_functions(
    items: &[Item],
    module: &[String],
    functions: &mut Vec<SeedableFunction>,
) {
    for item in items {
        match item {
            Item::Fn(function) => {
                let name = function.sig.ident.to_string();
                let qualified_name = module
                    .iter()
                    .map(String::as_str)
                    .chain(std::iter::once(name.as_str()))
                    .collect::<Vec<_>>()
                    .join("::");
                functions.push(SeedableFunction {
                    name,
                    qualified_name,
                    argument_count: function.sig.inputs.len(),
                });
            }
            Item::Mod(item_mod) => {
                if let Some((_, nested)) = &item_mod.content {
                    let mut nested_module = module.to_vec();
                    nested_module.push(item_mod.ident.to_string());
                    collect_seedable_functions(nested, &nested_module, functions);
                }
            }
            _ => {}
        }
    }
}

impl TemporaryRustSource {
    fn create(source: &str) -> std::io::Result<Self> {
        let sequence = TEMP_SOURCE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir().join(format!(
            "diffkit-rust-source-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory)?;
        let temporary = TemporaryRustSource { directory };
        let path = temporary.directory.join("input.rs");
        fs::write(&path, source)?;
        Ok(temporary)
    }

    fn path(&self) -> PathBuf {
        self.directory.join("input.rs")
    }
}

struct TemporaryRustSource {
    directory: PathBuf,
}

impl Drop for TemporaryRustSource {
    fn drop(&mut self) {
        let _ = fs::remove_file(self.directory.join("input.rs"));
        let _ = fs::remove_dir(&self.directory);
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct SemanticProgram {
    crate_name: String,
    functions: Vec<SemanticFunction>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct SemanticFunction {
    key: String,
    display: String,
    body_span: SourceSpan,
    calls: Vec<SemanticCall>,
    parameter_types: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct SemanticCall {
    target: SemanticCallTarget,
    definition_name: String,
    span: SourceSpan,
    argument_types: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
enum SemanticCallTarget {
    Direct {
        key: String,
        display: String,
    },
    Dynamic {
        key: String,
        display: String,
        candidates: Vec<SemanticDispatchCandidate>,
        open: bool,
    },
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct SemanticDispatchCandidate {
    key: String,
    display: String,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct DynFlow {
    concrete: Vec<TraitRef>,
    parameters: Vec<usize>,
    unknown: bool,
}

impl DynFlow {
    fn parameter(index: usize) -> Self {
        Self {
            concrete: Vec::new(),
            parameters: vec![index],
            unknown: false,
        }
    }

    fn concrete(trait_ref: TraitRef) -> Self {
        Self {
            concrete: vec![trait_ref],
            parameters: Vec::new(),
            unknown: false,
        }
    }

    fn unknown() -> Self {
        Self {
            concrete: Vec::new(),
            parameters: Vec::new(),
            unknown: true,
        }
    }

    fn is_empty(&self) -> bool {
        self.concrete.is_empty() && self.parameters.is_empty() && !self.unknown
    }

    fn merge(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for candidate in &other.concrete {
            if !self.concrete.contains(candidate) {
                self.concrete.push(candidate.clone());
                changed = true;
            }
        }
        for parameter in &other.parameters {
            if !self.parameters.contains(parameter) {
                self.parameters.push(*parameter);
                changed = true;
            }
        }
        if other.unknown && !self.unknown {
            self.unknown = true;
            changed = true;
        }
        self.parameters.sort_unstable();
        changed
    }
}

#[derive(Clone, Debug, Default)]
struct ResolvedDynFlow {
    concrete: Vec<TraitRef>,
    unknown: bool,
}

impl ResolvedDynFlow {
    fn merge(&mut self, other: &Self) {
        for candidate in &other.concrete {
            if !self.concrete.contains(candidate) {
                self.concrete.push(candidate.clone());
            }
        }
        self.unknown |= other.unknown;
    }
}

#[derive(Clone)]
struct RawSemanticFunction {
    key: String,
    display: String,
    body_span: SourceSpan,
    calls: Vec<RawSemanticCall>,
    parameter_types: Vec<String>,
}

#[derive(Clone)]
struct RawSemanticCall {
    target: RawSemanticCallTarget,
    definition_name: String,
    span: SourceSpan,
    argument_types: Vec<String>,
    argument_flows: Vec<DynFlow>,
}

#[derive(Clone)]
enum RawSemanticCallTarget {
    Direct {
        key: String,
        display: String,
    },
    Dynamic {
        dispatch: Instance,
        key: String,
        display: String,
        receiver: DynFlow,
    },
}

#[derive(Clone)]
struct InstanceBody {
    instance: Instance,
    body: Body,
}

#[derive(Clone, Default)]
struct MirCallFlow {
    arguments: Vec<DynFlow>,
}

#[derive(Default)]
struct BodyDynAnalysis {
    calls: Vec<Option<MirCallFlow>>,
    return_flow: DynFlow,
}

fn collect_rustc_program(path: &Path) -> FrontendResult<SemanticProgram> {
    let _driver_guard = RUSTC_DRIVER_LOCK
        .lock()
        .map_err(|_| std::io::Error::other("rustc semantic driver lock was poisoned"))?;
    let arguments = vec![
        "rustc".to_owned(),
        path.display().to_string(),
        "--crate-name=diffkit_input".to_owned(),
        "--crate-type=lib".to_owned(),
        "--edition=2024".to_owned(),
        "--cap-lints=allow".to_owned(),
    ];

    match rustc_public::run!(&arguments, || {
        std::ops::ControlFlow::<SemanticProgram, ()>::Break(collect_instances())
    }) {
        Err(CompilerError::Interrupted(program)) => Ok(program),
        Err(CompilerError::Failed) => Err(std::io::Error::other(format!(
            "rustc failed to compile {} for semantic analysis",
            path.display()
        ))
        .into()),
        Err(CompilerError::Skipped) => Err(std::io::Error::other(
            "rustc skipped semantic analysis before its callback ran",
        )
        .into()),
        Ok(()) => Err(std::io::Error::other(
            "rustc semantic callback unexpectedly completed without analysis",
        )
        .into()),
    }
}

fn collect_instances() -> SemanticProgram {
    let crate_name = rustc_public::local_crate().name.to_string();
    let trait_method_implementations = trait_method_implementations();
    let (instance_bodies, observed_vtables) =
        collect_instance_bodies(&trait_method_implementations);
    let local_instances = instance_bodies
        .iter()
        .map(|item| item.instance)
        .collect::<HashSet<_>>();
    let mut return_summaries = HashMap::<Instance, DynFlow>::new();

    // Return-value summaries remain symbolic in terms of the callee's formal
    // parameters. This lets a trait object cross ordinary helper functions
    // without losing its concrete provenance. The lattice is finite, so the
    // monotone iteration also handles recursive helpers.
    let max_iterations = instance_bodies
        .iter()
        .map(|item| item.body.locals().len())
        .sum::<usize>()
        .saturating_add(instance_bodies.len())
        .max(1);
    let mut summaries_converged = false;
    for _ in 0..max_iterations {
        let mut changed = false;
        for item in &instance_bodies {
            let analysis = analyze_body_dyn_flows(&item.body, &return_summaries, &local_instances);
            changed |= return_summaries
                .entry(item.instance)
                .or_default()
                .merge(&analysis.return_flow);
        }
        if !changed {
            summaries_converged = true;
            break;
        }
    }
    if !summaries_converged {
        for item in &instance_bodies {
            if type_contains_dyn(item.body.ret_local().ty) {
                return_summaries.entry(item.instance).or_default().unknown = true;
            }
        }
    }

    let mut raw_functions = Vec::new();
    for item in &instance_bodies {
        let instance = item.instance;
        let body = &item.body;
        let instance_name = instance.name();
        let analysis = analyze_body_dyn_flows(body, &return_summaries, &local_instances);
        let mut calls = Vec::new();
        for (block_index, block) in body.blocks.iter().enumerate() {
            let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                continue;
            };
            let Some(target) = resolve_called_instance(body, func) else {
                continue;
            };
            let name = target.name();
            let definition_name = target.def.name();
            let call_flow = analysis
                .calls
                .get(block_index)
                .and_then(Option::as_ref)
                .cloned()
                .unwrap_or_default();
            let target = match target.kind {
                InstanceKind::Virtual { .. } => RawSemanticCallTarget::Dynamic {
                    dispatch: target,
                    key: normalize_instance_key(&name),
                    display: normalize_instance_display(&name, &crate_name),
                    receiver: call_flow
                        .arguments
                        .first()
                        .cloned()
                        .unwrap_or_else(DynFlow::unknown),
                },
                _ => RawSemanticCallTarget::Direct {
                    key: normalize_instance_key(&name),
                    display: normalize_instance_display(&name, &crate_name),
                },
            };
            calls.push(RawSemanticCall {
                target,
                definition_name,
                span: rustc_source_span(block.terminator.span),
                argument_types: args
                    .iter()
                    .filter_map(|argument| argument.ty(body.locals()).ok())
                    .map(|ty| normalize_type_display(&ty.to_string(), &crate_name))
                    .collect(),
                argument_flows: call_flow.arguments,
            });
        }
        calls.sort_by_key(|call| {
            (
                call.span.start_line,
                call.span.start_column,
                call.span.end_line,
                call.span.end_column,
            )
        });
        raw_functions.push(RawSemanticFunction {
            key: normalize_instance_key(&instance_name),
            display: normalize_instance_display(&instance_name, &crate_name),
            body_span: rustc_source_span(body.span),
            calls,
            parameter_types: body
                .arg_locals()
                .iter()
                .map(|argument| normalize_type_display(&argument.ty.to_string(), &crate_name))
                .collect(),
        });
    }

    let mut functions = specialize_semantic_functions(
        &raw_functions,
        &observed_vtables,
        &trait_method_implementations,
        &crate_name,
    );
    functions.sort_by(|left, right| left.key.cmp(&right.key));
    SemanticProgram {
        crate_name,
        functions,
    }
}

fn collect_instance_bodies(
    trait_method_implementations: &HashMap<rustc_public::DefId, rustc_public::DefId>,
) -> (Vec<InstanceBody>, Vec<TraitRef>) {
    let mut queue = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| matches!(item.kind(), rustc_public::ItemKind::Fn))
        .filter_map(|item| Instance::try_from(item).ok())
        .collect::<VecDeque<_>>();
    let mut visited = HashSet::new();
    let mut bodies = Vec::new();
    let mut observed_vtables = Vec::<TraitRef>::new();

    loop {
        while let Some(instance) = queue.pop_front() {
            if !visited.insert(instance) {
                continue;
            }
            let Some(body) = instance.body() else {
                continue;
            };

            let mut local_vtables = Vec::new();
            collect_observed_vtables(&body, &mut local_vtables);
            for vtable in local_vtables {
                if !observed_vtables.contains(&vtable) {
                    observed_vtables.push(vtable);
                }
            }

            for block in &body.blocks {
                let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                    continue;
                };
                let Some(target) = resolve_called_instance(&body, func) else {
                    continue;
                };
                if !matches!(target.kind, InstanceKind::Virtual { .. })
                    && target.def.krate().is_local
                    && target.has_body()
                {
                    queue.push_back(target);
                }
            }
            bodies.push(InstanceBody { instance, body });
        }

        for item in &bodies {
            for block in &item.body.blocks {
                let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                    continue;
                };
                let Some(dispatch) = resolve_called_instance(&item.body, func) else {
                    continue;
                };
                if !matches!(dispatch.kind, InstanceKind::Virtual { .. }) {
                    continue;
                }
                for trait_ref in &observed_vtables {
                    let Some(candidate) = resolve_dispatch_candidate(
                        dispatch,
                        trait_ref,
                        trait_method_implementations,
                    ) else {
                        continue;
                    };
                    if candidate.def.krate().is_local
                        && candidate.has_body()
                        && !visited.contains(&candidate)
                    {
                        queue.push_back(candidate);
                    }
                }
            }
        }
        if queue.is_empty() {
            break;
        }
    }
    (bodies, observed_vtables)
}

fn collect_observed_vtables(body: &rustc_public::mir::Body, observed: &mut Vec<TraitRef>) {
    for block in &body.blocks {
        for statement in &block.statements {
            let StatementKind::Assign(
                _,
                Rvalue::Cast(
                    CastKind::PointerCoercion(PointerCoercion::Unsize),
                    operand,
                    target_ty,
                ),
            ) = &statement.kind
            else {
                continue;
            };
            let Ok(source_ty) = operand.ty(body.locals()) else {
                continue;
            };
            let Some((concrete_ty, principal)) = dyn_coercion(source_ty, *target_ty) else {
                continue;
            };
            let trait_ref = TraitRef::new(principal.def_id, concrete_ty, &principal.generic_args);
            if !observed.contains(&trait_ref) {
                observed.push(trait_ref);
            }
        }
    }
}

fn dyn_coercion(source: Ty, target: Ty) -> Option<(Ty, ExistentialTraitRef)> {
    let target_kind = target.kind();
    if let Some(principal) = target_kind.trait_principal() {
        // A trait upcast (`dyn Child` -> `dyn Parent`) does not reveal a
        // concrete implementation. Only thin-to-wide coercions contribute an
        // concrete receiver-flow candidate here.
        return (!source.kind().is_trait()).then_some((source, principal.value));
    }

    match (source.kind(), target_kind) {
        (
            TyKind::RigidTy(RigidTy::Ref(_, source, _)),
            TyKind::RigidTy(RigidTy::Ref(_, target, _)),
        )
        | (
            TyKind::RigidTy(RigidTy::RawPtr(source, _)),
            TyKind::RigidTy(RigidTy::RawPtr(target, _)),
        ) => dyn_coercion(source, target),
        (
            TyKind::RigidTy(RigidTy::Adt(source_def, source_args)),
            TyKind::RigidTy(RigidTy::Adt(target_def, target_args)),
        ) if source_def == target_def => source_args
            .0
            .iter()
            .zip(&target_args.0)
            .filter_map(|(source, target)| Some((*source.ty()?, *target.ty()?)))
            .find_map(|(source, target)| dyn_coercion(source, target)),
        _ => None,
    }
}

fn trait_method_implementations() -> HashMap<rustc_public::DefId, rustc_public::DefId> {
    rustc_public::all_trait_impls()
        .into_iter()
        .flat_map(|implementation| implementation.associated_items())
        .filter_map(|item| match item.container {
            AssocContainer::TraitImpl(trait_item) => {
                Some((item.def_id.def_id(), trait_item.def_id()))
            }
            AssocContainer::InherentImpl | AssocContainer::Trait => None,
        })
        .collect()
}

fn resolve_called_instance(body: &Body, operand: &Operand) -> Option<Instance> {
    let function_type = operand.ty(body.locals()).ok()?;
    let function_kind = function_type.kind();
    let (definition, arguments) = function_kind.fn_def()?;
    Instance::resolve(definition, arguments).ok()
}

fn resolve_dispatch_candidate(
    dispatch: Instance,
    trait_ref: &TraitRef,
    trait_method_implementations: &HashMap<rustc_public::DefId, rustc_public::DefId>,
) -> Option<Instance> {
    let InstanceKind::Virtual { idx } = dispatch.kind else {
        return None;
    };
    let VtblEntry::Method(candidate) = trait_ref.vtable_entry(idx)? else {
        return None;
    };
    let trait_method = dispatch.def.def_id();
    let candidate_method = candidate.def.def_id();
    (candidate_method == trait_method
        || trait_method_implementations.get(&candidate_method) == Some(&trait_method))
    .then_some(candidate)
}

type DynState = HashMap<Place, DynFlow>;

fn analyze_body_dyn_flows(
    body: &Body,
    return_summaries: &HashMap<Instance, DynFlow>,
    local_instances: &HashSet<Instance>,
) -> BodyDynAnalysis {
    let mut result = BodyDynAnalysis {
        calls: vec![None; body.blocks.len()],
        return_flow: DynFlow::default(),
    };
    if body.blocks.is_empty() {
        return result;
    }

    let mut entry = DynState::new();
    for (index, argument) in body.arg_locals().iter().enumerate() {
        if type_contains_dyn(argument.ty) {
            entry.insert(Place::from(index + 1), DynFlow::parameter(index));
        }
    }
    let mut incoming = vec![None::<DynState>; body.blocks.len()];
    incoming[0] = Some(entry);
    let mut pending = VecDeque::from([0usize]);

    let mut iterations = 0usize;
    let max_iterations = body
        .blocks
        .len()
        .saturating_mul(body.locals().len().saturating_add(1))
        .saturating_mul(16)
        .max(1);
    while let Some(block_index) = pending.pop_front() {
        iterations += 1;
        if iterations > max_iterations {
            degrade_dyn_analysis_to_unknown(body, &mut result);
            break;
        }
        let Some(mut state) = incoming[block_index].clone() else {
            continue;
        };
        let block = &body.blocks[block_index];
        for statement in &block.statements {
            transfer_dyn_statement(body, &mut state, statement);
        }

        match &block.terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                let argument_flows = args
                    .iter()
                    .map(|argument| dyn_flow_for_operand(body, &state, argument))
                    .collect::<Vec<_>>();
                merge_call_flow(
                    &mut result.calls[block_index],
                    &MirCallFlow {
                        arguments: argument_flows.clone(),
                    },
                );

                let destination_flow = resolve_called_instance(body, func).map_or_else(
                    || unknown_if_dyn_place(body, destination),
                    |callee| {
                        if matches!(callee.kind, InstanceKind::Virtual { .. }) {
                            unknown_if_dyn_place(body, destination)
                        } else if let Some(summary) = return_summaries.get(&callee) {
                            resolve_symbolic_flow(summary, &argument_flows)
                        } else if local_instances.contains(&callee) {
                            DynFlow::default()
                        } else {
                            unknown_if_dyn_place(body, destination)
                        }
                    },
                );

                for successor in block.terminator.successors() {
                    let mut outgoing = state.clone();
                    if Some(successor) == *target {
                        write_dyn_place(&mut outgoing, destination, destination_flow.clone());
                    }
                    if merge_dyn_state(&mut incoming[successor], &outgoing) {
                        pending.push_back(successor);
                    }
                }
            }
            TerminatorKind::Return => {
                let flow = read_dyn_place(&state, &Place::from(0));
                result.return_flow.merge(&flow);
            }
            _ => {
                for successor in block.terminator.successors() {
                    if merge_dyn_state(&mut incoming[successor], &state) {
                        pending.push_back(successor);
                    }
                }
            }
        }
    }
    result
}

fn degrade_dyn_analysis_to_unknown(body: &Body, analysis: &mut BodyDynAnalysis) {
    if type_contains_dyn(body.ret_local().ty) {
        analysis.return_flow.unknown = true;
    }
    for (block_index, block) in body.blocks.iter().enumerate() {
        let TerminatorKind::Call { args, .. } = &block.terminator.kind else {
            continue;
        };
        let call = analysis.calls[block_index].get_or_insert_with(|| MirCallFlow {
            arguments: vec![DynFlow::default(); args.len()],
        });
        call.arguments.resize_with(args.len(), DynFlow::default);
        for (argument, flow) in args.iter().zip(&mut call.arguments) {
            if argument.ty(body.locals()).is_ok_and(type_contains_dyn) {
                flow.unknown = true;
            }
        }
    }
}

fn transfer_dyn_statement(
    body: &Body,
    state: &mut DynState,
    statement: &rustc_public::mir::Statement,
) {
    let StatementKind::Assign(destination, value) = &statement.kind else {
        return;
    };
    let flow = dyn_flow_for_rvalue(body, state, value);
    write_dyn_place(state, destination, flow);

    let Rvalue::Aggregate(kind, operands) = value else {
        return;
    };
    for (index, operand) in operands.iter().enumerate() {
        let Ok(operand_ty) = operand.ty(body.locals()) else {
            continue;
        };
        let projection = match kind {
            AggregateKind::Tuple | AggregateKind::Adt(..) => {
                Some(ProjectionElem::Field(index, operand_ty))
            }
            AggregateKind::Array(_) => Some(ProjectionElem::ConstantIndex {
                offset: index as u64,
                min_length: operands.len() as u64,
                from_end: false,
            }),
            AggregateKind::Closure(..)
            | AggregateKind::Coroutine(..)
            | AggregateKind::CoroutineClosure(..)
            | AggregateKind::RawPtr(..) => None,
        };
        let Some(projection) = projection else {
            continue;
        };
        let mut field = destination.clone();
        field.projection.push(projection);
        write_dyn_place(state, &field, dyn_flow_for_operand(body, state, operand));
    }
}

fn dyn_flow_for_rvalue(body: &Body, state: &DynState, value: &Rvalue) -> DynFlow {
    let mut flow = match value {
        Rvalue::Use(operand, _) | Rvalue::Repeat(operand, _) => {
            dyn_flow_for_operand(body, state, operand)
        }
        Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), operand, target_ty) => {
            operand
                .ty(body.locals())
                .ok()
                .and_then(|source_ty| dyn_coercion(source_ty, *target_ty))
                .map(|(concrete_ty, principal)| {
                    DynFlow::concrete(TraitRef::new(
                        principal.def_id,
                        concrete_ty,
                        &principal.generic_args,
                    ))
                })
                .unwrap_or_else(|| dyn_flow_for_operand(body, state, operand))
        }
        Rvalue::Cast(_, operand, _) => dyn_flow_for_operand(body, state, operand),
        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) | Rvalue::CopyForDeref(place) => {
            read_dyn_place(state, place)
        }
        Rvalue::Aggregate(_, operands) => {
            let mut aggregate = DynFlow::default();
            for operand in operands {
                aggregate.merge(&dyn_flow_for_operand(body, state, operand));
            }
            aggregate
        }
        Rvalue::BinaryOp(_, left, right) | Rvalue::CheckedBinaryOp(_, left, right) => {
            let mut combined = dyn_flow_for_operand(body, state, left);
            combined.merge(&dyn_flow_for_operand(body, state, right));
            combined
        }
        Rvalue::UnaryOp(_, operand) => dyn_flow_for_operand(body, state, operand),
        Rvalue::ThreadLocalRef(_) | Rvalue::Discriminant(_) | Rvalue::Len(_) => DynFlow::default(),
    };
    if flow.is_empty() && value.ty(body.locals()).is_ok_and(type_contains_dyn) {
        flow.unknown = true;
    }
    flow
}

fn dyn_flow_for_operand(body: &Body, state: &DynState, operand: &Operand) -> DynFlow {
    let mut flow = match operand {
        Operand::Copy(place) | Operand::Move(place) => read_dyn_place(state, place),
        Operand::Constant(_) | Operand::RuntimeChecks(_) => DynFlow::default(),
    };
    if flow.is_empty() && operand.ty(body.locals()).is_ok_and(type_contains_dyn) {
        flow.unknown = true;
    }
    flow
}

fn unknown_if_dyn_place(body: &Body, place: &Place) -> DynFlow {
    place
        .ty(body.locals())
        .ok()
        .filter(|ty| type_contains_dyn(*ty))
        .map_or_else(DynFlow::default, |_| DynFlow::unknown())
}

fn type_contains_dyn(ty: Ty) -> bool {
    ty.to_string().contains("dyn ")
}

fn read_dyn_place(state: &DynState, place: &Place) -> DynFlow {
    if let Some(flow) = state.get(place) {
        return flow.clone();
    }
    let mut ancestor = place.clone();
    while ancestor.projection.pop().is_some() {
        if let Some(flow) = state.get(&ancestor) {
            let suffix = &place.projection[ancestor.projection.len()..];
            return if suffix
                .iter()
                .all(|projection| matches!(projection, ProjectionElem::Deref))
            {
                flow.clone()
            } else {
                // Whole-value flow is not enough to assign a candidate to one
                // particular field. Keep this unresolved instead of leaking
                // candidates from sibling fields.
                DynFlow::unknown()
            };
        }
    }
    let mut result = DynFlow::default();
    for (candidate, flow) in state {
        if place_is_prefix(place, candidate) {
            result.merge(flow);
        }
    }
    result
}

fn write_dyn_place(state: &mut DynState, place: &Place, flow: DynFlow) {
    state.retain(|candidate, _| !place_is_prefix(place, candidate));
    if !flow.is_empty() {
        state.insert(place.clone(), flow);
    }
}

fn place_is_prefix(prefix: &Place, place: &Place) -> bool {
    prefix.local == place.local
        && prefix.projection.len() <= place.projection.len()
        && place.projection.starts_with(&prefix.projection)
}

fn merge_dyn_state(destination: &mut Option<DynState>, source: &DynState) -> bool {
    let Some(destination) = destination else {
        *destination = Some(source.clone());
        return true;
    };
    let mut changed = false;
    for (place, flow) in source {
        changed |= destination.entry(place.clone()).or_default().merge(flow);
    }
    changed
}

fn merge_call_flow(destination: &mut Option<MirCallFlow>, source: &MirCallFlow) {
    let Some(destination) = destination else {
        *destination = Some(source.clone());
        return;
    };
    if destination.arguments.len() < source.arguments.len() {
        destination
            .arguments
            .resize_with(source.arguments.len(), DynFlow::default);
    }
    for (destination, source) in destination.arguments.iter_mut().zip(&source.arguments) {
        destination.merge(source);
    }
}

fn resolve_symbolic_flow(flow: &DynFlow, arguments: &[DynFlow]) -> DynFlow {
    let mut resolved = DynFlow {
        concrete: flow.concrete.clone(),
        parameters: Vec::new(),
        unknown: flow.unknown,
    };
    for parameter in &flow.parameters {
        if let Some(argument) = arguments.get(*parameter) {
            resolved.merge(argument);
        } else {
            resolved.unknown = true;
        }
    }
    resolved
}

fn specialize_semantic_functions(
    raw_functions: &[RawSemanticFunction],
    observed_vtables: &[TraitRef],
    trait_method_implementations: &HashMap<rustc_public::DefId, rustc_public::DefId>,
    crate_name: &str,
) -> Vec<SemanticFunction> {
    let index = raw_functions
        .iter()
        .enumerate()
        .map(|(index, function)| (function.key.clone(), index))
        .collect::<HashMap<_, _>>();
    let mut incoming = vec![0usize; raw_functions.len()];
    for function in raw_functions {
        for call in &function.calls {
            match &call.target {
                RawSemanticCallTarget::Direct { key, .. } => {
                    if let Some(target) = index.get(key) {
                        incoming[*target] += 1;
                    }
                }
                RawSemanticCallTarget::Dynamic { dispatch, .. } => {
                    for trait_ref in observed_vtables {
                        let Some(candidate) = resolve_dispatch_candidate(
                            *dispatch,
                            trait_ref,
                            trait_method_implementations,
                        ) else {
                            continue;
                        };
                        if let Some(target) = index.get(&normalize_instance_key(&candidate.name()))
                        {
                            incoming[*target] += 1;
                        }
                    }
                }
            }
        }
    }

    let mut pending = VecDeque::<(usize, Vec<ResolvedDynFlow>)>::new();
    for (function, count) in incoming.iter().enumerate() {
        if *count == 0 {
            pending.push_back((function, root_dyn_context(&raw_functions[function])));
        }
    }
    let mut visited = HashSet::new();
    let mut covered_raw = HashSet::new();
    let mut functions = Vec::new();

    loop {
        while let Some((raw_index, context)) = pending.pop_front() {
            let raw = &raw_functions[raw_index];
            let function_key = specialized_function_key(raw, &context);
            if !visited.insert(function_key.clone()) {
                continue;
            }
            covered_raw.insert(raw_index);
            let mut calls = Vec::new();

            for raw_call in &raw.calls {
                let target = match &raw_call.target {
                    RawSemanticCallTarget::Direct { key, display } => {
                        let specialized = index.get(key).map_or_else(
                            || key.clone(),
                            |callee_index| {
                                let callee = &raw_functions[*callee_index];
                                let callee_context =
                                    call_dyn_context(callee, &raw_call.argument_flows, &context);
                                let key = specialized_function_key(callee, &callee_context);
                                pending.push_back((*callee_index, callee_context));
                                key
                            },
                        );
                        SemanticCallTarget::Direct {
                            key: specialized,
                            display: display.clone(),
                        }
                    }
                    RawSemanticCallTarget::Dynamic {
                        dispatch,
                        key,
                        display,
                        receiver,
                    } => {
                        let receiver = resolve_context_flow(receiver, &context);
                        let mut candidates = Vec::new();
                        for trait_ref in &receiver.concrete {
                            let Some(candidate) = resolve_dispatch_candidate(
                                *dispatch,
                                trait_ref,
                                trait_method_implementations,
                            ) else {
                                continue;
                            };
                            let candidate_name = candidate.name();
                            let raw_candidate_key = normalize_instance_key(&candidate_name);
                            let candidate_key = index.get(&raw_candidate_key).map_or_else(
                                || raw_candidate_key.clone(),
                                |candidate_index| {
                                    let candidate_function = &raw_functions[*candidate_index];
                                    let candidate_context = call_dyn_context(
                                        candidate_function,
                                        &raw_call.argument_flows,
                                        &context,
                                    );
                                    let key = specialized_function_key(
                                        candidate_function,
                                        &candidate_context,
                                    );
                                    pending.push_back((*candidate_index, candidate_context));
                                    key
                                },
                            );
                            if !candidates
                                .iter()
                                .any(|existing: &SemanticDispatchCandidate| {
                                    existing.key == candidate_key
                                })
                            {
                                candidates.push(SemanticDispatchCandidate {
                                    key: candidate_key,
                                    display: normalize_instance_display(
                                        &candidate_name,
                                        crate_name,
                                    ),
                                });
                            }
                        }
                        candidates.sort_by(|left, right| left.key.cmp(&right.key));
                        SemanticCallTarget::Dynamic {
                            key: key.clone(),
                            display: display.clone(),
                            candidates,
                            open: receiver.unknown,
                        }
                    }
                };
                calls.push(SemanticCall {
                    target,
                    definition_name: raw_call.definition_name.clone(),
                    span: raw_call.span.clone(),
                    argument_types: raw_call.argument_types.clone(),
                });
            }

            functions.push(SemanticFunction {
                key: function_key,
                display: raw.display.clone(),
                body_span: raw.body_span.clone(),
                calls,
                parameter_types: raw.parameter_types.clone(),
            });
        }

        let Some(uncovered) = (0..raw_functions.len()).find(|index| !covered_raw.contains(index))
        else {
            break;
        };
        pending.push_back((uncovered, root_dyn_context(&raw_functions[uncovered])));
    }
    functions
}

fn root_dyn_context(function: &RawSemanticFunction) -> Vec<ResolvedDynFlow> {
    function
        .parameter_types
        .iter()
        .map(|parameter| ResolvedDynFlow {
            concrete: Vec::new(),
            unknown: parameter.contains("dyn "),
        })
        .collect()
}

fn call_dyn_context(
    callee: &RawSemanticFunction,
    arguments: &[DynFlow],
    caller_context: &[ResolvedDynFlow],
) -> Vec<ResolvedDynFlow> {
    callee
        .parameter_types
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            if !parameter.contains("dyn ") {
                return ResolvedDynFlow::default();
            }
            arguments.get(index).map_or_else(
                || ResolvedDynFlow {
                    concrete: Vec::new(),
                    unknown: true,
                },
                |flow| {
                    let mut resolved = resolve_context_flow(flow, caller_context);
                    if resolved.concrete.is_empty() && !resolved.unknown {
                        resolved.unknown = true;
                    }
                    resolved
                },
            )
        })
        .collect()
}

fn resolve_context_flow(flow: &DynFlow, context: &[ResolvedDynFlow]) -> ResolvedDynFlow {
    let mut resolved = ResolvedDynFlow {
        concrete: flow.concrete.clone(),
        unknown: flow.unknown,
    };
    for parameter in &flow.parameters {
        if let Some(argument) = context.get(*parameter) {
            resolved.merge(argument);
        } else {
            resolved.unknown = true;
        }
    }
    resolved
}

fn specialized_function_key(function: &RawSemanticFunction, context: &[ResolvedDynFlow]) -> String {
    let bindings = context
        .iter()
        .enumerate()
        .filter(|(index, value)| {
            function
                .parameter_types
                .get(*index)
                .is_some_and(|parameter| parameter.contains("dyn "))
                || !value.concrete.is_empty()
                || value.unknown
        })
        .map(|(index, value)| {
            let mut candidates = value
                .concrete
                .iter()
                .map(|trait_ref| trait_ref.self_ty().to_string())
                .collect::<Vec<_>>();
            candidates.sort();
            if value.unknown {
                candidates.push("?".to_owned());
            }
            format!("{index}={}", candidates.join("|"))
        })
        .collect::<Vec<_>>();
    if bindings.is_empty() {
        function.key.clone()
    } else {
        format!("{}#ctx[dyn:{}]", function.key, bindings.join(","))
    }
}

fn merge_semantic_program(syntax: FileAnalysis, semantic: SemanticProgram) -> FileAnalysis {
    let mut analysis = FileAnalysis::default();

    for semantic_function in semantic.functions {
        let Some(template) =
            best_function_template(&syntax.functions, &semantic_function.body_span)
        else {
            // Compiler-generated functions (drop glue, coroutine shims, etc.)
            // are intentionally omitted until they have explicit source syntax.
            continue;
        };
        let id = semantic_symbol(semantic_function.key);
        let mut claimed_calls = HashSet::new();
        let calls = template
            .calls
            .iter()
            .map(|call| {
                let match_index =
                    best_semantic_call(call, &semantic_function.calls, &claimed_calls);
                let mut resolved = call.clone();
                if let Some(index) = match_index {
                    claimed_calls.insert(index);
                    let semantic_call = &semantic_function.calls[index];
                    match &semantic_call.target {
                        SemanticCallTarget::Direct { key, display } => {
                            resolved.target = CallTarget::Direct(semantic_symbol(key.clone()));
                            resolved.label = replace_label_callee(&resolved.label, display);
                        }
                        SemanticCallTarget::Dynamic {
                            key,
                            display,
                            candidates,
                            open,
                            ..
                        } => {
                            resolved.target = CallTarget::Dynamic {
                                dispatch: semantic_symbol(key.clone()),
                                candidates: candidates
                                    .iter()
                                    .map(|candidate| DispatchCandidate {
                                        target: semantic_symbol(candidate.key.clone()),
                                        label: replace_label_callee(
                                            &resolved.label,
                                            &candidate.display,
                                        ),
                                    })
                                    .collect(),
                                resolution: if candidates.is_empty() {
                                    DispatchResolution::Unresolved
                                } else if *open {
                                    DispatchResolution::Partial
                                } else {
                                    DispatchResolution::Complete
                                },
                            };
                            resolved.label = replace_label_callee(&resolved.label, display);
                        }
                    }
                    let argument_types = semantic_call_argument_types(semantic_call);
                    resolved.label.typed = Some(annotate_rust_label(
                        &resolved.label.default,
                        &argument_types,
                    ));
                }
                resolved
            })
            .collect();

        let mut function_label = replace_label_callee(&template.label, &semantic_function.display);
        function_label.typed = Some(annotate_rust_label(
            &function_label.default,
            &semantic_function.parameter_types,
        ));
        analysis.functions.push(FunctionInfo {
            id: id.clone(),
            label: function_label,
            public: template.public,
            calls,
            span: template.span.clone(),
        });
        analysis.facts.extend(
            syntax
                .facts
                .iter()
                .filter(|fact| fact.subject == template.id)
                .cloned()
                .map(|mut fact| {
                    fact.subject = id.clone();
                    fact
                }),
        );
    }

    analysis
}

fn best_function_template<'a>(
    functions: &'a [FunctionInfo],
    body_span: &SourceSpan,
) -> Option<&'a FunctionInfo> {
    functions
        .iter()
        .filter(|function| {
            source_files_match(&function.span.file, &body_span.file)
                && span_contains(&function.span, body_span)
        })
        .min_by_key(|function| span_size(&function.span))
}

fn best_semantic_call(
    syntax_call: &CallSite,
    semantic_calls: &[SemanticCall],
    claimed: &HashSet<usize>,
) -> Option<usize> {
    let syntax_name = match &syntax_call.syntax {
        CallSyntax::Path(parts) => parts.last().map(String::as_str),
        CallSyntax::SelfMethod(method) | CallSyntax::Method { method, .. } => Some(method.as_str()),
    }?;

    semantic_calls
        .iter()
        .enumerate()
        .filter(|(index, call)| {
            !claimed.contains(index)
                && source_files_match(&syntax_call.span.file, &call.span.file)
                && spans_overlap(&syntax_call.span, &call.span)
        })
        .min_by_key(|(_, call)| {
            let definition_leaf = call
                .definition_name
                .rsplit("::")
                .next()
                .unwrap_or(&call.definition_name);
            let name_penalty = usize::from(definition_leaf != syntax_name) * 1_000_000;
            name_penalty + span_distance(&syntax_call.span, &call.span)
        })
        .map(|(index, _)| index)
}

fn semantic_symbol(name: String) -> SymbolId {
    SymbolId {
        language: LanguageId::new("rust"),
        module: Vec::new(),
        container: None,
        name,
    }
}

fn normalize_instance_key(name: &str) -> String {
    name.replace("::<", "<")
}

fn normalize_instance_display(name: &str, crate_name: &str) -> String {
    let compact = name
        .replace(&format!("{crate_name}::"), "")
        .replace("::<", "<");
    collapse_trait_qualification(&compact)
}

fn collapse_trait_qualification(name: &str) -> String {
    let Some(rest) = name.strip_prefix('<') else {
        return name.to_owned();
    };
    let Some((qualification, method)) = rest.rsplit_once(">::") else {
        return name.to_owned();
    };
    let Some((self_type, _trait_name)) = qualification.rsplit_once(" as ") else {
        return name.to_owned();
    };
    format!("{self_type}::{method}")
}

fn replace_label_callee(label: &CallLabel, callee: &str) -> CallLabel {
    CallLabel {
        default: replace_callee_text(&label.default, callee),
        typed: label
            .typed
            .as_ref()
            .map(|typed| replace_callee_text(typed, callee)),
    }
}

fn replace_callee_text(label: &str, callee: &str) -> String {
    let rendered = if let Some(arguments_start) = outer_call_arguments_start(label) {
        format!(
            "{}{}",
            semantic_callee(&label[..arguments_start], callee),
            &label[arguments_start..]
        )
    } else {
        semantic_callee(label, callee)
    };
    match closure_ordinal(callee) {
        Some(ordinal) if !label.contains("closure#") => {
            format!("{rendered} [closure#{ordinal}]")
        }
        Some(_) | None => rendered,
    }
}

fn closure_ordinal(callee: &str) -> Option<&str> {
    let rest = callee.split("{closure#").nth(1)?;
    rest.split('}').next()
}

fn semantic_callee(source: &str, semantic: &str) -> String {
    if semantic.starts_with("dyn ") {
        return semantic.rsplit_once("::").map_or_else(
            || semantic.to_owned(),
            |(dispatch, method)| format!("{}::{method}", simplify_type_paths(dispatch)),
        );
    }

    let generic_arguments = semantic
        .find('<')
        .zip(semantic.rfind('>'))
        .filter(|(start, end)| start < end)
        .map(|(start, end)| simplify_type_paths(&semantic[start..=end]));
    if let Some(generic_arguments) = generic_arguments {
        let source_base = source
            .find('<')
            .map_or(source, |generic_start| &source[..generic_start]);
        return format!("{source_base}{generic_arguments}");
    }

    let parts = semantic.split("::").collect::<Vec<_>>();
    if parts.len() >= 2
        && parts[parts.len() - 2]
            .chars()
            .next()
            .is_some_and(char::is_uppercase)
    {
        return format!("{}::{}", parts[parts.len() - 2], parts[parts.len() - 1]);
    }
    source.to_owned()
}

fn simplify_type_paths(value: &str) -> String {
    let mut output = String::with_capacity(value.len());
    let mut token = String::new();
    let flush = |token: &mut String, output: &mut String| {
        if token.is_empty() {
            return;
        }
        output.push_str(token.rsplit("::").next().unwrap_or(token));
        token.clear();
    };
    for character in value.chars() {
        if character.is_ascii_alphanumeric() || matches!(character, '_' | ':' | '\'') {
            token.push(character);
        } else {
            flush(&mut token, &mut output);
            output.push(character);
        }
    }
    flush(&mut token, &mut output);
    output
}

fn normalize_type_display(value: &str, crate_name: &str) -> String {
    simplify_type_paths(&value.replace(&format!("{crate_name}::"), ""))
}

fn semantic_call_argument_types(call: &SemanticCall) -> Vec<String> {
    let is_closure = matches!(
        &call.target,
        SemanticCallTarget::Direct { display, .. } if display.contains("{closure#")
    );
    if !is_closure {
        return call.argument_types.clone();
    }
    let Some(tuple) = call.argument_types.last() else {
        return Vec::new();
    };
    let Some(tuple) = tuple
        .strip_prefix('(')
        .and_then(|tuple| tuple.strip_suffix(')'))
    else {
        return call.argument_types.clone();
    };
    split_rust_arguments(tuple)
        .into_iter()
        .filter(|argument| !argument.is_empty())
        .map(ToOwned::to_owned)
        .collect()
}

fn annotate_rust_label(label: &str, semantic_types: &[String]) -> String {
    let Some(arguments_start) = outer_call_arguments_start(label) else {
        return label.to_owned();
    };
    let Some(arguments_end) = matching_parenthesis(label, arguments_start) else {
        return label.to_owned();
    };
    let arguments = split_rust_arguments(&label[arguments_start + 1..arguments_end]);
    if arguments.is_empty() || semantic_types.is_empty() {
        return label.to_owned();
    }
    let types = if semantic_types.len() >= arguments.len() {
        &semantic_types[semantic_types.len() - arguments.len()..]
    } else {
        semantic_types
    };
    let leading_untyped = arguments.len().saturating_sub(types.len());
    let annotated = arguments
        .iter()
        .enumerate()
        .map(|(index, argument)| {
            if index < leading_untyped {
                argument.to_string()
            } else {
                format!("{}: {}", argument, types[index - leading_untyped])
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "{}({annotated}){}",
        &label[..arguments_start],
        &label[arguments_end + 1..]
    )
}

fn matching_parenthesis(label: &str, start: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    for (offset, character) in label[start..].char_indices() {
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
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(start + offset);
                }
            }
            _ => {}
        }
    }
    None
}

fn split_rust_arguments(arguments: &str) -> Vec<&str> {
    if arguments.trim().is_empty() {
        return Vec::new();
    }
    let mut result = Vec::new();
    let mut start = 0usize;
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
            '"' => in_string = true,
            '(' | '[' | '{' | '<' => delimiters.push(character),
            ')' | ']' | '}' | '>' => {
                delimiters.pop();
            }
            ',' if delimiters.is_empty() => {
                result.push(arguments[start..index].trim());
                start = index + character.len_utf8();
            }
            _ => {}
        }
    }
    result.push(arguments[start..].trim());
    result
}

fn outer_call_arguments_start(label: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (index, character) in label.char_indices().rev() {
        match character {
            ')' => depth += 1,
            '(' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(index);
                }
            }
            _ => {}
        }
    }
    None
}

fn rustc_source_span(span: rustc_public::ty::Span) -> SourceSpan {
    let lines = span.get_lines();
    let file = PathBuf::from(span.get_filename());
    let file = if file.is_absolute() {
        file
    } else {
        env::current_dir().map_or(file.clone(), |directory| directory.join(file))
    };
    SourceSpan {
        file,
        start_line: lines.start_line,
        start_column: lines.start_col.saturating_sub(1),
        start_byte: None,
        end_line: lines.end_line.max(lines.start_line),
        end_column: lines.end_col.saturating_sub(1),
        end_byte: None,
    }
}

fn source_files_match(left: &Path, right: &Path) -> bool {
    left == right
        || left
            .canonicalize()
            .ok()
            .zip(right.canonicalize().ok())
            .is_some_and(|(left, right)| left == right)
}

fn span_contains(outer: &SourceSpan, inner: &SourceSpan) -> bool {
    position_le(
        outer.start_line,
        outer.start_column,
        inner.start_line,
        inner.start_column,
    ) && position_le(
        inner.end_line,
        inner.end_column,
        outer.end_line,
        outer.end_column,
    )
}

fn spans_overlap(left: &SourceSpan, right: &SourceSpan) -> bool {
    position_le(
        left.start_line,
        left.start_column,
        right.end_line,
        right.end_column,
    ) && position_le(
        right.start_line,
        right.start_column,
        left.end_line,
        left.end_column,
    )
}

fn position_le(
    left_line: usize,
    left_column: usize,
    right_line: usize,
    right_column: usize,
) -> bool {
    (left_line, left_column) <= (right_line, right_column)
}

fn span_size(span: &SourceSpan) -> usize {
    (span.end_line.saturating_sub(span.start_line) * 10_000)
        + span.end_column.saturating_sub(span.start_column)
}

fn span_distance(left: &SourceSpan, right: &SourceSpan) -> usize {
    left.start_line.abs_diff(right.start_line) * 10_000
        + left.start_column.abs_diff(right.start_column)
}

impl LanguageFrontend for RustSourceExtractor {
    fn language(&self) -> LanguageId {
        LanguageId::new("rust")
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["rs"]
    }

    fn analyze_file(
        &self,
        context: &FileContext<'_>,
        source: &str,
    ) -> FrontendResult<FileAnalysis> {
        let syntax = syn::parse_file(source)?;
        let mut analysis = FileAnalysis::default();
        analyze_items(context.path, context.module, &syntax.items, &mut analysis);
        Ok(analysis)
    }
}

fn analyze_items(file: &Path, module: &[String], items: &[Item], analysis: &mut FileAnalysis) {
    for item in items {
        match item {
            Item::Fn(function) => {
                let function_info = function_from_item(file, module, None, function);
                let owner = function_info.id.clone();
                add_signature_facts(file, &function_info, &function.sig, analysis);
                analysis.functions.push(function_info);
                add_closure_functions(file, module, &owner, &function.block, analysis);
            }
            Item::Impl(item_impl) => analyze_impl(file, module, item_impl, analysis),
            Item::Trait(item_trait) => analyze_trait(file, module, item_trait, analysis),
            Item::Mod(item_mod) => {
                if let Some((_, nested)) = &item_mod.content {
                    let mut nested_module = module.to_vec();
                    nested_module.push(item_mod.ident.to_string());
                    analyze_items(file, &nested_module, nested, analysis);
                }
            }
            _ => {}
        }
    }
}

fn function_from_item(
    file: &Path,
    module: &[String],
    container: Option<String>,
    function: &ItemFn,
) -> FunctionInfo {
    function_from_parts(
        file,
        module,
        container,
        &function.sig,
        &function.block,
        is_public(&function.vis),
        function.span(),
    )
}

fn analyze_impl(file: &Path, module: &[String], item_impl: &ItemImpl, analysis: &mut FileAnalysis) {
    let self_ty = compact_tokens(&item_impl.self_ty);
    let trait_name = item_impl
        .trait_
        .as_ref()
        .map(|(_, path, _)| compact_tokens(path));
    let container = trait_name
        .as_ref()
        .map(|trait_name| format!("{self_ty} as {trait_name}"))
        .unwrap_or_else(|| self_ty.clone());

    for item in &item_impl.items {
        let ImplItem::Fn(method) = item else {
            continue;
        };
        let function = function_from_parts(
            file,
            module,
            Some(container.clone()),
            &method.sig,
            &method.block,
            is_public(&method.vis) || trait_name.is_some(),
            method.span(),
        );
        let owner = function.id.clone();

        add_signature_facts(file, &function, &method.sig, analysis);
        if let Some(trait_name) = &trait_name {
            analysis.facts.push(LanguageFact {
                subject: function.id.clone(),
                namespace: LanguageId::new("rust"),
                kind: "impl-trait".to_owned(),
                key: trait_name.clone(),
                value: self_ty.clone(),
                span: function.span.clone(),
            });
        }
        analysis.functions.push(function);
        add_closure_functions(file, module, &owner, &method.block, analysis);
    }
}

fn analyze_trait(
    file: &Path,
    module: &[String],
    item_trait: &ItemTrait,
    analysis: &mut FileAnalysis,
) {
    let trait_name = item_trait.ident.to_string();
    for item in &item_trait.items {
        let TraitItem::Fn(method) = item else {
            continue;
        };
        let Some(block) = &method.default else {
            continue;
        };
        let function = function_from_parts(
            file,
            module,
            Some(trait_name.clone()),
            &method.sig,
            block,
            is_public(&item_trait.vis),
            method.span(),
        );
        let owner = function.id.clone();
        add_signature_facts(file, &function, &method.sig, analysis);
        analysis.functions.push(function);
        add_closure_functions(file, module, &owner, block, analysis);
    }
}

fn add_closure_functions(
    file: &Path,
    module: &[String],
    owner: &SymbolId,
    block: &syn::Block,
    analysis: &mut FileAnalysis,
) {
    let mut extractor = ClosureExtractor {
        file,
        module,
        owner,
        next_ordinal: 0,
        functions: Vec::new(),
    };
    extractor.visit_block(block);
    analysis.functions.extend(extractor.functions);
}

struct ClosureExtractor<'a> {
    file: &'a Path,
    module: &'a [String],
    owner: &'a SymbolId,
    next_ordinal: usize,
    functions: Vec<FunctionInfo>,
}

impl<'ast> Visit<'ast> for ClosureExtractor<'_> {
    fn visit_expr_closure(&mut self, node: &'ast ExprClosure) {
        let ordinal = self.next_ordinal;
        self.next_ordinal += 1;
        let closure_name = format!("{{closure#{ordinal}}}");
        let id = SymbolId {
            language: LanguageId::new("rust"),
            module: self.module.to_vec(),
            container: Some(self.owner.qualified_parts().join("::")),
            name: closure_name.clone(),
        };
        let mut calls = CallCollector {
            file: self.file,
            calls: Vec::new(),
        };
        calls.visit_expr(&node.body);
        let parameters = node.inputs.iter().map(pattern_name).collect::<Vec<_>>();
        let typed_parameters = node
            .inputs
            .iter()
            .map(|parameter| match parameter {
                Pat::Type(typed) => format!(
                    "{}: {}",
                    pattern_name(&typed.pat),
                    compact_tokens(&typed.ty)
                ),
                parameter => pattern_name(parameter),
            })
            .collect::<Vec<_>>();
        self.functions.push(FunctionInfo {
            id,
            label: CallLabel::with_types(
                format!("{closure_name}({})", parameters.join(", ")),
                format!("{closure_name}({})", typed_parameters.join(", ")),
            ),
            public: false,
            calls: calls.calls,
            span: source_span(self.file, node.span()),
        });
        visit::visit_expr_closure(self, node);
    }

    fn visit_item_fn(&mut self, _node: &'ast ItemFn) {}
}

fn function_from_parts(
    file: &Path,
    module: &[String],
    container: Option<String>,
    signature: &Signature,
    block: &syn::Block,
    public: bool,
    span: Span,
) -> FunctionInfo {
    let id = SymbolId {
        language: LanguageId::new("rust"),
        module: module.to_vec(),
        container,
        name: signature.ident.to_string(),
    };
    let mut collector = CallCollector {
        file,
        calls: Vec::new(),
    };
    collector.visit_block(block);

    FunctionInfo {
        label: function_label(&id, signature),
        id,
        public,
        calls: collector.calls,
        span: source_span(file, span),
    }
}

fn add_signature_facts(
    file: &Path,
    function: &FunctionInfo,
    signature: &Signature,
    analysis: &mut FileAnalysis,
) {
    for input in &signature.inputs {
        match input {
            FnArg::Receiver(receiver) => {
                let mode = match (&receiver.reference, receiver.mutability.is_some()) {
                    (Some(_), true) => "&mut self",
                    (Some(_), false) => "&self",
                    (None, true) => "mut self",
                    (None, false) => "self",
                };
                analysis.facts.push(LanguageFact {
                    subject: function.id.clone(),
                    namespace: LanguageId::new("rust"),
                    kind: "receiver".to_owned(),
                    key: "self".to_owned(),
                    value: mode.to_owned(),
                    span: source_span(file, receiver.span()),
                });
            }
            FnArg::Typed(argument) => {
                analysis.facts.push(LanguageFact {
                    subject: function.id.clone(),
                    namespace: LanguageId::new("rust"),
                    kind: "parameter".to_owned(),
                    key: compact_tokens(&argument.pat),
                    value: compact_tokens(&argument.ty),
                    span: source_span(file, argument.span()),
                });
            }
        }
    }

    if signature.asyncness.is_some() {
        push_modifier_fact(function, "async", file, signature.span(), analysis);
    }
    if signature.unsafety.is_some() {
        push_modifier_fact(function, "unsafe", file, signature.span(), analysis);
    }
    if signature.constness.is_some() {
        push_modifier_fact(function, "const", file, signature.span(), analysis);
    }
    if let ReturnType::Type(_, ty) = &signature.output {
        analysis.facts.push(LanguageFact {
            subject: function.id.clone(),
            namespace: LanguageId::new("rust"),
            kind: "return-type".to_owned(),
            key: "return".to_owned(),
            value: compact_tokens(ty),
            span: source_span(file, ty.span()),
        });
    }
}

fn push_modifier_fact(
    function: &FunctionInfo,
    modifier: &str,
    file: &Path,
    span: Span,
    analysis: &mut FileAnalysis,
) {
    analysis.facts.push(LanguageFact {
        subject: function.id.clone(),
        namespace: LanguageId::new("rust"),
        kind: "modifier".to_owned(),
        key: modifier.to_owned(),
        value: "true".to_owned(),
        span: source_span(file, span),
    });
}

fn parameter_names(signature: &Signature) -> String {
    signature
        .inputs
        .iter()
        .map(|input| match input {
            FnArg::Receiver(receiver) => match (&receiver.reference, receiver.mutability.is_some())
            {
                (Some(_), true) => "&mut self".to_owned(),
                (Some(_), false) => "&self".to_owned(),
                (None, true) => "mut self".to_owned(),
                (None, false) => "self".to_owned(),
            },
            FnArg::Typed(argument) => pattern_name(&argument.pat),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn function_label(id: &SymbolId, signature: &Signature) -> CallLabel {
    let generic_names = signature
        .generics
        .params
        .iter()
        .map(|parameter| match parameter {
            syn::GenericParam::Lifetime(lifetime) => lifetime.lifetime.to_string(),
            syn::GenericParam::Type(parameter) => parameter.ident.to_string(),
            syn::GenericParam::Const(parameter) => parameter.ident.to_string(),
        })
        .collect::<Vec<_>>();
    let generics = if generic_names.is_empty() {
        String::new()
    } else {
        format!("<{}>", generic_names.join(", "))
    };
    let default = format!(
        "{}{generics}({})",
        id.short_name(),
        parameter_names(signature)
    );
    let typed = format!(
        "{}{generics}({})",
        id.short_name(),
        typed_parameters(signature)
    );
    CallLabel::with_types(default, typed)
}

fn typed_parameters(signature: &Signature) -> String {
    signature
        .inputs
        .iter()
        .map(|input| match input {
            FnArg::Receiver(_) => pattern_name_from_argument(input),
            FnArg::Typed(argument) => {
                format!(
                    "{}: {}",
                    pattern_name(&argument.pat),
                    compact_tokens(&argument.ty)
                )
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn pattern_name_from_argument(argument: &FnArg) -> String {
    match argument {
        FnArg::Receiver(receiver) => match (&receiver.reference, receiver.mutability.is_some()) {
            (Some(_), true) => "&mut self".to_owned(),
            (Some(_), false) => "&self".to_owned(),
            (None, true) => "mut self".to_owned(),
            (None, false) => "self".to_owned(),
        },
        FnArg::Typed(argument) => pattern_name(&argument.pat),
    }
}

fn pattern_name(pattern: &Pat) -> String {
    match pattern {
        Pat::Ident(ident) => ident.ident.to_string(),
        Pat::Reference(reference) => pattern_name(&reference.pat),
        Pat::Wild(_) => "_".to_owned(),
        _ => compact_tokens(pattern),
    }
}

fn is_public(visibility: &Visibility) -> bool {
    matches!(visibility, Visibility::Public(_))
}

fn compact_tokens(tokens: &impl ToTokens) -> String {
    tokens.to_token_stream().to_string().replace(' ', "")
}

fn source_span(file: &Path, span: Span) -> SourceSpan {
    let start = span.start();
    let end = span.end();
    SourceSpan {
        file: file.to_path_buf(),
        start_line: start.line,
        start_column: start.column,
        start_byte: None,
        end_line: end.line.max(start.line),
        end_column: end.column,
        end_byte: None,
    }
}

struct CallCollector<'a> {
    file: &'a Path,
    calls: Vec<CallSite>,
}

impl<'ast> Visit<'ast> for CallCollector<'_> {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if let Some(parts) = callable_path(&node.func) {
            self.calls.push(CallSite {
                syntax: CallSyntax::Path(parts),
                target: CallTarget::Unresolved,
                label: CallLabel::new(call_expression_label(node)),
                span: source_span(self.file, node.span()),
            });
        }
        visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        let method = node.method.to_string();
        let syntax = if is_self_expr(&node.receiver) {
            CallSyntax::SelfMethod(method)
        } else {
            CallSyntax::Method {
                receiver: receiver_name(&node.receiver),
                method,
            }
        };
        self.calls.push(CallSite {
            syntax,
            target: CallTarget::Unresolved,
            label: CallLabel::new(method_call_label(node)),
            span: source_span(self.file, node.span()),
        });
        visit::visit_expr_method_call(self, node);
    }

    // Nested closures and local functions own their calls; do not attribute them
    // to the enclosing function.
    fn visit_expr_closure(&mut self, _node: &'ast ExprClosure) {}

    fn visit_item_fn(&mut self, _node: &'ast ItemFn) {}
}

fn call_expression_label(node: &ExprCall) -> String {
    let function = compact_tokens(&node.func).replace("::<", "<");
    let arguments = node.args.iter().map(compact_tokens).collect::<Vec<_>>();
    format!("{function}({})", arguments.join(", "))
}

fn method_call_label(node: &ExprMethodCall) -> String {
    let receiver = compact_tokens(&node.receiver);
    let generics = node
        .turbofish
        .as_ref()
        .map(compact_tokens)
        .unwrap_or_default()
        .replace("::<", "<");
    let arguments = node.args.iter().map(compact_tokens).collect::<Vec<_>>();
    format!(
        "{receiver}.{}{generics}({})",
        node.method,
        arguments.join(", ")
    )
}

fn callable_path(expression: &Expr) -> Option<Vec<String>> {
    match expression {
        Expr::Path(path) => Some(
            path.path
                .segments
                .iter()
                .map(|segment| segment.ident.to_string())
                .collect(),
        ),
        Expr::Group(group) => callable_path(&group.expr),
        Expr::Paren(paren) => callable_path(&paren.expr),
        _ => None,
    }
}

fn is_self_expr(expression: &Expr) -> bool {
    matches!(expression, Expr::Path(path) if path.path.is_ident("self"))
}

fn receiver_name(expression: &Expr) -> String {
    match expression {
        Expr::Path(path) => path
            .path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect::<Vec<_>>()
            .join("::"),
        _ => "<expr>".to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;

    use super::*;

    #[test]
    fn extracts_functions_methods_calls_and_signature_facts() {
        let source = r#"
            pub trait Store {
                fn save(&mut self, value: Item) {
                    validate(value);
                }
            }

            struct Database;

            impl Store for Database {
                fn save(&mut self, value: Item) {
                    self.prepare();
                    persist(value);
                }
            }
        "#;
        let frontend = RustSourceExtractor;
        let analysis = frontend
            .analyze_file(
                &FileContext {
                    path: Path::new("src/lib.rs"),
                    module: &[],
                },
                source,
            )
            .unwrap();

        assert_eq!(analysis.functions.len(), 2);
        let implementation = analysis
            .functions
            .iter()
            .find(|function| function.id.container.as_deref() == Some("Database as Store"))
            .unwrap();
        assert_eq!(implementation.calls.len(), 2);
        assert!(analysis.facts.iter().any(|fact| {
            fact.subject == implementation.id
                && fact.kind == "receiver"
                && fact.value == "&mut self"
        }));
        assert!(analysis.facts.iter().any(|fact| {
            fact.subject == implementation.id && fact.kind == "impl-trait" && fact.key == "Store"
        }));
    }

    #[test]
    fn rustc_public_can_analyze_a_compilable_file() {
        let directory =
            std::env::temp_dir().join(format!("diffkit-rustc-public-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("input.rs");
        fs::write(&path, "pub fn entry() { helper(); } fn helper() {}\n").unwrap();

        let analysis = analyze_semantic_file(&path).unwrap();

        assert!(
            analysis
                .functions
                .iter()
                .any(|function| function.id.name.ends_with("::entry"))
        );
        assert!(
            analysis
                .functions
                .iter()
                .any(|function| function.id.name.ends_with("::helper"))
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn rustc_public_resolves_generic_trait_dispatch() {
        let directory = std::env::temp_dir().join(format!(
            "diffkit-rustc-public-generics-{}",
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("input.rs");
        fs::write(
            &path,
            r#"
                #[derive(Clone, Copy)]
                pub struct Order;
                trait Store { fn save(&self, order: Order); }
                struct Postgres;
                impl Store for Postgres {
                    fn save(&self, order: Order) {
                        sql::begin();
                        sql::insert(order);
                        sql::commit();
                    }
                }
                struct S3;
                impl Store for S3 {
                    fn save(&self, order: Order) {
                        aws::sign(order);
                        aws::put_object(order);
                    }
                }
                fn run<S: Store>(storage: &S, order: Order) {
                    validate(order);
                    storage.save(order);
                    finalize(order);
                }
                pub fn entry(order: Order) {
                    run(&Postgres, order);
                    run(&S3, order);
                }
                fn validate(_: Order) {}
                fn finalize(_: Order) {}
                mod sql {
                    use super::Order;
                    pub fn begin() {}
                    pub fn insert(_: Order) {}
                    pub fn commit() {}
                }
                mod aws {
                    use super::Order;
                    pub fn sign(_: Order) {}
                    pub fn put_object(_: Order) {}
                }
            "#,
        )
        .unwrap();

        let analysis = analyze_semantic_file(&path).unwrap();
        let labels = analysis
            .functions
            .iter()
            .map(|function| {
                (
                    function.label.default.clone(),
                    function
                        .calls
                        .iter()
                        .map(|call| call.label.default.clone())
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>();
        assert!(labels.iter().any(|(label, calls)| {
            label == "run<Postgres>(storage, order)"
                && calls.iter().any(|call| call == "Postgres::save(order)")
        }));
        assert!(labels.iter().any(|(label, calls)| {
            label == "run<S3>(storage, order)" && calls.iter().any(|call| call == "S3::save(order)")
        }));
        fs::remove_dir_all(directory).unwrap();
    }
}
