use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::env;
use std::fs;
use std::io::Read;
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
    AssocContainer, Binder, ExistentialTraitRef, GenericArgKind, GenericArgs, RigidTy, TraitRef,
    Ty, TyKind, VtblEntry,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::visit_mut::{self, VisitMut};
use syn::{
    Expr, ExprCall, ExprClosure, ExprMethodCall, FnArg, ImplItem, Item, ItemFn, ItemImpl,
    ItemTrait, Pat, ReturnType, Signature, TraitItem, Visibility,
};

use super::{FileContext, FrontendResult, LanguageBackend, ProjectContext};
use crate::model::{
    CallLabel, CallSite, CallSiteId, CallSyntax, CallTarget, DispatchCandidate, DispatchEvidence,
    DispatchResolution, FileAnalysis, FunctionInfo, LanguageFact, LanguageId, SourceSpan, SymbolId,
    UnresolvedReason,
};

#[derive(Default)]
pub struct RustBackend;

pub static RUST_BACKEND: RustBackend = RustBackend;

static RUSTC_DRIVER_LOCK: Mutex<()> = Mutex::new(());
static TEMP_SOURCE_SEQUENCE: AtomicU64 = AtomicU64::new(0);
const RUSTC_CAPTURE_DIRECTORY: &str = "DIFFKIT_RUSTC_CAPTURE_DIRECTORY";
const RUSTC_ANALYSIS_ROOT: &str = "DIFFKIT_RUSTC_ANALYSIS_ROOT";
const SNAPSHOT_FINGERPRINT_FILE: &str = ".diffkit-snapshot-key";
const RUST_SEMANTIC_CACHE_SCHEMA: u32 = 4;

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
    let syntax = RustBackend.analyze_file(&FileContext { path, module: &[] }, &source)?;
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
pub(crate) fn analyze_semantic_project(
    project_root: &Path,
    wrapper_executable: &Path,
    entries: &[String],
    session: &RustProjectSession,
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
        return capture_semantic_project(&root, wrapper_executable, session);
    }

    let seeded = SeededRustProject::create(&root)?;
    seed_project_entries(seeded.root(), &generic_entries)?;
    let mut analysis = capture_semantic_project(seeded.root(), wrapper_executable, session)?;
    remap_analysis_root(&mut analysis, seeded.root(), &root);
    remove_seed_functions(&mut analysis);
    Ok(analysis)
}

fn capture_semantic_project(
    root: &Path,
    wrapper_executable: &Path,
    session: &RustProjectSession,
) -> FrontendResult<FileAnalysis> {
    let started = std::time::Instant::now();
    let fingerprint_started = std::time::Instant::now();
    let fingerprint = session
        .cache_path()
        .map(|_| semantic_cache_fingerprint(root))
        .transpose()?;
    let fingerprint_elapsed = fingerprint_started.elapsed();
    // `cargo clean --workspace` and the following check form one operation.
    // Cargo's own target lock covers each command separately, so another
    // DiffKit process could otherwise clean between them and then observe a
    // fresh build without receiving any semantic wrapper output.
    let cache_lock = fs::OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        .truncate(false)
        .open(session.target().join(".diffkit.lock"))?;
    cache_lock.lock()?;
    if let (Some(cache_path), Some(fingerprint)) = (session.cache_path(), fingerprint.as_deref())
        && let Some(analysis) = read_analysis_cache(cache_path, fingerprint, root)
    {
        session.report_cache(true, fingerprint, fingerprint_elapsed, started.elapsed());
        return Ok(analysis);
    }
    let capture = RustProjectCapture::create()?;
    let wrapper = wrapper_executable.canonicalize()?;
    let clean = Command::new("cargo")
        .args(["clean", "--workspace", "--quiet"])
        .current_dir(root)
        .env("CARGO_TARGET_DIR", session.target())
        .output()?;
    if !clean.status.success() {
        let diagnostic = String::from_utf8_lossy(&clean.stderr).trim().to_owned();
        return Err(std::io::Error::other(if diagnostic.is_empty() {
            format!("Cargo cache preparation exited with {}", clean.status)
        } else {
            diagnostic
        })
        .into());
    }
    let output = Command::new("cargo")
        .args([
            "check",
            "--workspace",
            "--all-targets",
            "--all-features",
            "--quiet",
        ])
        .current_dir(root)
        .env("RUSTC_WORKSPACE_WRAPPER", &wrapper)
        .env(RUSTC_CAPTURE_DIRECTORY, capture.results())
        .env(RUSTC_ANALYSIS_ROOT, root)
        .env("CARGO_TARGET_DIR", session.target())
        // Before and after snapshots have different source roots. Reusing
        // rustc incremental state across those roots can mix stale module
        // paths even though Cargo correctly reruns the workspace target.
        .env("CARGO_INCREMENTAL", "0")
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
    respecialize_merged_semantic_program(&mut semantic);

    let syntax = analyze_project_sources(root)?;
    let analysis = deduplicate_analysis(merge_semantic_program(syntax, semantic));
    if let (Some(cache_path), Some(fingerprint)) = (session.cache_path(), fingerprint) {
        let cache = CachedRustAnalysis {
            schema: RUST_SEMANTIC_CACHE_SCHEMA,
            fingerprint,
            root: root.to_path_buf(),
            analysis,
        };
        let _ = write_analysis_cache(cache_path, &cache);
        session.report_cache(
            false,
            &cache.fingerprint,
            fingerprint_elapsed,
            started.elapsed(),
        );
        return Ok(cache.analysis);
    }
    Ok(analysis)
}

fn semantic_cache_fingerprint(root: &Path) -> std::io::Result<String> {
    let mut hasher = Sha256::new();
    hash_cache_bytes(&mut hasher, &RUST_SEMANTIC_CACHE_SCHEMA.to_le_bytes());
    hash_cache_bytes(&mut hasher, &analyzer_identity());
    hash_command_identity(&mut hasher, root, "rustc", &["-vV"])?;
    hash_command_identity(&mut hasher, root, "cargo", &["-V"])?;

    let mut environment = env::vars_os()
        .filter(|(key, _)| rust_build_environment_key(key))
        .collect::<Vec<_>>();
    environment.sort_by(|left, right| {
        left.0
            .as_encoded_bytes()
            .cmp(right.0.as_encoded_bytes())
            .then_with(|| left.1.as_encoded_bytes().cmp(right.1.as_encoded_bytes()))
    });
    for (key, value) in environment {
        hash_cache_bytes(&mut hasher, key.as_encoded_bytes());
        hash_cache_bytes(&mut hasher, value.as_encoded_bytes());
    }
    if let Ok(snapshot_key) = fs::read(root.join(SNAPSHOT_FINGERPRINT_FILE)) {
        hash_cache_bytes(&mut hasher, b"git-snapshot");
        hash_cache_bytes(&mut hasher, &snapshot_key);
    } else {
        hash_project_inputs(root, root, &mut hasher)?;
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn rust_build_environment_key(key: &std::ffi::OsStr) -> bool {
    let Some(key) = key.to_str() else {
        return true;
    };
    matches!(
        key,
        "PATH"
            | "HOME"
            | "RUSTFLAGS"
            | "RUSTDOCFLAGS"
            | "RUSTC"
            | "RUSTUP_HOME"
            | "RUSTUP_TOOLCHAIN"
            | "CARGO_HOME"
            | "CARGO_BUILD_TARGET"
            | "CARGO_ENCODED_RUSTFLAGS"
            | "CC"
            | "CXX"
            | "AR"
            | "CFLAGS"
            | "CXXFLAGS"
            | "LDFLAGS"
            | "MACOSX_DEPLOYMENT_TARGET"
            | "SDKROOT"
            | "PKG_CONFIG_PATH"
    ) || [
        "CARGO_PROFILE_",
        "CARGO_TARGET_",
        "RUSTC_",
        "CC_",
        "CXX_",
        "AR_",
        "CFLAGS_",
        "CXXFLAGS_",
        "PKG_CONFIG_",
    ]
    .iter()
    .any(|prefix| key.starts_with(prefix))
}

fn analyzer_identity() -> Vec<u8> {
    // Engine and renderer rebuilds do not change captured rustc facts. Cache
    // compatibility is owned explicitly by the semantic schema so a local
    // binary timestamp cannot invalidate every analyzed project.
    format!(
        "{}:semantic-schema-{RUST_SEMANTIC_CACHE_SCHEMA}",
        env!("CARGO_PKG_VERSION")
    )
    .into_bytes()
}

fn hash_command_identity(
    hasher: &mut Sha256,
    root: &Path,
    program: &str,
    arguments: &[&str],
) -> std::io::Result<()> {
    let output = Command::new(program)
        .args(arguments)
        .current_dir(root)
        .output()?;
    hash_cache_bytes(hasher, program.as_bytes());
    hash_cache_bytes(hasher, &output.stdout);
    hash_cache_bytes(hasher, &output.stderr);
    hash_cache_bytes(hasher, &output.status.code().unwrap_or(-1).to_le_bytes());
    Ok(())
}

fn hash_project_inputs(root: &Path, directory: &Path, hasher: &mut Sha256) -> std::io::Result<()> {
    let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(std::fs::DirEntry::path);
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            if !is_generated_directory(&path) {
                hash_project_inputs(root, &path, hasher)?;
            }
            continue;
        }

        let relative = path.strip_prefix(root).unwrap_or(&path);
        if file_type.is_file() {
            hash_cache_bytes(hasher, b"file");
            hash_cache_bytes(hasher, relative.as_os_str().as_encoded_bytes());
            hash_file_contents(&path, hasher)?;
        } else if file_type.is_symlink() {
            hash_cache_bytes(hasher, b"symlink");
            hash_cache_bytes(hasher, relative.as_os_str().as_encoded_bytes());
            let target = fs::read_link(&path)?;
            hash_cache_bytes(hasher, target.as_os_str().as_encoded_bytes());
            if let Ok(resolved) = path.canonicalize()
                && resolved.is_file()
            {
                hash_file_contents(&resolved, hasher)?;
            }
        }
    }
    Ok(())
}

fn is_generated_directory(path: &Path) -> bool {
    matches!(
        path.file_name().and_then(|name| name.to_str()),
        Some(".git" | "target" | "node_modules" | ".zig-cache" | "zig-out" | "_build")
    )
}

fn hash_file_contents(path: &Path, hasher: &mut Sha256) -> std::io::Result<()> {
    let mut file = fs::File::open(path)?;
    let length = file.metadata()?.len();
    hasher.update(length.to_le_bytes());
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(())
}

fn hash_cache_bytes(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

fn read_analysis_cache(path: PathBuf, fingerprint: &str, root: &Path) -> Option<FileAnalysis> {
    let mut cached = serde_json::from_slice::<CachedRustAnalysis>(&fs::read(path).ok()?).ok()?;
    if cached.schema != RUST_SEMANTIC_CACHE_SCHEMA || cached.fingerprint != fingerprint {
        return None;
    }
    remap_analysis_root(&mut cached.analysis, &cached.root, root);
    Some(cached.analysis)
}

fn write_analysis_cache(path: PathBuf, cached: &CachedRustAnalysis) -> std::io::Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let sequence = TEMP_SOURCE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let temporary = path.with_extension(format!("json.tmp-{}-{sequence}", std::process::id()));
    fs::write(&temporary, serde_json::to_vec(cached)?)?;
    if let Err(error) = fs::rename(&temporary, &path) {
        if path.is_file() {
            fs::remove_file(&path)?;
            fs::rename(&temporary, &path)?;
        } else {
            let _ = fs::remove_file(temporary);
            return Err(error);
        }
    }
    Ok(())
}

struct RustProjectCapture {
    directory: PathBuf,
}

impl RustProjectCapture {
    fn create() -> std::io::Result<Self> {
        let sequence = TEMP_SOURCE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = env::temp_dir().join(format!(
            "diffkit-rust-capture-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory)?;
        fs::create_dir(directory.join("results"))?;
        Ok(Self { directory })
    }

    fn results(&self) -> PathBuf {
        self.directory.join("results")
    }
}

impl Drop for RustProjectCapture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

/// Owns one Cargo target directory for one semantic-analysis endpoint.
///
/// A before/after comparison must not share a persistent target directory:
/// Cargo identifies workspace packages independently of the temporary Git
/// snapshot path, so a binary from one endpoint can otherwise be checked
/// against stale library metadata from the other endpoint.
pub(crate) struct RustProjectSession {
    target: PathBuf,
    cleanup: Option<PathBuf>,
    endpoint: Option<String>,
    verbose: bool,
}

impl RustProjectSession {
    pub(crate) fn create() -> std::io::Result<Self> {
        let sequence = TEMP_SOURCE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = env::temp_dir().join(format!(
            "diffkit-rust-session-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory)?;
        Ok(Self {
            target: directory.join("target"),
            cleanup: Some(directory),
            endpoint: None,
            verbose: false,
        })
    }

    pub(crate) fn create_cached(
        project_root: &Path,
        endpoint: &str,
        verbose: bool,
    ) -> std::io::Result<Self> {
        let mut components = Path::new(endpoint).components();
        if !matches!(components.next(), Some(std::path::Component::Normal(_)))
            || components.next().is_some()
        {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "Rust semantic cache endpoint must be one path component",
            ));
        }
        let target = project_root
            .join("target")
            .join("diffkit-semantic")
            .join(endpoint);
        fs::create_dir_all(&target)?;
        Ok(Self {
            target,
            cleanup: None,
            endpoint: Some(endpoint.to_owned()),
            verbose,
        })
    }

    fn target(&self) -> &Path {
        &self.target
    }

    fn cache_path(&self) -> Option<PathBuf> {
        self.cleanup
            .is_none()
            .then(|| self.target.join(".diffkit").join("analysis-v2.json"))
    }

    fn report_cache(
        &self,
        hit: bool,
        fingerprint_key: &str,
        fingerprint: std::time::Duration,
        total: std::time::Duration,
    ) {
        if self.verbose {
            let status = if hit { "hit" } else { "miss" };
            eprintln!(
                "Rust semantic cache {status}: {} [{}] ({} ms; fingerprint {} ms)",
                self.endpoint.as_deref().unwrap_or("temporary"),
                &fingerprint_key[..fingerprint_key.len().min(12)],
                total.as_millis(),
                fingerprint.as_millis(),
            );
        }
    }
}

impl Drop for RustProjectSession {
    fn drop(&mut self) {
        if let Some(directory) = &self.cleanup {
            let _ = fs::remove_dir_all(directory);
        }
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
    analysis.source_files = std::mem::take(&mut analysis.source_files)
        .into_iter()
        .map(|mut file| {
            remap(&mut file);
            file
        })
        .collect();
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
        let mut analysis = RustBackend.analyze_file(
            &FileContext {
                path: &file,
                module: &module,
            },
            &source,
        )?;
        combined.functions.append(&mut analysis.functions);
        combined.facts.append(&mut analysis.facts);
        combined.source_files.append(&mut analysis.source_files);
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
        source_files: analysis.source_files,
        roots: analysis.roots,
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

#[derive(Debug, Deserialize, Serialize)]
struct CachedRustAnalysis {
    schema: u32,
    fingerprint: String,
    root: PathBuf,
    analysis: FileAnalysis,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct SemanticFunction {
    base_key: String,
    key: String,
    display: String,
    definition_name: String,
    body_span: SourceSpan,
    calls: Vec<SemanticCall>,
    constructor_spans: Vec<SourceSpan>,
    constructor_names: Vec<String>,
    parameter_types: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct SemanticCall {
    target: SemanticCallTarget,
    definition_name: String,
    span: SourceSpan,
    argument_types: Vec<String>,
    argument_flows: Vec<SemanticDynFlow>,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
struct SemanticDynFlow {
    concrete_types: Vec<String>,
    parameters: Vec<usize>,
    unresolved_reasons: BTreeSet<UnresolvedReason>,
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
        unresolved_reasons: BTreeSet<UnresolvedReason>,
        receiver_flow: SemanticDynFlow,
    },
    Indirect {
        signature: String,
    },
    Unresolved,
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
    unresolved_reasons: BTreeSet<UnresolvedReason>,
}

impl DynFlow {
    fn parameter(index: usize) -> Self {
        Self {
            concrete: Vec::new(),
            parameters: vec![index],
            unresolved_reasons: BTreeSet::new(),
        }
    }

    fn concrete(trait_ref: TraitRef) -> Self {
        Self {
            concrete: vec![trait_ref],
            parameters: Vec::new(),
            unresolved_reasons: BTreeSet::new(),
        }
    }

    fn unresolved(reason: UnresolvedReason) -> Self {
        Self {
            concrete: Vec::new(),
            parameters: Vec::new(),
            unresolved_reasons: [reason].into_iter().collect(),
        }
    }

    fn is_empty(&self) -> bool {
        self.concrete.is_empty() && self.parameters.is_empty() && self.unresolved_reasons.is_empty()
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
        for reason in &other.unresolved_reasons {
            changed |= self.unresolved_reasons.insert(reason.clone());
        }
        self.parameters.sort_unstable();
        changed
    }
}

#[derive(Clone, Debug, Default)]
struct ResolvedDynFlow {
    concrete: Vec<TraitRef>,
    unresolved_reasons: BTreeSet<UnresolvedReason>,
}

impl ResolvedDynFlow {
    fn merge(&mut self, other: &Self) {
        for candidate in &other.concrete {
            if !self.concrete.contains(candidate) {
                self.concrete.push(candidate.clone());
            }
        }
        self.unresolved_reasons
            .extend(other.unresolved_reasons.iter().cloned());
    }
}

#[derive(Clone)]
struct RawSemanticFunction {
    key: String,
    display: String,
    definition_name: String,
    body_span: SourceSpan,
    calls: Vec<RawSemanticCall>,
    constructor_spans: Vec<SourceSpan>,
    constructor_names: Vec<String>,
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
    Indirect {
        signature: String,
    },
    Unresolved,
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
                return_summaries
                    .entry(item.instance)
                    .or_default()
                    .unresolved_reasons
                    .insert(UnresolvedReason::AnalysisLimit);
            }
        }
    }

    let mut raw_functions = Vec::new();
    for item in &instance_bodies {
        let instance = item.instance;
        let body = &item.body;
        let instance_name = stable_instance_name(instance);
        let analysis = analyze_body_dyn_flows(body, &return_summaries, &local_instances);
        let mut calls = Vec::new();
        for (block_index, block) in body.blocks.iter().enumerate() {
            let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                continue;
            };
            let resolved_target = resolve_called_instance(body, func);
            let definition_name = resolved_target
                .map(|target| target.def.name())
                .unwrap_or_default();
            let call_flow = analysis
                .calls
                .get(block_index)
                .and_then(Option::as_ref)
                .cloned()
                .unwrap_or_default();
            let target = match resolved_target {
                Some(target) => {
                    let name = stable_instance_name(target);
                    match target.kind {
                        InstanceKind::Virtual { .. } => RawSemanticCallTarget::Dynamic {
                            dispatch: target,
                            key: normalize_instance_key(&name),
                            display: normalize_instance_display(&name, &crate_name),
                            receiver: call_flow.arguments.first().cloned().unwrap_or_else(|| {
                                DynFlow::unresolved(UnresolvedReason::AnalysisLimit)
                            }),
                        },
                        _ => RawSemanticCallTarget::Direct {
                            key: normalize_instance_key(&name),
                            display: normalize_instance_display(&name, &crate_name),
                        },
                    }
                }
                None => func
                    .ty(body.locals())
                    .ok()
                    .filter(|ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::FnPtr(_))))
                    .map(|ty| RawSemanticCallTarget::Indirect {
                        signature: normalize_type_display(&ty.to_string(), &crate_name),
                    })
                    .unwrap_or(RawSemanticCallTarget::Unresolved),
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
        let mut constructor_spans = body
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .filter_map(|statement| {
                let StatementKind::Assign(_, value) = &statement.kind else {
                    return None;
                };
                let ty = value.ty(body.locals()).ok()?;
                matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(..)))
                    .then(|| rustc_source_span(statement.span))
            })
            .collect::<Vec<_>>();
        constructor_spans.sort_by_key(|span| {
            (
                span.start_line,
                span.start_column,
                span.end_line,
                span.end_column,
            )
        });
        constructor_spans.dedup();
        let mut constructor_names = HashSet::new();
        for local in body.locals() {
            collect_adt_constructor_names(local.ty, &mut constructor_names);
        }
        let mut constructor_names = constructor_names.into_iter().collect::<Vec<_>>();
        constructor_names.sort();
        raw_functions.push(RawSemanticFunction {
            key: normalize_instance_key(&instance_name),
            display: normalize_instance_display(&instance_name, &crate_name),
            definition_name: instance.def.name().to_string(),
            body_span: rustc_source_span(body.span),
            calls,
            constructor_spans,
            constructor_names,
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
                let TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } = &block.terminator.kind
                else {
                    continue;
                };
                let Some(target) = resolve_called_instance(&body, func) else {
                    continue;
                };
                if !matches!(target.kind, InstanceKind::Virtual { .. })
                    && target.has_body()
                    && (target.def.krate().is_local
                        || instance_body_is_in_analysis_root(target)
                        || call_boundary_contains_dyn(&body, args, destination))
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
                    if candidate.has_body() && !visited.contains(&candidate) {
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

fn instance_body_is_in_analysis_root(instance: Instance) -> bool {
    let Some(root) = env::var_os(RUSTC_ANALYSIS_ROOT).map(PathBuf::from) else {
        return false;
    };
    let Some(body) = instance.body() else {
        return false;
    };
    let file = rustc_source_span(body.span).file;
    file.starts_with(&root)
        || file
            .canonicalize()
            .ok()
            .zip(root.canonicalize().ok())
            .is_some_and(|(file, root)| file.starts_with(root))
}

fn call_boundary_contains_dyn(body: &Body, arguments: &[Operand], destination: &Place) -> bool {
    arguments
        .iter()
        .filter_map(|argument| argument.ty(body.locals()).ok())
        .any(type_contains_dyn)
        || destination.ty(body.locals()).is_ok_and(type_contains_dyn)
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
            // `TraitRef` cannot represent the binder around a higher-ranked
            // principal such as `dyn for<'a> Fn(&'a T)`. Flattening it would
            // pass escaping bound variables to rustc's vtable query and panic.
            if !principal.bound_vars.is_empty() {
                continue;
            }
            let principal = principal.value;
            let trait_ref = TraitRef::new(principal.def_id, concrete_ty, &principal.generic_args);
            if !observed.contains(&trait_ref) {
                observed.push(trait_ref);
            }
        }
    }
}

fn dyn_coercion(source: Ty, target: Ty) -> Option<(Ty, Binder<ExistentialTraitRef>)> {
    let target_kind = target.kind();
    if let Some(principal) = target_kind.trait_principal() {
        // A trait upcast (`dyn Child` -> `dyn Parent`) does not reveal a
        // concrete implementation. Only thin-to-wide coercions contribute an
        // concrete receiver-flow candidate here.
        return (!source.kind().is_trait()).then_some((source, principal));
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

#[derive(Clone, Default)]
struct DynState {
    flows: HashMap<Place, DynFlow>,
    aliases: HashMap<Place, Vec<Place>>,
}

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

    let mut entry = DynState::default();
    for (index, argument) in body.arg_locals().iter().enumerate() {
        if type_contains_dyn(argument.ty) {
            entry
                .flows
                .insert(Place::from(index + 1), DynFlow::parameter(index));
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
                    || unknown_if_dyn_place(body, destination, UnresolvedReason::ExternalCode),
                    |callee| {
                        if matches!(callee.kind, InstanceKind::Virtual { .. }) {
                            unknown_if_dyn_place(body, destination, UnresolvedReason::ExternalCode)
                        } else if let Some(summary) = return_summaries.get(&callee) {
                            let mut flow = resolve_symbolic_flow(summary, &argument_flows);
                            if !callee.def.krate().is_local {
                                flow.merge(&external_return_flow(
                                    body,
                                    args,
                                    destination,
                                    &argument_flows,
                                ));
                            }
                            flow
                        } else if local_instances.contains(&callee) {
                            DynFlow::default()
                        } else {
                            external_return_flow(body, args, destination, &argument_flows)
                        }
                    },
                );

                apply_external_memory_effects(
                    body,
                    &mut state,
                    func,
                    args,
                    resolve_called_instance(body, func),
                    &argument_flows,
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

fn external_return_flow(
    body: &Body,
    arguments: &[Operand],
    destination: &Place,
    argument_flows: &[DynFlow],
) -> DynFlow {
    if !destination.ty(body.locals()).is_ok_and(type_contains_dyn) {
        return DynFlow::default();
    }
    let mut flow = DynFlow::unresolved(UnresolvedReason::ExternalCode);
    for (argument, argument_flow) in arguments.iter().zip(argument_flows) {
        if argument.ty(body.locals()).is_ok_and(type_contains_dyn) {
            flow.merge(argument_flow);
        }
    }
    flow
}

/// Model memory that crosses a call boundary as an abstract region attached
/// to the referenced MIR place. This is type-directed: it does not name Vec,
/// Arc, HashMap, or individual methods. Opaque external behavior remains in
/// the unresolved-reason set, while concrete values that cross that same
/// boundary remain available as partial evidence instead of being lost.
fn apply_external_memory_effects(
    body: &Body,
    state: &mut DynState,
    _function: &Operand,
    arguments: &[Operand],
    resolved: Option<Instance>,
    argument_flows: &[DynFlow],
) {
    if resolved.is_some_and(|callee| callee.def.krate().is_local) {
        return;
    }
    let mut stored = DynFlow::default();
    for (argument, flow) in arguments.iter().zip(argument_flows) {
        let Ok(ty) = argument.ty(body.locals()) else {
            continue;
        };
        if !is_mutable_reference(ty) && type_contains_dyn(ty) {
            stored.merge(flow);
        }
    }
    if stored.is_empty() {
        return;
    }
    stored
        .unresolved_reasons
        .insert(UnresolvedReason::ExternalCode);
    for argument in arguments {
        let Ok(ty) = argument.ty(body.locals()) else {
            continue;
        };
        if !is_mutable_reference(ty) || !type_contains_dyn(ty) {
            continue;
        }
        let Some(place) = operand_place(argument) else {
            continue;
        };
        merge_dyn_place(state, place, &stored);
    }
}

fn operand_place(operand: &Operand) -> Option<&Place> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
    }
}

fn is_mutable_reference(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(RigidTy::Ref(_, _, rustc_public::mir::Mutability::Mut))
            | TyKind::RigidTy(RigidTy::RawPtr(_, rustc_public::mir::Mutability::Mut))
    )
}

fn degrade_dyn_analysis_to_unknown(body: &Body, analysis: &mut BodyDynAnalysis) {
    if type_contains_dyn(body.ret_local().ty) {
        analysis
            .return_flow
            .unresolved_reasons
            .insert(UnresolvedReason::AnalysisLimit);
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
                flow.unresolved_reasons
                    .insert(UnresolvedReason::AnalysisLimit);
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
    match value {
        Rvalue::Ref(_, _, source) | Rvalue::AddressOf(_, source) | Rvalue::CopyForDeref(source) => {
            let targets = resolve_alias_places(state, source);
            state.aliases.insert(destination.clone(), targets);
        }
        Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _)
        | Rvalue::Cast(_, Operand::Copy(source) | Operand::Move(source), _) => {
            if let Some(targets) = state.aliases.get(source).cloned() {
                state.aliases.insert(destination.clone(), targets);
            } else {
                state.aliases.remove(destination);
            }
        }
        _ => {
            state.aliases.remove(destination);
        }
    }
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
                .and_then(|(concrete_ty, principal)| {
                    principal.bound_vars.is_empty().then(|| {
                        let principal = principal.value;
                        DynFlow::concrete(TraitRef::new(
                            principal.def_id,
                            concrete_ty,
                            &principal.generic_args,
                        ))
                    })
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
        flow.unresolved_reasons
            .insert(UnresolvedReason::AnalysisLimit);
    }
    flow
}

fn dyn_flow_for_operand(body: &Body, state: &DynState, operand: &Operand) -> DynFlow {
    let mut flow = match operand {
        Operand::Copy(place) | Operand::Move(place) => read_dyn_place(state, place),
        Operand::Constant(_) | Operand::RuntimeChecks(_) => DynFlow::default(),
    };
    if flow.is_empty() && operand.ty(body.locals()).is_ok_and(type_contains_dyn) {
        flow.unresolved_reasons
            .insert(UnresolvedReason::ExternalMemory);
    }
    flow
}

fn unknown_if_dyn_place(body: &Body, place: &Place, reason: UnresolvedReason) -> DynFlow {
    place
        .ty(body.locals())
        .ok()
        .filter(|ty| type_contains_dyn(*ty))
        .map_or_else(DynFlow::default, |_| DynFlow::unresolved(reason))
}

fn type_contains_dyn(ty: Ty) -> bool {
    ty.to_string().contains("dyn ")
}

fn collect_adt_constructor_names(ty: Ty, names: &mut HashSet<String>) {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(definition, arguments)) => {
            names.extend(
                definition
                    .variants()
                    .into_iter()
                    .map(|variant| variant.name().to_string()),
            );
            for argument in arguments.0 {
                if let Some(ty) = argument.ty() {
                    collect_adt_constructor_names(*ty, names);
                }
            }
        }
        TyKind::RigidTy(
            RigidTy::FnDef(_, arguments)
            | RigidTy::Closure(_, arguments)
            | RigidTy::Coroutine(_, arguments)
            | RigidTy::CoroutineClosure(_, arguments)
            | RigidTy::CoroutineWitness(_, arguments),
        ) => {
            for argument in arguments.0 {
                if let Some(ty) = argument.ty() {
                    collect_adt_constructor_names(*ty, names);
                }
            }
        }
        TyKind::RigidTy(
            RigidTy::Array(ty, _)
            | RigidTy::Slice(ty)
            | RigidTy::RawPtr(ty, _)
            | RigidTy::Ref(_, ty, _),
        ) => collect_adt_constructor_names(ty, names),
        TyKind::RigidTy(RigidTy::Tuple(types)) => {
            for ty in types {
                collect_adt_constructor_names(ty, names);
            }
        }
        _ => {}
    }
}

fn read_dyn_place(state: &DynState, place: &Place) -> DynFlow {
    if let Some(flow) = state.flows.get(place) {
        return flow.clone();
    }
    let alias_targets = resolve_alias_places(state, place);
    if alias_targets.len() != 1 || alias_targets.first() != Some(place) {
        let mut aliased = DynFlow::default();
        for target in alias_targets {
            if target != *place {
                aliased.merge(&read_dyn_place_without_alias(state, &target));
            }
        }
        if !aliased.is_empty() {
            return aliased;
        }
    }
    read_dyn_place_without_alias(state, place)
}

fn read_dyn_place_without_alias(state: &DynState, place: &Place) -> DynFlow {
    if let Some(flow) = state.flows.get(place) {
        return flow.clone();
    }
    let mut ancestor = place.clone();
    while ancestor.projection.pop().is_some() {
        if let Some(flow) = state.flows.get(&ancestor) {
            let suffix = &place.projection[ancestor.projection.len()..];
            return if suffix
                .iter()
                .all(|projection| matches!(projection, ProjectionElem::Deref))
            {
                flow.clone()
            } else {
                // Locally built aggregates have explicit field entries above.
                // A whole-value-only region came from opaque memory (for
                // example an allocator-backed container), so retain its
                // candidates but mark the projection as partial rather than
                // assigning them as exact field provenance.
                let mut projected = flow.clone();
                projected
                    .unresolved_reasons
                    .insert(UnresolvedReason::ExternalMemory);
                projected
            };
        }
    }
    let mut result = DynFlow::default();
    for (candidate, flow) in &state.flows {
        if place_is_prefix(place, candidate) {
            result.merge(flow);
        }
    }
    result
}

fn write_dyn_place(state: &mut DynState, place: &Place, flow: DynFlow) {
    let targets = resolve_alias_places(state, place);
    let targets = if targets.len() == 1 && targets[0] == *place {
        vec![place.clone()]
    } else {
        targets
    };
    for target in targets {
        state
            .flows
            .retain(|candidate, _| !place_is_prefix(&target, candidate));
        if !flow.is_empty() {
            state.flows.insert(target, flow.clone());
        }
    }
}

fn merge_dyn_place(state: &mut DynState, place: &Place, flow: &DynFlow) {
    if flow.is_empty() {
        return;
    }
    let targets = resolve_alias_places(state, place);
    for target in targets {
        state.flows.entry(target).or_default().merge(flow);
    }
}

fn resolve_alias_places(state: &DynState, place: &Place) -> Vec<Place> {
    if let Some(targets) = state.aliases.get(place) {
        return targets.clone();
    }
    let base = Place::from(place.local);
    let Some(targets) = state.aliases.get(&base) else {
        return vec![place.clone()];
    };
    let mut suffix = place.projection.as_slice();
    if suffix
        .first()
        .is_some_and(|projection| matches!(projection, ProjectionElem::Deref))
    {
        suffix = &suffix[1..];
    }
    targets
        .iter()
        .cloned()
        .map(|mut target| {
            target.projection.extend_from_slice(suffix);
            target
        })
        .collect()
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
    for (place, flow) in &source.flows {
        changed |= destination
            .flows
            .entry(place.clone())
            .or_default()
            .merge(flow);
    }
    for (place, targets) in &source.aliases {
        let destination_targets = destination.aliases.entry(place.clone()).or_default();
        for target in targets {
            if !destination_targets.contains(target) {
                destination_targets.push(target.clone());
                changed = true;
            }
        }
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
        unresolved_reasons: flow.unresolved_reasons.clone(),
    };
    for parameter in &flow.parameters {
        if let Some(argument) = arguments.get(*parameter) {
            resolved.merge(argument);
        } else {
            resolved
                .unresolved_reasons
                .insert(UnresolvedReason::AnalysisLimit);
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
                        let candidate_name = stable_instance_name(candidate);
                        if let Some(target) = index.get(&normalize_instance_key(&candidate_name)) {
                            incoming[*target] += 1;
                        }
                    }
                }
                RawSemanticCallTarget::Indirect { .. } | RawSemanticCallTarget::Unresolved => {}
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
            // Multiple compiler instances can normalize to the same display
            // key. Even when the emitted semantic function was already seen,
            // this raw instance is consumed; otherwise the disconnected-root
            // fallback below selects it forever.
            covered_raw.insert(raw_index);
            if !visited.insert(function_key.clone()) {
                continue;
            }
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
                        let receiver_flow = semantic_dyn_flow(receiver, crate_name);
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
                            let candidate_name = stable_instance_name(candidate);
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
                            open: !receiver.unresolved_reasons.is_empty(),
                            unresolved_reasons: receiver.unresolved_reasons,
                            receiver_flow,
                        }
                    }
                    RawSemanticCallTarget::Indirect { signature } => SemanticCallTarget::Indirect {
                        signature: signature.clone(),
                    },
                    RawSemanticCallTarget::Unresolved => SemanticCallTarget::Unresolved,
                };
                calls.push(SemanticCall {
                    target,
                    definition_name: raw_call.definition_name.clone(),
                    span: raw_call.span.clone(),
                    argument_types: raw_call.argument_types.clone(),
                    argument_flows: raw_call
                        .argument_flows
                        .iter()
                        .map(|flow| semantic_dyn_flow(flow, crate_name))
                        .collect(),
                });
            }

            functions.push(SemanticFunction {
                base_key: raw.key.clone(),
                key: function_key,
                display: raw.display.clone(),
                definition_name: raw.definition_name.clone(),
                body_span: raw.body_span.clone(),
                calls,
                constructor_spans: raw.constructor_spans.clone(),
                constructor_names: raw.constructor_names.clone(),
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
            unresolved_reasons: parameter
                .contains("dyn ")
                .then_some(UnresolvedReason::OpaqueInput)
                .into_iter()
                .collect(),
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
                    unresolved_reasons: [UnresolvedReason::AnalysisLimit].into_iter().collect(),
                },
                |flow| {
                    let mut resolved = resolve_context_flow(flow, caller_context);
                    if resolved.concrete.is_empty() && resolved.unresolved_reasons.is_empty() {
                        resolved
                            .unresolved_reasons
                            .insert(UnresolvedReason::AnalysisLimit);
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
        unresolved_reasons: flow.unresolved_reasons.clone(),
    };
    for parameter in &flow.parameters {
        if let Some(argument) = context.get(*parameter) {
            resolved.merge(argument);
        } else {
            resolved
                .unresolved_reasons
                .insert(UnresolvedReason::AnalysisLimit);
        }
    }
    resolved
}

fn semantic_dyn_flow(flow: &DynFlow, crate_name: &str) -> SemanticDynFlow {
    let mut concrete_types = flow
        .concrete
        .iter()
        .map(|trait_ref| normalize_type_display(&trait_ref.self_ty().to_string(), crate_name))
        .collect::<Vec<_>>();
    concrete_types.sort();
    concrete_types.dedup();
    SemanticDynFlow {
        concrete_types,
        parameters: flow.parameters.clone(),
        unresolved_reasons: flow.unresolved_reasons.clone(),
    }
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
                || !value.unresolved_reasons.is_empty()
        })
        .map(|(index, value)| {
            let mut candidates = value
                .concrete
                .iter()
                .map(|trait_ref| trait_ref.self_ty().to_string())
                .collect::<Vec<_>>();
            candidates.sort();
            for reason in &value.unresolved_reasons {
                candidates.push(format!("?{reason}"));
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

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct NamedDynFlow {
    concrete_types: BTreeSet<String>,
    unresolved_reasons: BTreeSet<UnresolvedReason>,
}

fn respecialize_merged_semantic_program(program: &mut SemanticProgram) {
    if program.functions.is_empty() {
        return;
    }
    let mut templates = BTreeMap::<String, SemanticFunction>::new();
    for function in &program.functions {
        templates
            .entry(function.base_key.clone())
            .and_modify(|existing| {
                if semantic_template_score(function) > semantic_template_score(existing) {
                    *existing = function.clone();
                }
            })
            .or_insert_with(|| function.clone());
    }
    let bases = templates.keys().cloned().collect::<HashSet<_>>();
    let mut incoming = bases
        .iter()
        .cloned()
        .map(|key| (key, 0usize))
        .collect::<HashMap<_, _>>();
    for function in templates.values() {
        for call in &function.calls {
            let SemanticCallTarget::Direct { key, .. } = &call.target else {
                continue;
            };
            if let Some(base) = semantic_target_base(key, &bases) {
                *incoming.entry(base).or_default() += 1;
            }
        }
    }

    let mut pending = incoming
        .iter()
        .filter(|(_, count)| **count == 0)
        .filter_map(|(base, _)| {
            templates
                .get(base)
                .map(|function| (base.clone(), root_named_context(function)))
        })
        .collect::<VecDeque<_>>();
    let mut visited = HashSet::new();
    let mut covered = HashSet::new();
    let mut specialized = Vec::new();

    loop {
        while let Some((base, context)) = pending.pop_front() {
            let Some(template) = templates.get(&base) else {
                continue;
            };
            covered.insert(base.clone());
            let key = named_specialized_key(template, &context);
            if !visited.insert(key.clone()) {
                continue;
            }
            let mut function = template.clone();
            function.key = key;
            for call in &mut function.calls {
                match &mut call.target {
                    SemanticCallTarget::Direct { key, .. } => {
                        let Some(target_base) = semantic_target_base(key, &bases) else {
                            continue;
                        };
                        let Some(target) = templates.get(&target_base) else {
                            continue;
                        };
                        let target_context =
                            named_call_context(target, &call.argument_flows, &context);
                        *key = named_specialized_key(target, &target_context);
                        pending.push_back((target_base, target_context));
                    }
                    SemanticCallTarget::Dynamic {
                        key,
                        candidates,
                        open,
                        unresolved_reasons,
                        receiver_flow,
                        ..
                    } => {
                        let mut receiver = resolve_named_flow(receiver_flow, &context);
                        if let Some(argument_receiver) = call.argument_flows.first() {
                            merge_named_flow(
                                &mut receiver,
                                &resolve_named_flow(argument_receiver, &context),
                            );
                        }
                        *candidates = receiver
                            .concrete_types
                            .iter()
                            .filter_map(|concrete| {
                                let candidate =
                                    named_dispatch_candidate(concrete, key, templates.values())?;
                                let candidate_context =
                                    named_call_context(candidate, &call.argument_flows, &context);
                                let candidate_key =
                                    named_specialized_key(candidate, &candidate_context);
                                pending.push_back((candidate.base_key.clone(), candidate_context));
                                Some(SemanticDispatchCandidate {
                                    key: candidate_key,
                                    display: candidate.display.clone(),
                                })
                            })
                            .collect();
                        candidates.sort_by(|left, right| left.key.cmp(&right.key));
                        candidates.dedup_by(|left, right| left.key == right.key);
                        *unresolved_reasons = receiver.unresolved_reasons;
                        *open = !unresolved_reasons.is_empty();
                    }
                    SemanticCallTarget::Indirect { .. } | SemanticCallTarget::Unresolved => {}
                }
            }
            specialized.push(function);
        }

        let Some(uncovered) = templates
            .keys()
            .find(|base| !covered.contains(*base))
            .cloned()
        else {
            break;
        };
        let context = root_named_context(&templates[&uncovered]);
        pending.push_back((uncovered, context));
    }
    specialized.sort_by(|left, right| left.key.cmp(&right.key));
    program.functions = specialized;
}

fn merge_named_flow(destination: &mut NamedDynFlow, source: &NamedDynFlow) {
    destination
        .concrete_types
        .extend(source.concrete_types.iter().cloned());
    destination
        .unresolved_reasons
        .extend(source.unresolved_reasons.iter().cloned());
}

fn semantic_template_score(function: &SemanticFunction) -> usize {
    let symbolic = function
        .calls
        .iter()
        .map(|call| {
            let arguments = call
                .argument_flows
                .iter()
                .map(|flow| flow.parameters.len())
                .sum::<usize>();
            let receiver = match &call.target {
                SemanticCallTarget::Dynamic { receiver_flow, .. } => receiver_flow.parameters.len(),
                _ => 0,
            };
            arguments + receiver
        })
        .sum::<usize>();
    let exact_base = usize::from(function.key == function.base_key);
    symbolic.saturating_mul(10) + exact_base
}

fn semantic_target_base(key: &str, bases: &HashSet<String>) -> Option<String> {
    if bases.contains(key) {
        return Some(key.to_owned());
    }
    bases
        .iter()
        .filter(|base| key.starts_with(base.as_str()))
        .max_by_key(|base| base.len())
        .cloned()
}

fn root_named_context(function: &SemanticFunction) -> Vec<NamedDynFlow> {
    function
        .parameter_types
        .iter()
        .map(|parameter| NamedDynFlow {
            concrete_types: BTreeSet::new(),
            unresolved_reasons: parameter
                .contains("dyn ")
                .then_some(UnresolvedReason::OpaqueInput)
                .into_iter()
                .collect(),
        })
        .collect()
}

fn named_call_context(
    callee: &SemanticFunction,
    arguments: &[SemanticDynFlow],
    caller_context: &[NamedDynFlow],
) -> Vec<NamedDynFlow> {
    callee
        .parameter_types
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            if !parameter.contains("dyn ") {
                return NamedDynFlow::default();
            }
            arguments.get(index).map_or_else(
                || NamedDynFlow {
                    concrete_types: BTreeSet::new(),
                    unresolved_reasons: [UnresolvedReason::AnalysisLimit].into_iter().collect(),
                },
                |flow| resolve_named_flow(flow, caller_context),
            )
        })
        .collect()
}

fn resolve_named_flow(flow: &SemanticDynFlow, context: &[NamedDynFlow]) -> NamedDynFlow {
    let mut resolved = NamedDynFlow {
        concrete_types: flow.concrete_types.iter().cloned().collect(),
        unresolved_reasons: flow.unresolved_reasons.clone(),
    };
    for parameter in &flow.parameters {
        if let Some(value) = context.get(*parameter) {
            resolved
                .concrete_types
                .extend(value.concrete_types.iter().cloned());
            resolved
                .unresolved_reasons
                .extend(value.unresolved_reasons.iter().cloned());
        } else {
            resolved
                .unresolved_reasons
                .insert(UnresolvedReason::AnalysisLimit);
        }
    }
    resolved
}

fn named_specialized_key(function: &SemanticFunction, context: &[NamedDynFlow]) -> String {
    let bindings = context
        .iter()
        .enumerate()
        .filter(|(index, flow)| {
            function
                .parameter_types
                .get(*index)
                .is_some_and(|parameter| parameter.contains("dyn "))
                || !flow.concrete_types.is_empty()
                || !flow.unresolved_reasons.is_empty()
        })
        .map(|(index, flow)| {
            let mut values = flow.concrete_types.iter().cloned().collect::<Vec<_>>();
            values.extend(
                flow.unresolved_reasons
                    .iter()
                    .map(|reason| format!("?{reason}")),
            );
            format!("{index}={}", values.join("|"))
        })
        .collect::<Vec<_>>();
    if bindings.is_empty() {
        function.base_key.clone()
    } else {
        format!("{}#ctx[dyn:{}]", function.base_key, bindings.join(","))
    }
}

fn named_dispatch_candidate<'a>(
    concrete: &str,
    dispatch: &str,
    functions: impl Iterator<Item = &'a SemanticFunction>,
) -> Option<&'a SemanticFunction> {
    let method = dispatch
        .rsplit("::")
        .next()
        .unwrap_or(dispatch)
        .trim_end_matches('>');
    let concrete = concrete
        .rsplit("::")
        .next()
        .unwrap_or(concrete)
        .trim_matches(['&', ' ', '<', '>']);
    functions
        .filter(|function| {
            function.display.ends_with(&format!("{concrete}::{method}"))
                || (function.display.ends_with(&format!("::{method}"))
                    && function.base_key.contains(concrete)
                    && function.base_key.contains(" as "))
        })
        .min_by_key(|function| function.base_key.clone())
}

fn merge_semantic_program(syntax: FileAnalysis, mut semantic: SemanticProgram) -> FileAnalysis {
    let mut analysis = FileAnalysis {
        source_files: syntax.source_files.clone(),
        ..FileAnalysis::default()
    };
    let file_identities = source_file_identities(&syntax, &semantic);
    canonicalize_semantic_closures(&syntax, &mut semantic, &file_identities);
    let local_function_keys = semantic
        .functions
        .iter()
        .map(|function| function.key.clone())
        .collect::<HashSet<_>>();
    let semantic_closure_keys = semantic_closure_keys(&syntax, &semantic, &file_identities);
    let mut required_syntax_closures = HashSet::<SymbolId>::new();
    let mut matched_syntax_functions = HashSet::<SymbolId>::new();
    let generic_syntax_functions = syntax
        .facts
        .iter()
        .filter(|fact| fact.kind == "generic-parameter")
        .map(|fact| fact.subject.clone())
        .collect::<HashSet<_>>();
    let mut syntax_functions_by_file = HashMap::<PathBuf, Vec<usize>>::new();
    for (index, function) in syntax.functions.iter().enumerate() {
        syntax_functions_by_file
            .entry(source_file_identity(&file_identities, &function.span.file).to_path_buf())
            .or_default()
            .push(index);
    }
    let mut facts_by_subject = HashMap::<&SymbolId, Vec<&LanguageFact>>::new();
    for fact in &syntax.facts {
        facts_by_subject
            .entry(&fact.subject)
            .or_default()
            .push(fact);
    }

    for semantic_function in semantic.functions {
        let function_file =
            source_file_identity(&file_identities, &semantic_function.body_span.file);
        let Some(candidate_indices) = syntax_functions_by_file.get(function_file) else {
            continue;
        };
        let Some(template) = best_function_template(
            &syntax.functions,
            candidate_indices,
            &semantic_function.body_span,
        ) else {
            // Compiler-generated functions (drop glue, coroutine shims, etc.)
            // are intentionally omitted until they have explicit source syntax.
            continue;
        };
        matched_syntax_functions.insert(template.id.clone());
        let id = semantic_symbol(semantic_function.key);
        let mut claimed_calls = HashSet::new();
        let calls = template
            .calls
            .iter()
            .filter_map(|call| {
                let Some(match_index) = best_semantic_call(
                    call,
                    &semantic_function.calls,
                    &claimed_calls,
                    &file_identities,
                ) else {
                    let is_constructor = semantic_function
                        .constructor_spans
                        .iter()
                        .any(|span| span_coordinates_equal(&call.span, span))
                        || call_syntax_name(call).is_some_and(|name| {
                            semantic_function
                                .constructor_names
                                .iter()
                                .any(|constructor| constructor == name)
                        });
                    if is_constructor {
                        return None;
                    }
                    let mut unresolved = call.clone();
                    if let Some(closure) =
                        source_closure_for_call(template, call, &syntax.functions)
                    {
                        unresolved.target = semantic_closure_keys
                            .get(&closure.id)
                            .cloned()
                            .map(semantic_symbol)
                            .map_or_else(
                                || {
                                    required_syntax_closures.insert(closure.id.clone());
                                    CallTarget::Direct(closure.id.clone())
                                },
                                CallTarget::Direct,
                            );
                        unresolved.label =
                            replace_label_callee(&unresolved.label, closure_label_callee(closure));
                    }
                    return Some(unresolved);
                };
                let mut resolved = call.clone();
                claimed_calls.insert(match_index);
                let semantic_call = &semantic_function.calls[match_index];
                match &semantic_call.target {
                    SemanticCallTarget::Direct { key, display } => {
                        resolved.target = CallTarget::Direct(semantic_symbol(key.clone()));
                        if local_function_keys.contains(key) {
                            resolved.label = replace_label_callee(&resolved.label, display);
                        }
                    }
                    SemanticCallTarget::Dynamic {
                        key,
                        display,
                        candidates,
                        open,
                        unresolved_reasons,
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
                            evidence: DispatchEvidence::ExactFlow,
                            unresolved_reasons: if unresolved_reasons.is_empty()
                                && candidates.is_empty()
                            {
                                [UnresolvedReason::AnalysisLimit].into_iter().collect()
                            } else {
                                unresolved_reasons.clone()
                            },
                        };
                        resolved.label = replace_label_callee(&resolved.label, display);
                    }
                    SemanticCallTarget::Indirect { signature } => {
                        resolved.target = CallTarget::Indirect {
                            signature: Some(signature.clone()),
                            reason: UnresolvedReason::FunctionPointer,
                        };
                    }
                    SemanticCallTarget::Unresolved => {
                        resolved.target = CallTarget::Unresolved;
                    }
                }
                let argument_types = semantic_call_argument_types(semantic_call);
                resolved.label.typed = Some(annotate_rust_label(
                    &resolved.label.default,
                    &argument_types,
                ));
                Some(resolved)
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
        if let Some(facts) = facts_by_subject.get(&template.id) {
            analysis.facts.extend(facts.iter().map(|fact| {
                let mut fact = (*fact).clone();
                fact.subject = id.clone();
                fact
            }));
        }
    }

    for function in &syntax.functions {
        let preserve_closure = required_syntax_closures.contains(&function.id);
        let preserve_open_generic = generic_syntax_functions.contains(&function.id)
            && !matched_syntax_functions.contains(&function.id);
        if !preserve_closure && !preserve_open_generic {
            continue;
        }
        analysis.functions.push(function.clone());
        if preserve_open_generic && let Some(facts) = facts_by_subject.get(&function.id) {
            analysis.facts.extend(facts.iter().copied().cloned());
        }
    }

    synthesize_referenced_generic_instances(&mut analysis, &syntax);

    analysis
}

fn synthesize_referenced_generic_instances(analysis: &mut FileAnalysis, syntax: &FileAnalysis) {
    let generic_parameters = syntax
        .facts
        .iter()
        .filter(|fact| fact.kind == "generic-parameter")
        .fold(BTreeMap::<SymbolId, Vec<String>>::new(), |mut map, fact| {
            map.entry(fact.subject.clone())
                .or_default()
                .push(fact.key.clone());
            map
        });
    if generic_parameters.is_empty() {
        return;
    }

    let mut used_templates = HashSet::new();
    loop {
        let known = analysis
            .functions
            .iter()
            .map(|function| function.id.clone())
            .collect::<HashSet<_>>();
        let missing = analysis
            .functions
            .iter()
            .flat_map(|function| &function.calls)
            .filter_map(|call| match &call.target {
                CallTarget::Direct(target)
                    if !known.contains(target) && target.language.0 == "rust" =>
                {
                    Some(target.clone())
                }
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut added = Vec::new();
        for target in missing {
            let Some((base, arguments)) = generic_instance_parts(&target.name) else {
                continue;
            };
            let Some(template) = syntax.functions.iter().find(|function| {
                function.id.name == base
                    && generic_parameters
                        .get(&function.id)
                        .is_some_and(|parameters| parameters.len() == arguments.len())
            }) else {
                continue;
            };
            let parameters = &generic_parameters[&template.id];
            let bindings = parameters
                .iter()
                .cloned()
                .zip(arguments.iter().cloned())
                .collect::<HashMap<_, _>>();
            let mut function = template.clone();
            function.id = target.clone();
            let display = normalize_instance_display(&target.name, "");
            function.label = replace_label_callee(&function.label, &display);
            for call in &mut function.calls {
                substitute_generic_call(call, &bindings, &analysis.functions);
            }
            used_templates.insert(template.id.clone());
            added.push(function);
        }
        if added.is_empty() {
            break;
        }
        analysis.functions.extend(added);
    }

    let displays = analysis
        .functions
        .iter()
        .map(|function| {
            (
                function.id.clone(),
                outer_call_arguments_start(&function.label.default)
                    .map_or(function.label.default.clone(), |start| {
                        function.label.default[..start].to_owned()
                    }),
            )
        })
        .collect::<HashMap<_, _>>();
    for function in &mut analysis.functions {
        for call in &mut function.calls {
            let CallTarget::Direct(target) = &call.target else {
                continue;
            };
            if let Some(display) = displays.get(target) {
                call.label = replace_label_callee(&call.label, display);
            }
        }
    }
    analysis
        .functions
        .retain(|function| !used_templates.contains(&function.id));
    analysis
        .facts
        .retain(|fact| !used_templates.contains(&fact.subject));
}

fn generic_instance_parts(instance: &str) -> Option<(String, Vec<String>)> {
    let start = instance.find('<')?;
    let end = instance.rfind('>')?;
    if end <= start {
        return None;
    }
    let base = instance[..start]
        .rsplit("::")
        .next()
        .unwrap_or(&instance[..start])
        .to_owned();
    let arguments = split_rust_arguments(&instance[start + 1..end])
        .into_iter()
        .map(simplify_type_paths)
        .collect();
    Some((base, arguments))
}

fn substitute_generic_call(
    call: &mut CallSite,
    bindings: &HashMap<String, String>,
    functions: &[FunctionInfo],
) {
    let CallTarget::Direct(target) = &call.target else {
        return;
    };
    let Some(container) = target.container.as_deref() else {
        return;
    };
    let parameter = container
        .split_once(" as ")
        .map_or(container, |(parameter, _)| parameter);
    let Some(concrete) = bindings.get(parameter) else {
        return;
    };
    let callee = format!("{concrete}::{}", target.name);
    call.label = replace_label_callee(&call.label, &callee);
    call.target = functions
        .iter()
        .find(|function| {
            outer_call_arguments_start(&function.label.default)
                .is_some_and(|start| function.label.default[..start] == callee)
        })
        .map(|function| function.id.clone())
        .map_or_else(
            || {
                CallTarget::Direct(SymbolId {
                    language: LanguageId::new("rust"),
                    module: target.module.clone(),
                    container: Some(concrete.clone()),
                    name: target.name.clone(),
                })
            },
            CallTarget::Direct,
        );
}

fn semantic_closure_keys(
    syntax: &FileAnalysis,
    semantic: &SemanticProgram,
    file_identities: &HashMap<PathBuf, PathBuf>,
) -> HashMap<SymbolId, String> {
    syntax
        .functions
        .iter()
        .filter(|function| is_source_closure(function))
        .filter_map(|closure| {
            semantic
                .functions
                .iter()
                .filter(|function| {
                    source_file_identity(file_identities, &closure.span.file)
                        == source_file_identity(file_identities, &function.body_span.file)
                        && span_contains(&closure.span, &function.body_span)
                })
                .min_by_key(|function| span_size(&function.body_span))
                .map(|function| (closure.id.clone(), function.key.clone()))
        })
        .collect()
}

fn source_closure_for_call<'a>(
    owner: &FunctionInfo,
    call: &CallSite,
    functions: &'a [FunctionInfo],
) -> Option<&'a FunctionInfo> {
    let name = call_syntax_name(call)?;
    let expected_container = owner.id.qualified_parts().join("::");
    let expected_lambda = format!("λ{name}");
    functions.iter().find(|function| {
        is_source_closure(function)
            && function.id.container.as_deref() == Some(expected_container.as_str())
            && closure_label_callee(function) == expected_lambda
    })
}

fn closure_label_callee(function: &FunctionInfo) -> &str {
    outer_call_arguments_start(&function.label.default)
        .map_or(function.label.default.as_str(), |start| {
            &function.label.default[..start]
        })
}

#[derive(Clone)]
struct SemanticClosureSource {
    span: SourceSpan,
    identity: String,
    lambda: String,
}

#[derive(Clone, Copy)]
enum ClosureRewrite {
    Identity,
    Display,
}

fn canonicalize_semantic_closures(
    syntax: &FileAnalysis,
    semantic: &mut SemanticProgram,
    file_identities: &HashMap<PathBuf, PathBuf>,
) {
    let closures = syntax
        .functions
        .iter()
        .filter(|function| is_source_closure(function))
        .map(|function| SemanticClosureSource {
            span: function.span.clone(),
            identity: format!("{{lambda-id:{}}}", function.id),
            lambda: outer_call_arguments_start(&function.label.default).map_or_else(
                || function.label.default.clone(),
                |start| function.label.default[..start].to_owned(),
            ),
        })
        .collect::<Vec<_>>();
    let compiler_sources = semantic
        .functions
        .iter()
        .filter_map(|function| {
            let source = closure_for_body_span(&function.body_span, &closures, file_identities)?;
            let marker = compiler_closure_marker(&function.definition_name)?;
            Some((marker, (source.identity.clone(), source.lambda.clone())))
        })
        .collect::<HashMap<_, _>>();

    let mut direct_closures = HashMap::<String, (String, String)>::new();
    for function in &semantic.functions {
        let Some(source) = closure_for_body_span(&function.body_span, &closures, file_identities)
        else {
            continue;
        };
        let located_key = canonicalize_closure_value(
            &function.key,
            &closures,
            file_identities,
            ClosureRewrite::Identity,
            &compiler_sources,
        );
        let key = replace_closure_definition(&located_key, &source.identity);
        let display = canonicalize_closure_value(
            &closure_instance_display(&source.lambda, &function.display),
            &closures,
            file_identities,
            ClosureRewrite::Display,
            &compiler_sources,
        );
        direct_closures.insert(function.key.clone(), (key, display));
    }

    for function in &mut semantic.functions {
        let original_key = function.key.clone();
        if let Some((key, display)) = direct_closures.get(&original_key) {
            function.key = key.clone();
            function.display = display.clone();
        } else {
            function.key = canonicalize_closure_value(
                &function.key,
                &closures,
                file_identities,
                ClosureRewrite::Identity,
                &compiler_sources,
            );
            function.display = canonicalize_closure_value(
                &function.display,
                &closures,
                file_identities,
                ClosureRewrite::Display,
                &compiler_sources,
            );
        }
        for parameter in &mut function.parameter_types {
            *parameter = canonicalize_closure_value(
                parameter,
                &closures,
                file_identities,
                ClosureRewrite::Display,
                &compiler_sources,
            );
        }
        for call in &mut function.calls {
            for argument in &mut call.argument_types {
                *argument = canonicalize_closure_value(
                    argument,
                    &closures,
                    file_identities,
                    ClosureRewrite::Display,
                    &compiler_sources,
                );
            }
            match &mut call.target {
                SemanticCallTarget::Direct { key, display } => {
                    rewrite_closure_target(
                        key,
                        display,
                        &direct_closures,
                        &closures,
                        file_identities,
                        &compiler_sources,
                    );
                }
                SemanticCallTarget::Dynamic {
                    key,
                    display,
                    candidates,
                    ..
                } => {
                    rewrite_closure_target(
                        key,
                        display,
                        &direct_closures,
                        &closures,
                        file_identities,
                        &compiler_sources,
                    );
                    for candidate in candidates {
                        rewrite_closure_target(
                            &mut candidate.key,
                            &mut candidate.display,
                            &direct_closures,
                            &closures,
                            file_identities,
                            &compiler_sources,
                        );
                    }
                }
                SemanticCallTarget::Indirect { .. } => {}
                SemanticCallTarget::Unresolved => {}
            }
        }
    }
}

fn is_source_closure(function: &FunctionInfo) -> bool {
    function.id.name.starts_with("{lambda:")
}

fn rewrite_closure_target(
    key: &mut String,
    display: &mut String,
    direct_closures: &HashMap<String, (String, String)>,
    closures: &[SemanticClosureSource],
    file_identities: &HashMap<PathBuf, PathBuf>,
    compiler_sources: &HashMap<String, (String, String)>,
) {
    if let Some((canonical_key, canonical_display)) = direct_closures.get(key) {
        *key = canonical_key.clone();
        *display = canonical_display.clone();
        return;
    }
    *key = canonicalize_closure_value(
        key,
        closures,
        file_identities,
        ClosureRewrite::Identity,
        compiler_sources,
    );
    *display = canonicalize_closure_value(
        display,
        closures,
        file_identities,
        ClosureRewrite::Display,
        compiler_sources,
    );
}

fn canonicalize_closure_value(
    value: &str,
    closures: &[SemanticClosureSource],
    file_identities: &HashMap<PathBuf, PathBuf>,
    rewrite: ClosureRewrite,
    compiler_sources: &HashMap<String, (String, String)>,
) -> String {
    let mut value = rewrite_located_closures(value, closures, file_identities, rewrite);
    for (marker, (identity, display)) in compiler_sources {
        value = value.replace(
            marker,
            match rewrite {
                ClosureRewrite::Identity => identity,
                ClosureRewrite::Display => display,
            },
        );
    }
    match rewrite {
        ClosureRewrite::Identity => value,
        ClosureRewrite::Display => render_compiler_closure_markers(&value),
    }
}

fn render_compiler_closure_markers(value: &str) -> String {
    let mut output = String::with_capacity(value.len());
    let mut remainder = value;
    while let Some(start) = remainder.find("{lambda-def:") {
        output.push_str(&remainder[..start]);
        let marker = &remainder[start..];
        let Some(end) = marker.find('}') else {
            output.push_str(marker);
            return output;
        };
        let label = marker[..end]
            .rsplit_once(':')
            .map_or(&marker[..=end], |(_, label)| label);
        output.push_str(label);
        remainder = &marker[end + 1..];
    }
    output.push_str(remainder);
    output
}

fn closure_for_body_span<'a>(
    body: &SourceSpan,
    closures: &'a [SemanticClosureSource],
    file_identities: &HashMap<PathBuf, PathBuf>,
) -> Option<&'a SemanticClosureSource> {
    closures
        .iter()
        .filter(|closure| {
            source_file_identity(file_identities, &closure.span.file)
                == source_file_identity(file_identities, &body.file)
                && span_contains(&closure.span, body)
        })
        .min_by_key(|closure| span_size(&closure.span))
}

fn rewrite_located_closures(
    value: &str,
    closures: &[SemanticClosureSource],
    file_identities: &HashMap<PathBuf, PathBuf>,
    rewrite: ClosureRewrite,
) -> String {
    let mut output = String::with_capacity(value.len());
    let mut remainder = value;
    loop {
        let located = ["{closure@", "{async closure@"]
            .into_iter()
            .filter_map(|prefix| remainder.find(prefix).map(|start| (start, prefix)))
            .min_by_key(|(start, _)| *start);
        let Some((start, prefix)) = located else {
            output.push_str(remainder);
            break;
        };
        output.push_str(&remainder[..start]);
        let located = &remainder[start..];
        let Some(end) = located.find('}') else {
            output.push_str(located);
            break;
        };
        let location = &located[prefix.len()..end];
        let replacement = parse_anonymous_location(location).and_then(|(file, line, column)| {
            closure_for_location(&file, line, column, closures, file_identities)
        });
        if let Some(closure) = replacement {
            output.push_str(match rewrite {
                ClosureRewrite::Identity => &closure.identity,
                ClosureRewrite::Display => &closure.lambda,
            });
        } else {
            output.push_str(&located[..=end]);
        }
        remainder = &located[end + 1..];
    }
    output
}

fn parse_anonymous_location(location: &str) -> Option<(PathBuf, usize, usize)> {
    let mut fields = location.rsplitn(5, ':');
    let _end_column = fields.next()?.trim().parse::<usize>().ok()?;
    let _end_line = fields.next()?.trim().parse::<usize>().ok()?;
    let start_column = fields.next()?.trim().parse::<usize>().ok()?;
    let start_line = fields.next()?.trim().parse::<usize>().ok()?;
    let file = PathBuf::from(fields.next()?.trim());
    Some((file, start_line, start_column))
}

fn closure_for_location<'a>(
    file: &Path,
    line: usize,
    column: usize,
    closures: &'a [SemanticClosureSource],
    file_identities: &HashMap<PathBuf, PathBuf>,
) -> Option<&'a SemanticClosureSource> {
    let candidates = closures
        .iter()
        .filter(|closure| {
            source_paths_match(file_identities, &closure.span.file, file)
                && closure.span.start_line == line
        })
        .collect::<Vec<_>>();
    let best_distance = candidates
        .iter()
        .map(|closure| closure.span.start_column.saturating_add(1).abs_diff(column))
        .min()?;
    let mut best = candidates.into_iter().filter(|closure| {
        closure.span.start_column.saturating_add(1).abs_diff(column) == best_distance
    });
    let closure = best.next()?;
    best.next().is_none().then_some(closure)
}

fn replace_closure_definition(value: &str, replacement: &str) -> String {
    let Some(start) = ["{closure#", "{async closure#"]
        .into_iter()
        .filter_map(|prefix| value.rfind(prefix))
        .max()
    else {
        return value.to_owned();
    };
    let Some(end) = value[start..].find('}').map(|end| start + end) else {
        return value.to_owned();
    };
    format!("{}{replacement}{}", &value[..start], &value[end + 1..])
}

fn closure_instance_display(lambda: &str, semantic: &str) -> String {
    let Some(start) = ["::{closure#", "::{async closure#"]
        .into_iter()
        .filter_map(|prefix| semantic.rfind(prefix))
        .max()
    else {
        return lambda.to_owned();
    };
    let parent = &semantic[..start];
    let Some(generic_start) = trailing_generic_arguments_start(parent) else {
        return lambda.to_owned();
    };
    format!("{}{}", lambda, &parent[generic_start..])
}

fn source_file_identities(
    syntax: &FileAnalysis,
    semantic: &SemanticProgram,
) -> HashMap<PathBuf, PathBuf> {
    let mut paths = HashSet::<PathBuf>::new();
    for function in &syntax.functions {
        paths.insert(function.span.file.clone());
        paths.extend(function.calls.iter().map(|call| call.span.file.clone()));
    }
    for function in &semantic.functions {
        paths.insert(function.body_span.file.clone());
        paths.extend(function.calls.iter().map(|call| call.span.file.clone()));
    }

    paths
        .into_iter()
        .map(|path| {
            let identity = path.canonicalize().unwrap_or_else(|_| {
                if path.is_absolute() {
                    path.clone()
                } else {
                    env::current_dir().map_or_else(|_| path.clone(), |root| root.join(&path))
                }
            });
            (path, identity)
        })
        .collect()
}

fn source_file_identity<'a>(identities: &'a HashMap<PathBuf, PathBuf>, path: &'a Path) -> &'a Path {
    identities.get(path).map_or(path, PathBuf::as_path)
}

fn source_paths_match(identities: &HashMap<PathBuf, PathBuf>, left: &Path, right: &Path) -> bool {
    let left = source_file_identity(identities, left);
    let right = source_file_identity(identities, right);
    left == right
        || (left.is_absolute() && !right.is_absolute() && left.ends_with(right))
        || (right.is_absolute() && !left.is_absolute() && right.ends_with(left))
}

fn best_function_template<'a>(
    functions: &'a [FunctionInfo],
    candidate_indices: &[usize],
    body_span: &SourceSpan,
) -> Option<&'a FunctionInfo> {
    candidate_indices
        .iter()
        .filter_map(|index| functions.get(*index))
        .filter(|function| span_contains(&function.span, body_span))
        .min_by_key(|function| span_size(&function.span))
}

fn best_semantic_call(
    syntax_call: &CallSite,
    semantic_calls: &[SemanticCall],
    claimed: &HashSet<usize>,
    file_identities: &HashMap<PathBuf, PathBuf>,
) -> Option<usize> {
    let syntax_name = call_syntax_name(syntax_call)?;

    semantic_calls
        .iter()
        .enumerate()
        .filter(|(index, call)| {
            if claimed.contains(index)
                || source_file_identity(file_identities, &syntax_call.span.file)
                    != source_file_identity(file_identities, &call.span.file)
                || !spans_overlap(&syntax_call.span, &call.span)
            {
                return false;
            }
            let definition_leaf = call
                .definition_name
                .rsplit("::")
                .next()
                .unwrap_or(&call.definition_name);
            definition_leaf == syntax_name || span_coordinates_equal(&syntax_call.span, &call.span)
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

fn call_syntax_name(call: &CallSite) -> Option<&str> {
    match &call.syntax {
        CallSyntax::Path(parts) => parts.last().map(String::as_str),
        CallSyntax::SelfMethod(method) | CallSyntax::Method { method, .. } => Some(method.as_str()),
    }
}

fn span_coordinates_equal(left: &SourceSpan, right: &SourceSpan) -> bool {
    left.start_line == right.start_line
        && left.start_column == right.start_column
        && left.end_line == right.end_line
        && left.end_column == right.end_column
}

fn semantic_symbol(name: String) -> SymbolId {
    SymbolId {
        language: LanguageId::new("rust"),
        module: Vec::new(),
        container: None,
        name,
    }
}

fn stable_instance_name(instance: Instance) -> String {
    let name = instance.name().to_string();
    let mut replacements = BTreeMap::<String, Option<String>>::new();
    collect_compiler_closure_replacements(&instance.args(), &mut replacements);
    replacements
        .into_iter()
        .filter_map(|(located, marker)| marker.map(|marker| (located, marker)))
        .fold(name, |name, (located, marker)| {
            name.replace(&located, &marker)
        })
}

fn collect_compiler_closure_replacements(
    arguments: &GenericArgs,
    replacements: &mut BTreeMap<String, Option<String>>,
) {
    for argument in &arguments.0 {
        if let GenericArgKind::Type(ty) = argument {
            collect_direct_closure_replacement(*ty, replacements);
        }
    }
}

fn collect_direct_closure_replacement(ty: Ty, replacements: &mut BTreeMap<String, Option<String>>) {
    // `rustc_public` still has unimplemented conversions for aliases and
    // coroutine closures. Inspecting every nested `TyKind` can therefore panic
    // on otherwise valid crates (Rayon contains such aliases). Ordinary
    // closures passed as function generics are direct arguments here, so only
    // open that known-safe shape.
    let rendered = ty.to_string();
    if !rendered.starts_with("{closure@") {
        return;
    }
    let TyKind::RigidTy(RigidTy::Closure(definition, _)) = ty.kind() else {
        return;
    };
    record_compiler_closure(&rendered, &definition.name().to_string(), replacements);
}

fn record_compiler_closure(
    rendered: &str,
    definition_name: &str,
    replacements: &mut BTreeMap<String, Option<String>>,
) {
    let Some(located) = located_closure_token(rendered) else {
        return;
    };
    let Some(marker) = compiler_closure_marker(definition_name) else {
        return;
    };
    replacements
        .entry(located.to_owned())
        .and_modify(|current| {
            if current.as_deref() != Some(&marker) {
                *current = None;
            }
        })
        .or_insert(Some(marker));
}

fn located_closure_token(value: &str) -> Option<&str> {
    let start = ["{closure@", "{async closure@"]
        .into_iter()
        .filter_map(|prefix| value.find(prefix))
        .min()?;
    let end = value[start..].find('}')? + start;
    Some(&value[start..=end])
}

fn compiler_closure_marker(definition_name: &str) -> Option<String> {
    let label = compiler_closure_label(definition_name)?;
    let mut hasher = Sha256::new();
    hasher.update(definition_name.as_bytes());
    let identity = format!("{:x}", hasher.finalize());
    Some(format!("{{lambda-def:{}:{label}}}", &identity[..12]))
}

fn compiler_closure_label(definition_name: &str) -> Option<String> {
    let (parent, ordinal) = ["::{closure#", "::{async closure#"]
        .into_iter()
        .find_map(|separator| definition_name.rsplit_once(separator))?;
    let ordinal = ordinal.strip_suffix('}')?.parse::<usize>().ok()? + 1;
    let parent = parent.rsplit("::").next().unwrap_or("closure");
    let parent = parent
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '_' {
                character
            } else {
                '_'
            }
        })
        .collect::<String>();
    let parent = if parent.trim_matches('_').is_empty() {
        "closure"
    } else {
        parent.trim_matches('_')
    };
    Some(format!("λ{parent}#{ordinal}"))
}

fn normalize_instance_key(name: &str) -> String {
    normalize_anonymous_type_locations(&name.replace("::<", "<"))
}

fn normalize_instance_display(name: &str, crate_name: &str) -> String {
    let without_crate = if crate_name.is_empty() {
        name.to_owned()
    } else {
        name.replace(&format!("{crate_name}::"), "")
    };
    let compact = normalize_anonymous_type_locations(&without_crate.replace("::<", "<"));
    collapse_trait_qualification(&compact)
}

fn normalize_anonymous_type_locations(value: &str) -> String {
    [
        ("{async block@", "{async block}"),
        ("{coroutine@", "{coroutine}"),
        ("{generator@", "{generator}"),
    ]
    .into_iter()
    .fold(value.to_owned(), |value, (prefix, replacement)| {
        replace_braced_location(&value, prefix, replacement)
    })
}

fn replace_braced_location(value: &str, prefix: &str, replacement: &str) -> String {
    let mut output = String::with_capacity(value.len());
    let mut remainder = value;
    while let Some(start) = remainder.find(prefix) {
        output.push_str(&remainder[..start]);
        let located = &remainder[start..];
        let Some(end) = located.find('}') else {
            output.push_str(located);
            return output;
        };
        output.push_str(replacement);
        remainder = &located[end + 1..];
    }
    output.push_str(remainder);
    output
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
    if let Some(arguments_start) = outer_call_arguments_start(label) {
        format!(
            "{}{}",
            semantic_callee(&label[..arguments_start], callee),
            &label[arguments_start..]
        )
    } else {
        semantic_callee(label, callee)
    }
}

fn semantic_callee(source: &str, semantic: &str) -> String {
    if semantic.starts_with('λ') {
        return semantic.to_owned();
    }
    if semantic.starts_with("dyn ") {
        return semantic.rsplit_once("::").map_or_else(
            || semantic.to_owned(),
            |(dispatch, method)| format!("{}::{method}", simplify_type_paths(dispatch)),
        );
    }

    if semantic.contains('<') {
        let source_segments = split_top_level_path(source);
        let semantic_segments = split_top_level_path(semantic);
        let keep = source_segments.len().min(semantic_segments.len()).max(1);
        return semantic_segments[semantic_segments.len().saturating_sub(keep)..]
            .iter()
            .map(|segment| simplify_type_paths(segment))
            .collect::<Vec<_>>()
            .join("::");
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

fn split_top_level_path(value: &str) -> Vec<&str> {
    let mut segments = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    let bytes = value.as_bytes();
    let mut index = 0usize;
    while index < bytes.len() {
        match bytes[index] {
            b'<' => depth += 1,
            b'>' => depth = depth.saturating_sub(1),
            b':' if depth == 0 && bytes.get(index + 1) == Some(&b':') => {
                segments.push(&value[start..index]);
                index += 1;
                start = index + 1;
            }
            _ => {}
        }
        index += 1;
    }
    segments.push(&value[start..]);
    segments
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
    simplify_type_paths(&normalize_anonymous_type_locations(
        &value.replace(&format!("{crate_name}::"), ""),
    ))
}

fn semantic_call_argument_types(call: &SemanticCall) -> Vec<String> {
    let is_closure = matches!(
        &call.target,
        SemanticCallTarget::Direct { display, .. }
            if display.starts_with('λ') || display.contains("{closure#")
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

impl LanguageBackend for RustBackend {
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
        analysis.source_files.insert(context.path.to_path_buf());
        analyze_items(context.path, context.module, &syntax.items, &mut analysis);
        Ok(analysis)
    }

    fn analyze_project(&self, context: &ProjectContext<'_>) -> FrontendResult<FileAnalysis> {
        let wrapper = context.driver_executable.ok_or_else(|| {
            std::io::Error::other("Rust project analysis requires a driver executable")
        })?;
        let session = match context.cache {
            Some(cache) => RustProjectSession::create_cached(
                cache.project_root,
                cache.endpoint,
                cache.verbose,
            )?,
            None => RustProjectSession::create()?,
        };
        analyze_semantic_project(context.root, wrapper, context.entries, &session)
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
    let closure_sources = closure_sources(block);
    let mut extractor = ClosureExtractor {
        file,
        module,
        owner,
        closure_sources: &closure_sources,
        functions: Vec::new(),
    };
    extractor.visit_block(block);
    analysis.functions.extend(extractor.functions);
}

struct ClosureExtractor<'a> {
    file: &'a Path,
    module: &'a [String],
    owner: &'a SymbolId,
    closure_sources: &'a HashMap<ClosureSpan, ClosureSource>,
    functions: Vec<FunctionInfo>,
}

impl<'ast> Visit<'ast> for ClosureExtractor<'_> {
    fn visit_expr_closure(&mut self, node: &'ast ExprClosure) {
        let source = self
            .closure_sources
            .get(&closure_span(node.span()))
            .cloned()
            .unwrap_or_else(|| ClosureSource::anonymous(self.functions.len()));
        let closure_name = format!("{{lambda:{}}}", source.identity);
        let lambda = source.lambda_name();
        let id = SymbolId {
            language: LanguageId::new("rust"),
            module: self.module.to_vec(),
            container: Some(self.owner.qualified_parts().join("::")),
            name: closure_name.clone(),
        };
        let mut calls = CallCollector {
            file: self.file,
            closure_sources: self.closure_sources,
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
                format!("{lambda}({})", parameters.join(", ")),
                format!("{lambda}({})", typed_parameters.join(", ")),
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
    let closure_sources = closure_sources(block);
    let mut collector = CallCollector {
        file,
        closure_sources: &closure_sources,
        calls: Vec::new(),
    };
    collector.visit_block(block);
    rewrite_symbolic_generic_calls(module, signature, &mut collector.calls);

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
    for parameter in &signature.generics.params {
        let (key, value) = match parameter {
            syn::GenericParam::Lifetime(parameter) => (
                parameter.lifetime.to_string(),
                parameter
                    .bounds
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" + "),
            ),
            syn::GenericParam::Type(parameter) => (
                parameter.ident.to_string(),
                parameter
                    .bounds
                    .iter()
                    .map(compact_tokens)
                    .collect::<Vec<_>>()
                    .join(" + "),
            ),
            syn::GenericParam::Const(parameter) => {
                (parameter.ident.to_string(), compact_tokens(&parameter.ty))
            }
        };
        analysis.facts.push(LanguageFact {
            subject: function.id.clone(),
            namespace: LanguageId::new("rust"),
            kind: "generic-parameter".to_owned(),
            key,
            value,
            span: source_span(file, parameter.span()),
        });
    }
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
    let generic_names = generic_parameter_labels(signature);
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

fn generic_parameter_labels(signature: &Signature) -> Vec<String> {
    let mut where_bounds = HashMap::<String, Vec<String>>::new();
    if let Some(where_clause) = &signature.generics.where_clause {
        for predicate in &where_clause.predicates {
            let syn::WherePredicate::Type(predicate) = predicate else {
                continue;
            };
            let key = compact_tokens(&predicate.bounded_ty);
            where_bounds
                .entry(key)
                .or_default()
                .extend(predicate.bounds.iter().map(compact_tokens));
        }
    }

    signature
        .generics
        .params
        .iter()
        .map(|parameter| match parameter {
            syn::GenericParam::Lifetime(parameter) => {
                let mut bounds = parameter
                    .bounds
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>();
                bounds.extend(
                    where_bounds
                        .get(&parameter.lifetime.to_string())
                        .cloned()
                        .unwrap_or_default(),
                );
                format_generic_parameter(parameter.lifetime.to_string(), bounds)
            }
            syn::GenericParam::Type(parameter) => {
                let name = parameter.ident.to_string();
                let mut bounds = parameter
                    .bounds
                    .iter()
                    .map(compact_tokens)
                    .collect::<Vec<_>>();
                bounds.extend(where_bounds.get(&name).cloned().unwrap_or_default());
                format_generic_parameter(name, bounds)
            }
            syn::GenericParam::Const(parameter) => {
                format!(
                    "const {}: {}",
                    parameter.ident,
                    compact_tokens(&parameter.ty)
                )
            }
        })
        .collect()
}

fn format_generic_parameter(name: String, mut bounds: Vec<String>) -> String {
    bounds.retain(|bound| !bound.is_empty());
    bounds.sort();
    bounds.dedup();
    if bounds.is_empty() {
        name
    } else {
        format!("{name}: {}", bounds.join(" + "))
    }
}

fn rewrite_symbolic_generic_calls(
    module: &[String],
    signature: &Signature,
    calls: &mut [CallSite],
) {
    let generic_bounds = generic_type_bounds(signature);
    if generic_bounds.is_empty() {
        return;
    }
    let receivers = signature
        .inputs
        .iter()
        .filter_map(|input| {
            let FnArg::Typed(argument) = input else {
                return None;
            };
            let parameter = simple_pattern_binding(&argument.pat)?;
            let generic = simple_generic_type(&argument.ty)?;
            generic_bounds
                .contains_key(&generic)
                .then_some((parameter, generic))
        })
        .collect::<HashMap<_, _>>();

    for call in calls {
        let CallSyntax::Method { receiver, method } = &call.syntax else {
            continue;
        };
        let Some(generic) = receivers.get(receiver) else {
            continue;
        };
        let bound = generic_bounds
            .get(generic)
            .and_then(|bounds| (bounds.len() == 1).then(|| bounds[0].clone()));
        call.target = CallTarget::Direct(SymbolId {
            language: LanguageId::new("rust"),
            module: module.to_vec(),
            container: Some(
                bound.map_or_else(|| generic.clone(), |bound| format!("{generic} as {bound}")),
            ),
            name: method.clone(),
        });
        call.label = replace_label_callee(&call.label, &format!("{generic}::{method}"));
    }
}

fn generic_type_bounds(signature: &Signature) -> HashMap<String, Vec<String>> {
    let mut result = HashMap::<String, Vec<String>>::new();
    for parameter in &signature.generics.params {
        let syn::GenericParam::Type(parameter) = parameter else {
            continue;
        };
        result.insert(
            parameter.ident.to_string(),
            parameter.bounds.iter().map(compact_tokens).collect(),
        );
    }
    if let Some(where_clause) = &signature.generics.where_clause {
        for predicate in &where_clause.predicates {
            let syn::WherePredicate::Type(predicate) = predicate else {
                continue;
            };
            let name = compact_tokens(&predicate.bounded_ty);
            if let Some(bounds) = result.get_mut(&name) {
                bounds.extend(predicate.bounds.iter().map(compact_tokens));
            }
        }
    }
    for bounds in result.values_mut() {
        bounds.sort();
        bounds.dedup();
    }
    result
}

fn simple_generic_type(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
            Some(path.path.segments[0].ident.to_string())
        }
        syn::Type::Reference(reference) => simple_generic_type(&reference.elem),
        syn::Type::Group(group) => simple_generic_type(&group.elem),
        syn::Type::Paren(paren) => simple_generic_type(&paren.elem),
        _ => None,
    }
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
    closure_sources: &'a HashMap<ClosureSpan, ClosureSource>,
    calls: Vec<CallSite>,
}

impl<'ast> Visit<'ast> for CallCollector<'_> {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        // MIR evaluates nested calls before their enclosing expression. Keep
        // the same order so an aggregate constructor such as `Some(f())`
        // cannot claim `f`'s semantic call span.
        visit::visit_expr_call(self, node);
        if let Some(parts) = callable_path(&node.func) {
            let syntax = CallSyntax::Path(parts);
            let span = source_span(self.file, node.span());
            self.calls.push(CallSite {
                id: CallSiteId::source(&syntax, &span),
                syntax,
                target: CallTarget::Unresolved,
                label: CallLabel::new(call_expression_label(node, self.closure_sources)),
                span,
            });
        }
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        visit::visit_expr_method_call(self, node);
        let method = node.method.to_string();
        let syntax = if is_self_expr(&node.receiver) {
            CallSyntax::SelfMethod(method)
        } else {
            CallSyntax::Method {
                receiver: receiver_name(&node.receiver),
                method,
            }
        };
        let span = source_span(self.file, node.span());
        self.calls.push(CallSite {
            id: CallSiteId::source(&syntax, &span),
            syntax,
            target: CallTarget::Unresolved,
            label: CallLabel::new(method_call_label(node, self.closure_sources)),
            span,
        });
    }

    // Nested closures and local functions own their calls; do not attribute them
    // to the enclosing function.
    fn visit_expr_closure(&mut self, _node: &'ast ExprClosure) {}

    fn visit_item_fn(&mut self, _node: &'ast ItemFn) {}
}

fn call_expression_label(
    node: &ExprCall,
    closure_sources: &HashMap<ClosureSpan, ClosureSource>,
) -> String {
    let function = compact_tokens(&node.func).replace("::<", "<");
    let (closure_types, arguments) = call_arguments(&node.args, closure_sources);
    let function = append_generic_arguments(&function, &closure_types);
    format!("{function}({})", arguments.join(", "))
}

fn method_call_label(
    node: &ExprMethodCall,
    closure_sources: &HashMap<ClosureSpan, ClosureSource>,
) -> String {
    let receiver = simple_receiver(&node.receiver)
        .then(|| compact_expression(&node.receiver, closure_sources));
    let generics = node
        .turbofish
        .as_ref()
        .map(compact_tokens)
        .unwrap_or_default()
        .replace("::<", "<");
    let (closure_types, arguments) = call_arguments(&node.args, closure_sources);
    let method = format!("{}{generics}", node.method);
    let callee = receiver.map_or(method.clone(), |receiver| format!("{receiver}.{method}"));
    let callee = append_generic_arguments(&callee, &closure_types);
    format!("{callee}({})", arguments.join(", "))
}

type ClosureSpan = (usize, usize, usize, usize);

#[derive(Clone, Debug)]
struct ClosureSource {
    ordinal: usize,
    binding: Option<String>,
    identity: String,
}

impl ClosureSource {
    fn anonymous(ordinal: usize) -> Self {
        Self {
            ordinal,
            binding: None,
            identity: format!("fallback-{ordinal}"),
        }
    }

    fn lambda_name(&self) -> String {
        self.binding.as_ref().map_or_else(
            || format!("λ#{}", self.ordinal + 1),
            |name| format!("λ{name}"),
        )
    }
}

fn closure_span(span: Span) -> ClosureSpan {
    let start = span.start();
    let end = span.end();
    (start.line, start.column, end.line, end.column)
}

fn closure_sources(block: &syn::Block) -> HashMap<ClosureSpan, ClosureSource> {
    let mut collector = ClosureOrdinalCollector::default();
    collector.visit_block(block);
    collector.sources
}

#[derive(Default)]
struct ClosureOrdinalCollector {
    sources: HashMap<ClosureSpan, ClosureSource>,
    bindings: HashMap<ClosureSpan, String>,
    identity_counts: HashMap<String, usize>,
}

impl<'ast> Visit<'ast> for ClosureOrdinalCollector {
    fn visit_local(&mut self, node: &'ast syn::Local) {
        if let Some(initializer) = &node.init
            && let Some(closure) = direct_closure_expression(&initializer.expr)
            && let Some(binding) = simple_pattern_binding(&node.pat)
        {
            self.bindings.insert(closure_span(closure.span()), binding);
        }
        visit::visit_local(self, node);
    }

    fn visit_expr_closure(&mut self, node: &'ast ExprClosure) {
        let span = closure_span(node.span());
        let ordinal = self.sources.len();
        let base_identity = closure_structural_identity(node);
        let occurrence = self
            .identity_counts
            .entry(base_identity.clone())
            .or_default();
        let identity = if *occurrence == 0 {
            base_identity
        } else {
            format!("{base_identity}-{}", *occurrence + 1)
        };
        *occurrence += 1;
        self.sources.insert(
            span,
            ClosureSource {
                ordinal,
                binding: self.bindings.get(&span).cloned(),
                identity,
            },
        );
        visit::visit_expr_closure(self, node);
    }

    fn visit_item_fn(&mut self, _node: &'ast ItemFn) {}
}

fn closure_structural_identity(node: &ExprClosure) -> String {
    let signature = format!(
        "{}:{}:{}:{}",
        node.asyncness.is_some(),
        node.movability.is_some(),
        node.capture.is_some(),
        node.inputs
            .iter()
            .map(compact_tokens)
            .collect::<Vec<_>>()
            .join(",")
    );
    let mut hasher = Sha256::new();
    hasher.update(signature.as_bytes());
    format!("{:x}", hasher.finalize())[..12].to_owned()
}

struct ClosureLabelRedactor<'a> {
    closure_sources: &'a HashMap<ClosureSpan, ClosureSource>,
    used: Vec<(String, String)>,
}

impl VisitMut for ClosureLabelRedactor<'_> {
    fn visit_expr_mut(&mut self, node: &mut Expr) {
        let Expr::Closure(closure) = node else {
            visit_mut::visit_expr_mut(self, node);
            return;
        };
        let Some(source) = self
            .closure_sources
            .get(&closure_span(closure.span()))
            .cloned()
        else {
            return;
        };
        let marker = format!("__diffkit_closure_placeholder_{}", source.ordinal);
        self.used.push((marker.clone(), source.lambda_name()));
        let ident = syn::Ident::new(&marker, closure.span());
        *node = Expr::Path(syn::ExprPath {
            attrs: Vec::new(),
            qself: None,
            path: syn::Path::from(ident),
        });
    }
}

fn compact_expression(
    expression: &Expr,
    closure_sources: &HashMap<ClosureSpan, ClosureSource>,
) -> String {
    let mut expression = expression.clone();
    let mut redactor = ClosureLabelRedactor {
        closure_sources,
        used: Vec::new(),
    };
    redactor.visit_expr_mut(&mut expression);
    let mut rendered = compact_tokens(&expression);
    for (marker, lambda) in redactor.used {
        rendered = rendered.replace(&marker, &lambda);
    }
    rendered
}

fn call_argument_label(
    expression: &Expr,
    closure_sources: &HashMap<ClosureSpan, ClosureSource>,
) -> String {
    let rendered = compact_expression(expression, closure_sources);
    if rendered.chars().count() <= 96 {
        rendered
    } else {
        "…".to_owned()
    }
}

fn call_arguments(
    arguments: &syn::punctuated::Punctuated<Expr, syn::Token![,]>,
    closure_sources: &HashMap<ClosureSpan, ClosureSource>,
) -> (Vec<String>, Vec<String>) {
    let mut closure_types = Vec::new();
    let mut values = Vec::new();
    for argument in arguments {
        if let Some(source) = closure_source_for_expression(argument, closure_sources) {
            closure_types.push(source.lambda_name());
        } else {
            values.push(call_argument_label(argument, closure_sources));
        }
    }
    (closure_types, values)
}

fn closure_source_for_expression<'a>(
    expression: &Expr,
    closure_sources: &'a HashMap<ClosureSpan, ClosureSource>,
) -> Option<&'a ClosureSource> {
    if let Some(closure) = direct_closure_expression(expression) {
        return closure_sources.get(&closure_span(closure.span()));
    }
    let Expr::Path(path) = expression else {
        return None;
    };
    let binding = path.path.get_ident()?.to_string();
    closure_sources
        .values()
        .find(|source| source.binding.as_deref() == Some(binding.as_str()))
}

fn direct_closure_expression(expression: &Expr) -> Option<&ExprClosure> {
    match expression {
        Expr::Closure(closure) => Some(closure),
        Expr::Group(group) => direct_closure_expression(&group.expr),
        Expr::Paren(paren) => direct_closure_expression(&paren.expr),
        _ => None,
    }
}

fn simple_pattern_binding(pattern: &Pat) -> Option<String> {
    match pattern {
        Pat::Ident(identifier) => Some(identifier.ident.to_string()),
        Pat::Type(typed) => simple_pattern_binding(&typed.pat),
        _ => None,
    }
}

fn append_generic_arguments(callee: &str, additions: &[String]) -> String {
    if additions.is_empty() {
        return callee.to_owned();
    }
    let additions = additions.join(", ");
    let Some(start) = trailing_generic_arguments_start(callee) else {
        return format!("{callee}<{additions}>");
    };
    let existing = &callee[start + 1..callee.len() - 1];
    let separator = if existing.is_empty() { "" } else { ", " };
    format!("{}<{existing}{separator}{additions}>", &callee[..start])
}

fn trailing_generic_arguments_start(value: &str) -> Option<usize> {
    if !value.ends_with('>') {
        return None;
    }
    let mut depth = 0usize;
    for (index, character) in value.char_indices().rev() {
        match character {
            '>' => depth += 1,
            '<' => {
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

fn simple_receiver(expression: &Expr) -> bool {
    match expression {
        Expr::Path(_) => true,
        Expr::Field(field) => simple_receiver(&field.base),
        Expr::Index(index) => simple_receiver(&index.expr),
        Expr::Paren(paren) => simple_receiver(&paren.expr),
        Expr::Group(group) => simple_receiver(&group.expr),
        Expr::Reference(reference) => simple_receiver(&reference.expr),
        Expr::Unary(unary) => simple_receiver(&unary.expr),
        _ => false,
    }
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
        let frontend = RustBackend;
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
    fn closure_arguments_are_labels_not_serialized_bodies() {
        let source = r#"
            fn run(values: &[String]) {
                values
                    .iter()
                    .filter_map(|value| {
                        parse(value);
                        Some(value)
                    })
                    .collect::<Vec<_>>();
            }
            fn parse(_: &String) {}
        "#;
        let frontend = RustBackend;
        let analysis = frontend
            .analyze_file(
                &FileContext {
                    path: Path::new("src/lib.rs"),
                    module: &[],
                },
                source,
            )
            .unwrap();

        let run = analysis
            .functions
            .iter()
            .find(|function| function.label.default.starts_with("run("))
            .unwrap();
        let labels = run
            .calls
            .iter()
            .map(|call| call.label.default.as_str())
            .collect::<Vec<_>>();

        assert_eq!(
            labels,
            ["values.iter()", "filter_map<λ#1>()", "collect<Vec<_>>()",]
        );
        assert!(labels.iter().all(|label| !label.contains("parse(value)")));

        let closure = analysis
            .functions
            .iter()
            .find(|function| function.label.default.starts_with("λ#1("))
            .unwrap();
        assert!(
            closure
                .calls
                .iter()
                .any(|call| call.label.default == "parse(value)")
        );
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
    fn rustc_public_skips_higher_ranked_vtables() {
        let directory = std::env::temp_dir().join(format!(
            "diffkit-rustc-public-bound-vtable-{}",
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("input.rs");
        fs::write(
            &path,
            r#"
                use std::{
                    any::{Any, TypeId},
                    collections::HashMap,
                    sync::Arc,
                };

                pub fn populate() {
                    let mut values: HashMap<TypeId, Arc<dyn Any + Send + Sync>> = HashMap::new();
                    values.insert(TypeId::of::<u8>(), Arc::new(1_u8));
                    values.reserve(1);
                }
            "#,
        )
        .unwrap();

        let analysis = analyze_semantic_file(&path).unwrap();

        assert!(
            analysis
                .functions
                .iter()
                .any(|function| function.label.default.starts_with("populate("))
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn rustc_public_does_not_open_opaque_instance_arguments() {
        let directory = std::env::temp_dir().join(format!(
            "diffkit-rustc-public-opaque-argument-{}",
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("input.rs");
        fs::write(
            &path,
            r#"
                fn make() -> impl Copy { 1_u8 }
                fn consume<T: Copy>(_value: T) {}
                pub fn run() { consume(make()); }
            "#,
        )
        .unwrap();

        let analysis = analyze_semantic_file(&path).unwrap();

        assert!(
            analysis
                .functions
                .iter()
                .any(|function| function.label.default.starts_with("run("))
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn semantic_analysis_omits_enum_variant_constructors() {
        let directory = std::env::temp_dir().join(format!(
            "diffkit-rustc-public-constructors-{}",
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("input.rs");
        let source = r#"
            pub struct Node;
            pub fn root(before: Option<&Node>, after: Option<&Node>) -> Option<()> {
                match (before, after) {
                    (Some(before), Some(after)) => Some(inner(Some(before), Some(after))),
                    _ => None,
                }
            }
            fn inner(_: Option<&Node>, _: Option<&Node>) {}
            pub fn is_json(value: Option<&str>) -> bool { value == Some("json") }
        "#;
        fs::write(&path, source).unwrap();

        let analysis = analyze_semantic_file(&path).unwrap();
        let root = analysis
            .functions
            .iter()
            .find(|function| function.label.default.starts_with("root("))
            .unwrap();
        let calls = root
            .calls
            .iter()
            .map(|call| call.label.default.as_str())
            .collect::<Vec<_>>();

        assert_eq!(calls, ["inner(Some(before), Some(after))"]);
        let is_json = analysis
            .functions
            .iter()
            .find(|function| function.label.default.starts_with("is_json("))
            .unwrap();
        assert!(is_json.calls.is_empty(), "{:#?}", is_json.calls);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn semantic_labels_do_not_expose_external_inferred_generics_or_closure_bodies() {
        let directory = std::env::temp_dir().join(format!(
            "diffkit-rustc-public-call-labels-{}",
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("input.rs");
        fs::write(
            &path,
            r#"
                pub fn run(values: &[String]) -> Vec<usize> {
                    values
                        .iter()
                        .filter_map(|value| value.parse::<usize>().ok())
                        .collect()
                }
            "#,
        )
        .unwrap();

        let analysis = analyze_semantic_file(&path).unwrap();
        let run = analysis
            .functions
            .iter()
            .find(|function| function.label.default.starts_with("run("))
            .unwrap();
        let labels = run
            .calls
            .iter()
            .map(|call| call.label.default.as_str())
            .collect::<Vec<_>>();

        assert_eq!(labels, ["values.iter()", "filter_map<λ#1>()", "collect()"]);
        assert!(
            labels
                .iter()
                .all(|label| !label.contains("impl ") && !label.contains("|value|"))
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

    #[test]
    fn specialization_consumes_duplicate_normalized_instances() {
        let span = SourceSpan {
            file: PathBuf::from("src/lib.rs"),
            start_line: 1,
            start_column: 1,
            start_byte: None,
            end_line: 1,
            end_column: 1,
            end_byte: None,
        };
        let function = || RawSemanticFunction {
            key: "crate::duplicate".to_owned(),
            display: "duplicate".to_owned(),
            definition_name: "crate::duplicate".to_owned(),
            body_span: span.clone(),
            calls: Vec::new(),
            constructor_spans: Vec::new(),
            constructor_names: Vec::new(),
            parameter_types: Vec::new(),
        };

        let specialized =
            specialize_semantic_functions(&[function(), function()], &[], &HashMap::new(), "crate");

        assert_eq!(specialized.len(), 1);
        assert_eq!(specialized[0].key, "crate::duplicate");
    }

    #[test]
    fn closure_locations_survive_until_the_source_lambda_mapping() {
        assert_eq!(
            normalize_instance_key("core::result::Result::map::<{closure@src/lib.rs:10:4: 10:12}>"),
            "core::result::Result::map<{closure@src/lib.rs:10:4: 10:12}>"
        );
        assert_eq!(
            normalize_type_display(
                "diffkit::Runner<{async block@src/lib.rs:20:8: 24:9}>",
                "diffkit"
            ),
            "Runner<{async block}>"
        );
    }
}
