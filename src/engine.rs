use std::collections::{BTreeSet, HashMap};
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};

use crate::DiffkitResult;
use crate::diff::{
    DiffNode, collapse_unchanged_subtrees, diff_optional, tree_has_changes, truncate_diff_tree,
};
use crate::graph::ProgramGraph;
use crate::language::ocaml::OcamlFrontend;
use crate::language::rust::{
    RustProjectSession, analyze_semantic_file_with_entries, analyze_semantic_project,
    analyze_semantic_source,
};
use crate::language::{FileContext, LanguageBackend, ProjectContext};
use crate::model::{CallNode, FileAnalysis, SymbolId};

static CARGO_SOURCE_LAYOUTS: OnceLock<Mutex<HashMap<PathBuf, Option<CargoSourceLayout>>>> =
    OnceLock::new();

#[derive(Clone)]
struct CargoSourceLayout {
    package_roots: Vec<PathBuf>,
    target_sources: Vec<PathBuf>,
}

#[derive(Clone, Debug)]
pub struct DiffOptions {
    pub entries: Vec<String>,
    pub max_depth: usize,
}

impl Default for DiffOptions {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
            max_depth: 8,
        }
    }
}

#[derive(Clone, Debug)]
pub struct EntryDiff {
    pub entry: SymbolId,
    pub tree: DiffNode,
}

#[derive(Clone, Debug)]
pub struct DiffReport {
    pub language: String,
    pub before: String,
    pub after: String,
    pub trees: Vec<EntryDiff>,
    pub message: Option<String>,
    pub analyzed_files: BTreeSet<PathBuf>,
    pub diagnostics: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct EntryTree {
    pub entry: SymbolId,
    pub tree: CallNode,
}

#[derive(Clone, Debug)]
pub struct TreeReport {
    pub language: String,
    pub source: String,
    pub trees: Vec<EntryTree>,
    pub message: Option<String>,
    pub diagnostics: Vec<String>,
}

pub fn rustdiff_sources(
    before_name: impl Into<String>,
    before_source: &str,
    after_name: impl Into<String>,
    after_source: &str,
    options: &DiffOptions,
) -> DiffkitResult<DiffReport> {
    let before = graph_from_files([analyze_semantic_source(before_source, &options.entries)?])?;
    let after = graph_from_files([analyze_semantic_source(after_source, &options.entries)?])?;
    build_report(
        "rust".to_owned(),
        before_name.into(),
        after_name.into(),
        &before,
        &after,
        options,
    )
}

pub fn rustdiff_paths(
    before_path: &Path,
    after_path: &Path,
    options: &DiffOptions,
) -> DiffkitResult<DiffReport> {
    let before = graph_from_files([analyze_semantic_file_with_entries(
        before_path,
        &options.entries,
    )?])?;
    let after = graph_from_files([analyze_semantic_file_with_entries(
        after_path,
        &options.entries,
    )?])?;
    build_report(
        "rust".to_owned(),
        before_path.display().to_string(),
        after_path.display().to_string(),
        &before,
        &after,
        options,
    )
}

pub fn rustdiff_project_paths(
    before_root: &Path,
    after_root: &Path,
    wrapper_executable: &Path,
    options: &DiffOptions,
) -> DiffkitResult<DiffReport> {
    let session = RustProjectSession::create()?;
    rustdiff_project_paths_with_session(
        before_root,
        after_root,
        wrapper_executable,
        options,
        &session,
    )
}

pub fn rustdiff_project_paths_cached(
    before_root: &Path,
    after_root: &Path,
    cache_project_root: &Path,
    wrapper_executable: &Path,
    options: &DiffOptions,
    verbose: bool,
) -> DiffkitResult<DiffReport> {
    let before_session =
        RustProjectSession::create_cached(cache_project_root, "git-before", verbose)?;
    let after_session =
        RustProjectSession::create_cached(cache_project_root, "git-after", verbose)?;
    rustdiff_project_paths_with_sessions(
        before_root,
        after_root,
        wrapper_executable,
        options,
        &before_session,
        &after_session,
    )
}

fn rustdiff_project_paths_with_session(
    before_root: &Path,
    after_root: &Path,
    wrapper_executable: &Path,
    options: &DiffOptions,
    session: &RustProjectSession,
) -> DiffkitResult<DiffReport> {
    rustdiff_project_paths_with_sessions(
        before_root,
        after_root,
        wrapper_executable,
        options,
        session,
        session,
    )
}

fn rustdiff_project_paths_with_sessions(
    before_root: &Path,
    after_root: &Path,
    wrapper_executable: &Path,
    options: &DiffOptions,
    before_session: &RustProjectSession,
    after_session: &RustProjectSession,
) -> DiffkitResult<DiffReport> {
    let (before, after) = if std::ptr::eq(before_session, after_session) {
        (
            rust_project_graph(
                before_root,
                wrapper_executable,
                &options.entries,
                before_session,
            )?,
            rust_project_graph(
                after_root,
                wrapper_executable,
                &options.entries,
                after_session,
            )?,
        )
    } else {
        rust_project_graphs_parallel(
            before_root,
            after_root,
            wrapper_executable,
            &options.entries,
            before_session,
            after_session,
        )?
    };
    build_report(
        "rust".to_owned(),
        before_root.display().to_string(),
        after_root.display().to_string(),
        &before,
        &after,
        options,
    )
}

pub fn rustdiff_project_files(
    before_file: &Path,
    after_file: &Path,
    wrapper_executable: &Path,
    options: &DiffOptions,
    verbose: bool,
) -> DiffkitResult<Option<DiffReport>> {
    let before_root = find_cargo_root(before_file)?;
    let after_root = find_cargo_root(after_file)?;
    let before_session = RustProjectSession::create_cached(&before_root, "file-before", verbose)?;
    let after_session = RustProjectSession::create_cached(&after_root, "file-after", verbose)?;
    let (before, after) = rust_project_graphs_parallel(
        &before_root,
        &after_root,
        wrapper_executable,
        &options.entries,
        &before_session,
        &after_session,
    )?;
    if !before.analyzes_file(before_file) && !after.analyzes_file(after_file) {
        return Ok(None);
    }
    build_file_report(
        "rust".to_owned(),
        before_file,
        after_file,
        &before,
        &after,
        options,
    )
    .map(Some)
}

pub fn ocamldiff_sources(
    before_name: impl Into<String>,
    before_source: &str,
    after_name: impl Into<String>,
    after_source: &str,
    options: &DiffOptions,
) -> DiffkitResult<DiffReport> {
    let frontend = OcamlFrontend;
    diff_sources(
        before_name.into(),
        before_source,
        after_name.into(),
        after_source,
        &frontend,
        options,
    )
}

pub fn ocamldiff_paths(
    before_path: &Path,
    after_path: &Path,
    options: &DiffOptions,
) -> DiffkitResult<DiffReport> {
    let frontend = OcamlFrontend;
    let before = ocaml_optional_project_graph(before_path, &frontend)?;
    let after = ocaml_optional_project_graph(after_path, &frontend)?;
    build_report(
        frontend.language().0,
        before_path.display().to_string(),
        after_path.display().to_string(),
        &before,
        &after,
        options,
    )
}

pub fn ocamldiff_project_files(
    before_file: &Path,
    after_file: &Path,
    options: &DiffOptions,
) -> DiffkitResult<DiffReport> {
    let frontend = OcamlFrontend;
    let before_root = find_ocaml_root(before_file);
    let after_root = find_ocaml_root(after_file);
    let before = ocaml_project_graph(&before_root, &frontend)?;
    let after = ocaml_project_graph(&after_root, &frontend)?;
    build_file_report(
        frontend.language().0,
        before_file,
        after_file,
        &before,
        &after,
        options,
    )
}

pub fn rusttree_path(path: &Path, options: &DiffOptions) -> DiffkitResult<TreeReport> {
    let graph = graph_from_files([analyze_semantic_file_with_entries(path, &options.entries)?])?;
    build_tree_report("rust", path, &graph, options)
}

pub fn rusttree_project_file(
    path: &Path,
    wrapper_executable: &Path,
    options: &DiffOptions,
    verbose: bool,
) -> DiffkitResult<Option<TreeReport>> {
    let root = find_cargo_root(path)?;
    let session = RustProjectSession::create_cached(&root, "tree", verbose)?;
    let graph = rust_project_graph(&root, wrapper_executable, &options.entries, &session)?;
    if !graph.analyzes_file(path) {
        return Ok(None);
    }
    build_tree_report("rust", path, &graph, options).map(Some)
}

pub fn ocamltree_path(path: &Path, options: &DiffOptions) -> DiffkitResult<TreeReport> {
    let frontend = OcamlFrontend;
    let graph = load_path(path, &frontend)?;
    build_tree_report("ocaml", path, &graph, options)
}

pub fn ocamltree_project_file(path: &Path, options: &DiffOptions) -> DiffkitResult<TreeReport> {
    let frontend = OcamlFrontend;
    let root = find_ocaml_root(path);
    let graph = ocaml_project_graph(&root, &frontend)?;
    build_tree_report("ocaml", path, &graph, options)
}

fn diff_sources(
    before_name: String,
    before_source: &str,
    after_name: String,
    after_source: &str,
    frontend: &impl LanguageBackend,
    options: &DiffOptions,
) -> DiffkitResult<DiffReport> {
    let empty_module = Vec::new();
    let before_analysis = frontend.analyze_file(
        &FileContext {
            path: Path::new(&before_name),
            module: &empty_module,
        },
        before_source,
    )?;
    let after_analysis = frontend.analyze_file(
        &FileContext {
            path: Path::new(&after_name),
            module: &empty_module,
        },
        after_source,
    )?;
    let before = graph_from_files([before_analysis])?;
    let after = graph_from_files([after_analysis])?;
    build_report(
        frontend.language().0,
        before_name,
        after_name,
        &before,
        &after,
        options,
    )
}

fn build_report(
    language: String,
    before_name: String,
    after_name: String,
    before: &ProgramGraph,
    after: &ProgramGraph,
    options: &DiffOptions,
) -> DiffkitResult<DiffReport> {
    let candidate_entries = if options.entries.is_empty() {
        ordered_root_union(before, after)
    } else {
        resolve_explicit_entries(before, after, &options.entries)?
            .into_iter()
            .collect()
    };

    let trees = changed_entries(before, after, candidate_entries, options.max_depth);
    let mut report = report_from_trees(language, before_name, after_name, trees);
    report.analyzed_files.extend(before.source_files());
    report.analyzed_files.extend(after.source_files());
    report.diagnostics = comparison_diagnostics(before, after);
    Ok(report)
}

fn build_file_report(
    language: String,
    before_path: &Path,
    after_path: &Path,
    before: &ProgramGraph,
    after: &ProgramGraph,
    options: &DiffOptions,
) -> DiffkitResult<DiffReport> {
    let candidate_entries = if options.entries.is_empty() {
        ordered_file_root_union(before, after, before_path, after_path)
    } else {
        resolve_explicit_file_entries(before, after, before_path, after_path, &options.entries)?
            .into_iter()
            .collect()
    };
    let trees = candidate_entries
        .into_iter()
        .filter_map(|entry| {
            let before_tree = before.build_call_tree_in_file(&entry, usize::MAX, Some(before_path));
            let after_tree = after.build_call_tree_in_file(&entry, usize::MAX, Some(after_path));
            let mut tree = diff_optional(before_tree.as_ref(), after_tree.as_ref())?;
            tree_has_changes(&tree).then(|| {
                collapse_unchanged_subtrees(&mut tree);
                truncate_diff_tree(&mut tree, options.max_depth);
                EntryDiff { entry, tree }
            })
        })
        .collect();
    let mut report = report_from_trees(
        language,
        before_path.display().to_string(),
        after_path.display().to_string(),
        trees,
    );
    report.analyzed_files.extend(before.source_files());
    report.analyzed_files.extend(after.source_files());
    report.diagnostics = comparison_diagnostics(before, after);
    Ok(report)
}

fn build_tree_report(
    language: &str,
    path: &Path,
    graph: &ProgramGraph,
    options: &DiffOptions,
) -> DiffkitResult<TreeReport> {
    let entries = if options.entries.is_empty() {
        graph.roots_in_file(path).into_iter().collect::<Vec<_>>()
    } else {
        let mut resolved = Vec::new();
        for entry in &options.entries {
            let matches = graph
                .resolve_entries_in_file(entry, path)
                .map_err(std::io::Error::other)?;
            if matches.is_empty() {
                return Err(std::io::Error::other(format!(
                    "entry not found in selected file: {entry}"
                ))
                .into());
            }
            resolved.extend(matches);
        }
        resolved
    };

    let trees = entries
        .into_iter()
        .filter_map(|entry| {
            graph
                .build_call_tree_in_file(&entry, options.max_depth, Some(path))
                .map(|tree| EntryTree { entry, tree })
        })
        .collect::<Vec<_>>();
    let message = trees
        .is_empty()
        .then(|| format!("No {language} call trees in {}.", path.display()));
    Ok(TreeReport {
        language: language.to_owned(),
        source: path.display().to_string(),
        trees,
        message,
        diagnostics: graph.resolution_diagnostics(),
    })
}

fn ordered_root_union(before: &ProgramGraph, after: &ProgramGraph) -> Vec<SymbolId> {
    let before_roots = before.inferred_roots();
    let after_roots = after.inferred_roots();
    let mut common = before_roots
        .intersection(&after_roots)
        .cloned()
        .collect::<Vec<_>>();
    let mut removed = before_roots
        .difference(&after_roots)
        .cloned()
        .collect::<Vec<_>>();
    let mut added = after_roots
        .difference(&before_roots)
        .cloned()
        .collect::<Vec<_>>();
    sort_by_source(&mut common, before);
    sort_by_source(&mut removed, before);
    sort_by_source(&mut added, after);
    common.extend(removed);
    common.extend(added);
    common
}

fn ordered_file_root_union(
    before: &ProgramGraph,
    after: &ProgramGraph,
    before_path: &Path,
    after_path: &Path,
) -> Vec<SymbolId> {
    let before_roots = before.roots_in_file(before_path);
    let after_roots = after.roots_in_file(after_path);
    let mut common = before_roots
        .intersection(&after_roots)
        .cloned()
        .collect::<Vec<_>>();
    let mut removed = before_roots
        .difference(&after_roots)
        .cloned()
        .collect::<Vec<_>>();
    let mut added = after_roots
        .difference(&before_roots)
        .cloned()
        .collect::<Vec<_>>();
    sort_by_source(&mut common, before);
    sort_by_source(&mut removed, before);
    sort_by_source(&mut added, after);
    common.extend(removed);
    common.extend(added);
    common
}

fn sort_by_source(symbols: &mut [SymbolId], graph: &ProgramGraph) {
    symbols.sort_by_key(|symbol| {
        graph.functions().get(symbol).map_or_else(
            || (PathBuf::new(), usize::MAX, usize::MAX, symbol.clone()),
            |function| {
                (
                    function.span.file.clone(),
                    function.span.start_line,
                    function.span.start_column,
                    symbol.clone(),
                )
            },
        )
    });
}

fn report_from_trees(
    language: String,
    before: String,
    after: String,
    trees: Vec<EntryDiff>,
) -> DiffReport {
    let message = trees
        .is_empty()
        .then(|| format!("No {language} call changes between {before} and {after}."));
    DiffReport {
        language,
        before,
        after,
        trees,
        message,
        analyzed_files: BTreeSet::new(),
        diagnostics: Vec::new(),
    }
}

fn comparison_diagnostics(before: &ProgramGraph, after: &ProgramGraph) -> Vec<String> {
    before
        .resolution_diagnostics()
        .into_iter()
        .map(|diagnostic| format!("before: {diagnostic}"))
        .chain(
            after
                .resolution_diagnostics()
                .into_iter()
                .map(|diagnostic| format!("after: {diagnostic}")),
        )
        .collect()
}

fn resolve_explicit_entries(
    before: &ProgramGraph,
    after: &ProgramGraph,
    entries: &[String],
) -> DiffkitResult<BTreeSet<SymbolId>> {
    let mut resolved = BTreeSet::new();
    for entry in entries {
        let before_entries = before
            .resolve_entries(entry)
            .map_err(std::io::Error::other)?;
        let after_entries = after
            .resolve_entries(entry)
            .map_err(std::io::Error::other)?;
        if before_entries.is_empty() && after_entries.is_empty() {
            return Err(std::io::Error::other(format!("entry not found: {entry}")).into());
        }
        resolved.extend(before_entries);
        resolved.extend(after_entries);
    }
    Ok(resolved)
}

fn resolve_explicit_file_entries(
    before: &ProgramGraph,
    after: &ProgramGraph,
    before_path: &Path,
    after_path: &Path,
    entries: &[String],
) -> DiffkitResult<BTreeSet<SymbolId>> {
    let mut resolved = BTreeSet::new();
    for entry in entries {
        let before_entries = before
            .resolve_entries_in_file(entry, before_path)
            .map_err(std::io::Error::other)?;
        let after_entries = after
            .resolve_entries_in_file(entry, after_path)
            .map_err(std::io::Error::other)?;
        if before_entries.is_empty() && after_entries.is_empty() {
            return Err(std::io::Error::other(format!(
                "entry not found in selected file: {entry}"
            ))
            .into());
        }
        resolved.extend(before_entries);
        resolved.extend(after_entries);
    }
    Ok(resolved)
}

fn changed_entries(
    before: &ProgramGraph,
    after: &ProgramGraph,
    entries: impl IntoIterator<Item = SymbolId>,
    max_depth: usize,
) -> Vec<EntryDiff> {
    entries
        .into_iter()
        .filter_map(|entry| {
            let before_tree = before.build_call_tree(&entry, usize::MAX);
            let after_tree = after.build_call_tree(&entry, usize::MAX);
            let mut tree = diff_optional(before_tree.as_ref(), after_tree.as_ref())?;
            tree_has_changes(&tree).then(|| {
                collapse_unchanged_subtrees(&mut tree);
                truncate_diff_tree(&mut tree, max_depth);
                EntryDiff { entry, tree }
            })
        })
        .collect()
}

fn load_path(path: &Path, frontend: &impl LanguageBackend) -> DiffkitResult<ProgramGraph> {
    if !path.exists() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("path does not exist: {}", path.display()),
        )
        .into());
    }

    let files = collect_source_files(path, frontend.extensions())?;
    if files.is_empty() {
        return Err(std::io::Error::other(format!(
            "no {} source files found under {}",
            frontend.language(),
            path.display()
        ))
        .into());
    }

    let single_file = path.is_file();
    let root = if single_file {
        path.parent().unwrap_or_else(|| Path::new("."))
    } else {
        path
    };
    let mut analyses = Vec::with_capacity(files.len());
    for file in files {
        let source = fs::read_to_string(&file)?;
        let module = if single_file {
            Vec::new()
        } else {
            module_path(root, &file)
        };
        analyses.push(frontend.analyze_file(
            &FileContext {
                path: &file,
                module: &module,
            },
            &source,
        )?);
    }
    graph_from_files(analyses)
}

fn graph_from_files(files: impl IntoIterator<Item = FileAnalysis>) -> DiffkitResult<ProgramGraph> {
    ProgramGraph::from_files(files)
        .map_err(std::io::Error::other)
        .map_err(Into::into)
}

fn rust_project_graph(
    root: &Path,
    wrapper_executable: &Path,
    entries: &[String],
    session: &RustProjectSession,
) -> DiffkitResult<ProgramGraph> {
    if !root.join("Cargo.toml").is_file() {
        return graph_from_files(std::iter::empty());
    }
    graph_from_files([analyze_semantic_project(
        root,
        wrapper_executable,
        entries,
        session,
    )?])
}

fn rust_project_graphs_parallel(
    before_root: &Path,
    after_root: &Path,
    wrapper_executable: &Path,
    entries: &[String],
    before_session: &RustProjectSession,
    after_session: &RustProjectSession,
) -> DiffkitResult<(ProgramGraph, ProgramGraph)> {
    std::thread::scope(|scope| {
        let before = scope
            .spawn(|| rust_project_graph(before_root, wrapper_executable, entries, before_session));
        let after = scope
            .spawn(|| rust_project_graph(after_root, wrapper_executable, entries, after_session));
        let before = before
            .join()
            .map_err(|_| std::io::Error::other("before Rust analysis worker panicked"))??;
        let after = after
            .join()
            .map_err(|_| std::io::Error::other("after Rust analysis worker panicked"))??;
        Ok((before, after))
    })
}

fn ocaml_project_graph(
    root: &Path,
    frontend: &impl LanguageBackend,
) -> DiffkitResult<ProgramGraph> {
    if root.is_dir() {
        return graph_from_files([frontend.analyze_project(&ProjectContext {
            root,
            driver_executable: None,
            entries: &[],
            cache: None,
        })?]);
    }
    load_path(root, frontend)
}

fn ocaml_optional_project_graph(
    root: &Path,
    frontend: &impl LanguageBackend,
) -> DiffkitResult<ProgramGraph> {
    if !root.exists() {
        return graph_from_files(std::iter::empty());
    }
    ocaml_project_graph(root, frontend)
}

pub fn find_cargo_root(path: &Path) -> DiffkitResult<PathBuf> {
    let start = if path.is_dir() {
        path
    } else {
        path.parent().unwrap_or_else(|| Path::new("."))
    };
    for ancestor in start.ancestors() {
        if ancestor.join("Cargo.toml").is_file() {
            return Ok(ancestor.canonicalize()?);
        }
    }
    Err(std::io::Error::other(format!("no Cargo.toml found above {}", path.display())).into())
}

/// Return whether Cargo can plausibly compile `path` as part of one of the
/// package targets in the surrounding workspace. Merely living somewhere
/// below a Cargo.toml is not enough (documentation snippets are a common
/// counterexample).
pub fn rust_file_is_project_source(path: &Path) -> bool {
    let Ok(root) = find_cargo_root(path) else {
        return false;
    };
    let absolute = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let Some(layout) = cargo_source_layout(&root) else {
        return conventional_rust_source(&absolute, &root);
    };
    layout
        .package_roots
        .iter()
        .any(|root| conventional_rust_source(&absolute, root))
        || layout
            .target_sources
            .iter()
            .any(|source| target_contains_source(source, &absolute))
}

fn cargo_source_layout(root: &Path) -> Option<CargoSourceLayout> {
    let cache = CARGO_SOURCE_LAYOUTS.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(layout) = cache.lock().ok()?.get(root).cloned() {
        return layout;
    }

    let output = Command::new("cargo")
        .args(["metadata", "--no-deps", "--format-version", "1"])
        .current_dir(root)
        .output()
        .ok();
    let layout = output
        .filter(|output| output.status.success())
        .and_then(|output| serde_json::from_slice::<serde_json::Value>(&output.stdout).ok())
        .and_then(|metadata| {
            let packages = metadata.get("packages")?.as_array()?;
            let package_roots = packages
                .iter()
                .filter_map(|package| package.get("manifest_path"))
                .filter_map(serde_json::Value::as_str)
                .filter_map(|manifest| Path::new(manifest).parent())
                .map(Path::to_path_buf)
                .collect();
            let target_sources = packages
                .iter()
                .flat_map(|package| {
                    package
                        .get("targets")
                        .and_then(serde_json::Value::as_array)
                        .into_iter()
                        .flatten()
                })
                .filter_map(|target| target.get("src_path"))
                .filter_map(serde_json::Value::as_str)
                .map(PathBuf::from)
                .collect();
            Some(CargoSourceLayout {
                package_roots,
                target_sources,
            })
        });
    if let Ok(mut cache) = cache.lock() {
        cache.insert(root.to_path_buf(), layout.clone());
    }
    layout
}

fn conventional_rust_source(file: &Path, package_root: &Path) -> bool {
    file.starts_with(package_root.join("src"))
}

fn target_contains_source(target: &Path, file: &Path) -> bool {
    if target == file {
        return true;
    }
    let Some(parent) = target.parent() else {
        return false;
    };
    match target.file_name().and_then(|name| name.to_str()) {
        Some("lib.rs" | "main.rs" | "mod.rs") => file.starts_with(parent),
        _ => target
            .file_stem()
            .map(|stem| file.starts_with(parent.join(stem)))
            .unwrap_or(false),
    }
}

fn collect_source_files(path: &Path, extensions: &[&str]) -> DiffkitResult<Vec<PathBuf>> {
    let mut files = Vec::new();
    if path.is_file() {
        if has_extension(path, extensions) {
            files.push(path.to_path_buf());
        }
    } else {
        collect_directory(path, extensions, &mut files)?;
    }
    files.sort();
    Ok(files)
}

fn collect_directory(
    directory: &Path,
    extensions: &[&str],
    files: &mut Vec<PathBuf>,
) -> DiffkitResult<()> {
    let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(std::fs::DirEntry::path);
    for entry in entries {
        let file_type = entry.file_type()?;
        let path = entry.path();
        if file_type.is_dir() {
            if !matches!(
                path.file_name().and_then(|name| name.to_str()),
                Some("target" | ".git" | "_build" | "node_modules" | ".zig-cache" | "zig-out")
            ) {
                collect_directory(&path, extensions, files)?;
            }
        } else if file_type.is_file() && has_extension(&path, extensions) {
            files.push(path);
        }
    }
    Ok(())
}

fn find_ocaml_root(path: &Path) -> PathBuf {
    let start = if path.is_dir() {
        path
    } else {
        path.parent().unwrap_or_else(|| Path::new("."))
    };
    for ancestor in start.ancestors() {
        if ancestor.join("dune-project").is_file() {
            return ancestor.to_path_buf();
        }
    }
    start.to_path_buf()
}

fn has_extension(path: &Path, extensions: &[&str]) -> bool {
    path.extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| extensions.contains(&extension))
}

fn module_path(root: &Path, file: &Path) -> Vec<String> {
    let relative = file.strip_prefix(root).unwrap_or(file);
    let mut parts = relative
        .components()
        .filter_map(|component| match component {
            Component::Normal(value) => value.to_str().map(ToOwned::to_owned),
            _ => None,
        })
        .collect::<Vec<_>>();

    if parts.first().is_some_and(|part| part == "src") {
        parts.remove(0);
    }
    if let Some(last) = parts.last_mut() {
        *last = Path::new(last)
            .file_stem()
            .and_then(|stem| stem.to_str())
            .unwrap_or(last)
            .to_owned();
    }
    if parts
        .last()
        .is_some_and(|part| matches!(part.as_str(), "lib" | "main" | "mod"))
    {
        parts.pop();
    }
    parts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cargo_test_targets_are_project_sources() {
        let test = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/cli.rs");
        assert!(rust_file_is_project_source(&test));
    }
}
