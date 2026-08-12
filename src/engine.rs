use std::collections::BTreeSet;
use std::fs;
use std::path::{Component, Path, PathBuf};

use crate::DiffkitResult;
use crate::diff::{DiffNode, diff_optional, tree_has_changes};
use crate::graph::ProgramGraph;
use crate::language::ocaml::OcamlFrontend;
use crate::language::rust::{
    RustFrontend, analyze_semantic_file_with_entries, analyze_semantic_source,
};
use crate::language::{FileContext, LanguageFrontend};
use crate::model::{FileAnalysis, SymbolId};

#[derive(Clone, Debug)]
pub struct RustDiffOptions {
    pub entries: Vec<String>,
    pub max_depth: usize,
    pub mode: RustAnalysisMode,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum RustAnalysisMode {
    #[default]
    Syntax,
    Semantic,
}

impl Default for RustDiffOptions {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
            max_depth: 8,
            mode: RustAnalysisMode::Syntax,
        }
    }
}

#[derive(Clone, Debug)]
pub struct OcamlDiffOptions {
    pub entries: Vec<String>,
    pub max_depth: usize,
}

impl Default for OcamlDiffOptions {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
            max_depth: 8,
        }
    }
}

trait DiffOptions {
    fn entries(&self) -> &[String];
    fn max_depth(&self) -> usize;
}

impl DiffOptions for RustDiffOptions {
    fn entries(&self) -> &[String] {
        &self.entries
    }

    fn max_depth(&self) -> usize {
        self.max_depth
    }
}

impl DiffOptions for OcamlDiffOptions {
    fn entries(&self) -> &[String] {
        &self.entries
    }

    fn max_depth(&self) -> usize {
        self.max_depth
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
}

pub fn rustdiff_sources(
    before_name: impl Into<String>,
    before_source: &str,
    after_name: impl Into<String>,
    after_source: &str,
    options: &RustDiffOptions,
) -> DiffkitResult<DiffReport> {
    if options.mode == RustAnalysisMode::Semantic {
        let before_analysis = analyze_semantic_source(before_source, &options.entries)?;
        let after_analysis = analyze_semantic_source(after_source, &options.entries)?;
        let before = graph_from_files([before_analysis])?;
        let after = graph_from_files([after_analysis])?;
        return build_report(
            "rust".to_owned(),
            before_name.into(),
            after_name.into(),
            &before,
            &after,
            options,
        );
    }

    let frontend = RustFrontend;
    diff_sources(
        before_name.into(),
        before_source,
        after_name.into(),
        after_source,
        &frontend,
        options,
    )
}

pub fn rustdiff_paths(
    before_path: &Path,
    after_path: &Path,
    options: &RustDiffOptions,
) -> DiffkitResult<DiffReport> {
    if options.mode == RustAnalysisMode::Semantic {
        let before = graph_from_files([analyze_semantic_file_with_entries(
            before_path,
            &options.entries,
        )?])?;
        let after = graph_from_files([analyze_semantic_file_with_entries(
            after_path,
            &options.entries,
        )?])?;
        return build_report(
            "rust".to_owned(),
            before_path.display().to_string(),
            after_path.display().to_string(),
            &before,
            &after,
            options,
        );
    }

    let frontend = RustFrontend;
    let before = load_path(before_path, &frontend)?;
    let after = load_path(after_path, &frontend)?;
    build_report(
        frontend.language().0,
        before_path.display().to_string(),
        after_path.display().to_string(),
        &before,
        &after,
        options,
    )
}

pub fn ocamldiff_sources(
    before_name: impl Into<String>,
    before_source: &str,
    after_name: impl Into<String>,
    after_source: &str,
    options: &OcamlDiffOptions,
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
    options: &OcamlDiffOptions,
) -> DiffkitResult<DiffReport> {
    let frontend = OcamlFrontend;
    let before = load_path(before_path, &frontend)?;
    let after = load_path(after_path, &frontend)?;
    build_report(
        frontend.language().0,
        before_path.display().to_string(),
        after_path.display().to_string(),
        &before,
        &after,
        options,
    )
}

fn diff_sources(
    before_name: String,
    before_source: &str,
    after_name: String,
    after_source: &str,
    frontend: &impl LanguageFrontend,
    options: &impl DiffOptions,
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
    options: &impl DiffOptions,
) -> DiffkitResult<DiffReport> {
    let candidate_entries = if options.entries().is_empty() {
        let public = before
            .public_symbols()
            .into_iter()
            .chain(after.public_symbols())
            .collect::<BTreeSet<_>>();
        let public_changes = changed_entries(before, after, public, options.max_depth());
        if public_changes.is_empty() {
            before
                .functions()
                .keys()
                .chain(after.functions().keys())
                .cloned()
                .collect()
        } else {
            return Ok(report_from_trees(
                language,
                before_name,
                after_name,
                public_changes,
            ));
        }
    } else {
        resolve_explicit_entries(before, after, options.entries())?
    };

    let trees = changed_entries(before, after, candidate_entries, options.max_depth());
    Ok(report_from_trees(language, before_name, after_name, trees))
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
    }
}

fn resolve_explicit_entries(
    before: &ProgramGraph,
    after: &ProgramGraph,
    entries: &[String],
) -> DiffkitResult<BTreeSet<SymbolId>> {
    let mut resolved = BTreeSet::new();
    for entry in entries {
        let before_entry = before.resolve_entry(entry).map_err(std::io::Error::other)?;
        let after_entry = after.resolve_entry(entry).map_err(std::io::Error::other)?;
        if before_entry.is_none() && after_entry.is_none() {
            return Err(std::io::Error::other(format!("entry not found: {entry}")).into());
        }
        resolved.extend(before_entry);
        resolved.extend(after_entry);
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
            let before_tree = before.build_call_tree(&entry, max_depth);
            let after_tree = after.build_call_tree(&entry, max_depth);
            let tree = diff_optional(before_tree.as_ref(), after_tree.as_ref())?;
            tree_has_changes(&tree).then_some(EntryDiff { entry, tree })
        })
        .collect()
}

fn load_path(path: &Path, frontend: &impl LanguageFrontend) -> DiffkitResult<ProgramGraph> {
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
                Some("target" | ".git")
            ) {
                collect_directory(&path, extensions, files)?;
            }
        } else if file_type.is_file() && has_extension(&path, extensions) {
            files.push(path);
        }
    }
    Ok(())
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
