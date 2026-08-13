#![feature(rustc_private)]

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, ExitCode};

use clap::{Args, Parser, Subcommand, ValueEnum};
use diffkit::git::GitComparison;
use diffkit::language::rust::{run_rustc_wrapper, rustc_wrapper_requested};
use diffkit::{
    ColorMode, DiffOptions, RenderOptions, ocamldiff_paths, ocamldiff_project_files,
    ocamldiff_sources, ocamltree_path, ocamltree_project_file, render_report_with_options,
    render_tree_report_with_options, rustdiff_project_files, rustdiff_project_paths,
    rustdiff_sources, rusttree_path, rusttree_project_file,
};

fn main() -> ExitCode {
    if rustc_wrapper_requested() {
        return match run_rustc_wrapper() {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("error: {error}");
                ExitCode::from(1)
            }
        };
    }
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(1)
        }
    }
}

fn run() -> diffkit::DiffkitResult<()> {
    let cli = Cli::parse();
    let options = DiffOptions {
        entries: cli.entries,
        max_depth: cli.max_depth,
    };
    let render = RenderOptions {
        show_types: cli.types,
        color: cli.color.into(),
    };

    match cli.command {
        Some(Command::File(arguments)) => run_file(arguments, cli.language, &options, &render),
        Some(Command::Git(arguments)) => run_git(
            &arguments.revisions,
            &arguments.pathspecs,
            cli.language,
            &options,
            &render,
        ),
        None => run_git(&[], &cli.pathspecs, cli.language, &options, &render),
    }
}

fn run_file(
    arguments: FileArgs,
    language: Option<CliLanguage>,
    options: &DiffOptions,
    render: &RenderOptions,
) -> diffkit::DiffkitResult<()> {
    let detected = language.unwrap_or(detect_file_language(&arguments.before)?);
    let wrapper = std::env::current_exe()?;
    if let Some(after) = arguments.after {
        let after_language = detect_file_language(&after)?;
        if language.is_none() && detected != after_language {
            return Err(std::io::Error::other(format!(
                "cannot compare {} and {} because their languages differ",
                arguments.before.display(),
                after.display()
            ))
            .into());
        }
        let report = match detected {
            CliLanguage::Rust
                if diffkit::engine::rust_file_is_project_source(&arguments.before)
                    && diffkit::engine::rust_file_is_project_source(&after) =>
            {
                match rustdiff_project_files(&arguments.before, &after, &wrapper, options)? {
                    Some(report) => report,
                    None => rustdiff_standalone_files(&arguments.before, &after, options)?,
                }
            }
            CliLanguage::Rust => rustdiff_standalone_files(&arguments.before, &after, options)?,
            CliLanguage::Ocaml
                if find_ancestor_marker(&arguments.before, "dune-project").is_some()
                    && find_ancestor_marker(&after, "dune-project").is_some() =>
            {
                ocamldiff_project_files(&arguments.before, &after, options)?
            }
            CliLanguage::Ocaml => {
                let before_source = fs::read_to_string(&arguments.before)?;
                let after_source = fs::read_to_string(&after)?;
                ocamldiff_sources(
                    arguments.before.display().to_string(),
                    &before_source,
                    after.display().to_string(),
                    &after_source,
                    options,
                )?
            }
        };
        println!("{}", render_report_with_options(&report, render));
    } else {
        let report = match detected {
            CliLanguage::Rust
                if diffkit::engine::rust_file_is_project_source(&arguments.before) =>
            {
                match rusttree_project_file(&arguments.before, &wrapper, options)? {
                    Some(report) => report,
                    None => rusttree_path(&arguments.before, options)?,
                }
            }
            CliLanguage::Rust => rusttree_path(&arguments.before, options)?,
            CliLanguage::Ocaml
                if find_ancestor_marker(&arguments.before, "dune-project").is_some() =>
            {
                ocamltree_project_file(&arguments.before, options)?
            }
            CliLanguage::Ocaml => ocamltree_path(&arguments.before, options)?,
        };
        println!("{}", render_tree_report_with_options(&report, render));
    }
    Ok(())
}

fn rustdiff_standalone_files(
    before: &Path,
    after: &Path,
    options: &DiffOptions,
) -> diffkit::DiffkitResult<diffkit::DiffReport> {
    let before_source = fs::read_to_string(before)?;
    let after_source = fs::read_to_string(after)?;
    rustdiff_sources(
        before.display().to_string(),
        &before_source,
        after.display().to_string(),
        &after_source,
        options,
    )
}

fn run_git(
    revisions: &[String],
    pathspecs: &[PathBuf],
    language: Option<CliLanguage>,
    options: &DiffOptions,
    render: &RenderOptions,
) -> diffkit::DiffkitResult<()> {
    let comparison = GitComparison::discover(Path::new("."), revisions, pathspecs)?;
    if comparison.changed_paths.is_empty() {
        println!(
            "No call changes between {} and {}.",
            comparison.before.label(),
            comparison.after.label()
        );
        return Ok(());
    }
    let (before, after) = comparison.materialize()?;
    let mut rendered = Vec::new();
    let wrapper = std::env::current_exe()?;

    if language.is_none_or(|language| language == CliLanguage::Rust) {
        let rust_paths = comparison
            .changed_paths
            .iter()
            .filter(|path| language_from_extension(path) == Some(CliLanguage::Rust))
            .cloned()
            .collect::<Vec<_>>();
        let rust_triggers = comparison
            .changed_paths
            .iter()
            .filter(|path| is_rust_project_trigger(path))
            .cloned()
            .collect::<Vec<_>>();
        let project_roots = changed_cargo_roots(before.path(), after.path(), &rust_triggers);
        let mut covered = BTreeSet::new();
        for relative_root in project_roots {
            let before_root = before.path().join(&relative_root);
            let after_root = after.path().join(&relative_root);
            let relevant_paths = rust_paths
                .iter()
                .filter(|path| {
                    path.strip_prefix(&relative_root)
                        .ok()
                        .is_some_and(|relative| {
                            diffkit::engine::rust_file_is_project_source(
                                &before_root.join(relative),
                            ) || diffkit::engine::rust_file_is_project_source(
                                &after_root.join(relative),
                            )
                        })
                })
                .cloned()
                .collect::<Vec<_>>();
            let config_change = rust_triggers.iter().any(|path| {
                path.starts_with(&relative_root)
                    && language_from_extension(path) != Some(CliLanguage::Rust)
            });
            if relevant_paths.is_empty() && !config_change {
                continue;
            }
            let mut report = rustdiff_project_paths(&before_root, &after_root, &wrapper, options)?;
            report.before = endpoint_project_label(before.label(), &relative_root);
            report.after = endpoint_project_label(after.label(), &relative_root);
            covered.extend(relevant_paths.iter().filter_map(|path| {
                (report_analyzes_path(&report, &before.path().join(path))
                    || report_analyzes_path(&report, &after.path().join(path)))
                .then_some(path.clone())
            }));
            if report.message.is_none() {
                rendered.push(render_report_with_options(&report, render));
            }
        }

        for relative in rust_paths.iter().filter(|path| !covered.contains(*path)) {
            let before_path = before.path().join(relative);
            let after_path = after.path().join(relative);
            let mut report = rustdiff_sources(
                format!("{}:{}", before.label(), relative.display()),
                &read_source_or_empty(&before_path)?,
                format!("{}:{}", after.label(), relative.display()),
                &read_source_or_empty(&after_path)?,
                options,
            )?;
            if report.message.is_none() {
                report.before = format!("{}:{}", before.label(), relative.display());
                report.after = format!("{}:{}", after.label(), relative.display());
                rendered.push(render_report_with_options(&report, render));
            }
        }
    }

    if language.is_none_or(|language| language == CliLanguage::Ocaml) {
        let ocaml_paths = comparison
            .changed_paths
            .iter()
            .filter(|path| language_from_extension(path) == Some(CliLanguage::Ocaml))
            .cloned()
            .collect::<Vec<_>>();
        let ocaml_triggers = comparison
            .changed_paths
            .iter()
            .filter(|path| is_ocaml_project_trigger(path))
            .cloned()
            .collect::<Vec<_>>();
        if !ocaml_triggers.is_empty() {
            let roots =
                changed_marker_roots(before.path(), after.path(), &ocaml_triggers, "dune-project");
            let mut covered = BTreeSet::new();
            for relative_root in roots {
                let mut report = ocamldiff_paths(
                    &before.path().join(&relative_root),
                    &after.path().join(&relative_root),
                    options,
                )?;
                report.before = endpoint_project_label(before.label(), &relative_root);
                report.after = endpoint_project_label(after.label(), &relative_root);
                if report.message.is_none() {
                    rendered.push(render_report_with_options(&report, render));
                }
                covered.extend(
                    ocaml_paths
                        .iter()
                        .filter(|path| path.starts_with(&relative_root))
                        .cloned(),
                );
            }
            for relative in ocaml_paths.iter().filter(|path| !covered.contains(*path)) {
                let mut report = ocamldiff_sources(
                    format!("{}:{}", before.label(), relative.display()),
                    &read_source_or_empty(&before.path().join(relative))?,
                    format!("{}:{}", after.label(), relative.display()),
                    &read_source_or_empty(&after.path().join(relative))?,
                    options,
                )?;
                if report.message.is_none() {
                    report.before = format!("{}:{}", before.label(), relative.display());
                    report.after = format!("{}:{}", after.label(), relative.display());
                    rendered.push(render_report_with_options(&report, render));
                }
            }
        }
    }

    if rendered.is_empty() {
        println!(
            "No call changes between {} and {}.",
            comparison.before.label(),
            comparison.after.label()
        );
    } else {
        println!("{}", rendered.join("\n\n"));
    }
    Ok(())
}

fn endpoint_project_label(endpoint: &str, relative_root: &Path) -> String {
    if relative_root.as_os_str().is_empty() {
        endpoint.to_owned()
    } else {
        format!("{endpoint}:{}", relative_root.display())
    }
}

fn is_rust_project_trigger(path: &Path) -> bool {
    language_from_extension(path) == Some(CliLanguage::Rust)
        || matches!(
            path.file_name().and_then(|name| name.to_str()),
            Some("Cargo.toml" | "Cargo.lock" | "rust-toolchain" | "rust-toolchain.toml")
        )
        || path
            .components()
            .any(|component| component.as_os_str() == ".cargo")
}

fn is_ocaml_project_trigger(path: &Path) -> bool {
    language_from_extension(path) == Some(CliLanguage::Ocaml)
        || matches!(
            path.file_name().and_then(|name| name.to_str()),
            Some("dune" | "dune-project" | "dune-workspace")
        )
        || path.extension().and_then(|extension| extension.to_str()) == Some("opam")
}

fn report_analyzes_path(report: &diffkit::DiffReport, path: &Path) -> bool {
    report.analyzed_files.iter().any(|analyzed| {
        analyzed == path
            || analyzed
                .canonicalize()
                .ok()
                .zip(path.canonicalize().ok())
                .is_some_and(|(analyzed, path)| analyzed == path)
    })
}

fn changed_cargo_roots(
    before_snapshot: &Path,
    after_snapshot: &Path,
    paths: &[PathBuf],
) -> BTreeSet<PathBuf> {
    let mut roots = BTreeSet::new();
    for relative in paths {
        for snapshot in [before_snapshot, after_snapshot] {
            let Some(root) = nearest_cargo_root(snapshot, relative) else {
                continue;
            };
            let workspace = cargo_workspace_root(&root).unwrap_or(root);
            let relative_root = relative_snapshot_path(snapshot, &workspace).or_else(|| {
                nearest_cargo_root(snapshot, relative)
                    .and_then(|root| relative_snapshot_path(snapshot, &root))
            });
            if let Some(relative_root) = relative_root {
                roots.insert(relative_root);
            }
        }
    }
    roots
}

fn changed_marker_roots(
    before_snapshot: &Path,
    after_snapshot: &Path,
    paths: &[PathBuf],
    marker: &str,
) -> BTreeSet<PathBuf> {
    let mut roots = BTreeSet::new();
    for relative in paths {
        for snapshot in [before_snapshot, after_snapshot] {
            let Some(root) = nearest_project_marker(snapshot, relative, marker) else {
                continue;
            };
            if let Some(relative_root) = relative_snapshot_path(snapshot, &root) {
                roots.insert(relative_root);
            }
        }
    }
    roots
}

fn relative_snapshot_path(snapshot: &Path, path: &Path) -> Option<PathBuf> {
    path.strip_prefix(snapshot)
        .ok()
        .map(Path::to_path_buf)
        .or_else(|| {
            let snapshot = snapshot.canonicalize().ok()?;
            path.strip_prefix(snapshot).ok().map(Path::to_path_buf)
        })
}

fn nearest_cargo_root(snapshot: &Path, relative: &Path) -> Option<PathBuf> {
    nearest_project_marker(snapshot, relative, "Cargo.toml")
}

fn nearest_project_marker(snapshot: &Path, relative: &Path, marker: &str) -> Option<PathBuf> {
    let mut cursor = snapshot.join(relative).parent()?.to_path_buf();
    loop {
        if cursor.join(marker).is_file() {
            return Some(cursor);
        }
        if cursor == snapshot || !cursor.starts_with(snapshot) {
            return None;
        }
        cursor = cursor.parent()?.to_path_buf();
    }
}

fn cargo_workspace_root(directory: &Path) -> Option<PathBuf> {
    let output = ProcessCommand::new("cargo")
        .args(["locate-project", "--workspace", "--message-format", "plain"])
        .current_dir(directory)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let manifest = PathBuf::from(String::from_utf8(output.stdout).ok()?.trim());
    manifest.parent().map(Path::to_path_buf)
}

fn find_ancestor_marker(path: &Path, marker: &str) -> Option<PathBuf> {
    let start = if path.is_dir() { path } else { path.parent()? };
    start
        .ancestors()
        .find(|ancestor| ancestor.join(marker).is_file())
        .map(Path::to_path_buf)
}

fn read_source_or_empty(path: &Path) -> std::io::Result<String> {
    match fs::read_to_string(path) {
        Ok(source) => Ok(source),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(String::new()),
        Err(error) => Err(error),
    }
}

/// Show semantic call-tree changes. With no subcommand, compare HEAD with the
/// current Git worktree.
#[derive(Debug, Parser)]
#[command(
    version,
    about,
    after_help = "diffkit is shorthand for `diffkit git`. Languages are inferred from project and source files."
)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,

    /// Limit output to an entry function or method. May be repeated.
    #[arg(short = 'e', long = "entry", value_name = "SYMBOL", global = true)]
    entries: Vec<String>,

    /// Override source-language detection.
    #[arg(short, long, value_enum, global = true)]
    language: Option<CliLanguage>,

    /// Show parameter types. Concrete generic arguments are always shown.
    #[arg(long, global = true)]
    types: bool,

    /// Select ANSI colors or plain output.
    #[arg(long, value_enum, default_value_t, global = true)]
    color: CliColor,

    /// Maximum expanded call depth.
    #[arg(long, default_value_t = 8, value_name = "N", global = true)]
    max_depth: usize,

    /// Restrict the default Git diff to these paths. Must follow `--`.
    #[arg(last = true, value_name = "PATHSPEC")]
    pathspecs: Vec<PathBuf>,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Compare Git snapshots: no REV means HEAD/worktree, one means REV^/REV.
    Git(GitArgs),

    /// Show one file's semantic forest or compare two semantic forests.
    File(FileArgs),
}

#[derive(Debug, Args)]
struct GitArgs {
    /// Zero, one, or two Git revisions.
    #[arg(value_name = "REV", num_args = 0..=2)]
    revisions: Vec<String>,

    /// Restrict changed source locations. Must follow `--`.
    #[arg(last = true, value_name = "PATHSPEC")]
    pathspecs: Vec<PathBuf>,
}

#[derive(Debug, Args)]
struct FileArgs {
    /// File to display, or the before file when comparing.
    #[arg(value_name = "FILE")]
    before: PathBuf,

    /// Optional after file.
    #[arg(value_name = "AFTER")]
    after: Option<PathBuf>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, ValueEnum)]
enum CliLanguage {
    Rust,
    Ocaml,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, ValueEnum)]
enum CliColor {
    #[default]
    Ansi,
    Plain,
}

impl From<CliColor> for ColorMode {
    fn from(value: CliColor) -> Self {
        match value {
            CliColor::Ansi => Self::Ansi,
            CliColor::Plain => Self::Plain,
        }
    }
}

fn detect_file_language(path: &Path) -> diffkit::DiffkitResult<CliLanguage> {
    language_from_extension(path).ok_or_else(|| {
        std::io::Error::other(format!(
            "cannot infer a language from {}; expected .rs, .ml, or .mli",
            path.display()
        ))
        .into()
    })
}

fn language_from_extension(path: &Path) -> Option<CliLanguage> {
    match path.extension()?.to_str()?.to_ascii_lowercase().as_str() {
        "rs" => Some(CliLanguage::Rust),
        "ml" | "mli" => Some(CliLanguage::Ocaml),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use clap::{CommandFactory, Parser};

    use super::*;

    #[test]
    fn clap_definition_is_valid() {
        Cli::command().debug_assert();
    }

    #[test]
    fn no_subcommand_means_default_git_diff() {
        let cli = Cli::try_parse_from(["diffkit"]).unwrap();
        assert!(cli.command.is_none());
        assert_eq!(cli.color, CliColor::Ansi);
    }

    #[test]
    fn parses_git_revisions_pathspec_and_global_options() {
        let cli = Cli::try_parse_from([
            "diffkit",
            "git",
            "main",
            "HEAD",
            "--color=plain",
            "-e",
            "checkout",
            "--",
            "src/payment.rs",
        ])
        .unwrap();
        let Some(Command::Git(git)) = cli.command else {
            panic!("expected git command");
        };
        assert_eq!(git.revisions, ["main", "HEAD"]);
        assert_eq!(git.pathspecs, [PathBuf::from("src/payment.rs")]);
        assert_eq!(cli.entries, ["checkout"]);
        assert_eq!(cli.color, CliColor::Plain);
    }

    #[test]
    fn parses_file_show_and_compare_forms() {
        let show = Cli::try_parse_from(["diffkit", "file", "src/payment.rs"]).unwrap();
        let Some(Command::File(show)) = show.command else {
            panic!("expected file command");
        };
        assert!(show.after.is_none());

        let compare = Cli::try_parse_from(["diffkit", "file", "before.ml", "after.ml"]).unwrap();
        let Some(Command::File(compare)) = compare.command else {
            panic!("expected file command");
        };
        assert_eq!(compare.after, Some(PathBuf::from("after.ml")));
    }

    #[test]
    fn old_positional_snapshot_interface_is_rejected() {
        assert!(Cli::try_parse_from(["diffkit", "before.rs", "after.rs"]).is_err());
        assert!(Cli::try_parse_from(["diffkit", "--semantic"]).is_err());
        assert!(Cli::try_parse_from(["diffkit", "--syntax"]).is_err());
    }
}
