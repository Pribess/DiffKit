#![feature(rustc_private)]

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, ValueEnum};
use diffkit::{
    ColorMode, OcamlDiffOptions, RenderOptions, RustAnalysisMode, RustDiffOptions, ocamldiff_paths,
    render_report_with_options, rustdiff_paths,
};

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(1)
        }
    }
}

fn run() -> diffkit::DiffkitResult<()> {
    let Cli {
        before,
        after,
        entries,
        language: option_language,
        semantic,
        color,
        max_depth,
    } = Cli::parse();

    let language = option_language
        .map(Ok)
        .unwrap_or_else(|| detect_language(&before, &after))?;
    if language == CliLanguage::Ocaml && semantic {
        return Err(
            std::io::Error::other("--semantic is currently implemented for Rust only").into(),
        );
    }

    let report = match language {
        CliLanguage::Rust => rustdiff_paths(
            &before,
            &after,
            &RustDiffOptions {
                entries,
                max_depth,
                mode: if semantic {
                    RustAnalysisMode::Semantic
                } else {
                    RustAnalysisMode::Syntax
                },
            },
        )?,
        CliLanguage::Ocaml => {
            ocamldiff_paths(&before, &after, &OcamlDiffOptions { entries, max_depth })?
        }
    };
    println!(
        "{}",
        render_report_with_options(
            &report,
            &RenderOptions {
                show_types: false,
                color: color.into(),
            },
        )
    );
    Ok(())
}

/// Compare structural call trees from two source snapshots.
#[derive(Debug, Parser)]
#[command(
    version,
    about,
    arg_required_else_help = true,
    after_help = "The language is inferred from .rs, .ml, and .mli extensions. Use --language for mixed-language directories."
)]
struct Cli {
    /// Source file or directory before the change.
    #[arg(value_name = "BEFORE")]
    before: PathBuf,

    /// Source file or directory after the change.
    #[arg(value_name = "AFTER")]
    after: PathBuf,

    /// Limit output to an entry function or method. May be repeated.
    #[arg(short = 'e', long = "entry", value_name = "SYMBOL")]
    entries: Vec<String>,

    /// Override extension-based language detection.
    #[arg(short, long, value_enum)]
    language: Option<CliLanguage>,

    /// Resolve concrete Rust calls with rustc_public.
    #[arg(long)]
    semantic: bool,

    /// Select ANSI colors or plain output.
    #[arg(long, value_enum, default_value_t)]
    color: CliColor,

    /// Maximum expanded call depth.
    #[arg(long, default_value_t = 8, value_name = "N")]
    max_depth: usize,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, ValueEnum)]
enum CliLanguage {
    Rust,
    Ocaml,
}

impl CliLanguage {
    fn name(self) -> &'static str {
        match self {
            Self::Rust => "Rust",
            Self::Ocaml => "OCaml",
        }
    }
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

fn detect_language(before: &Path, after: &Path) -> diffkit::DiffkitResult<CliLanguage> {
    let before_languages = languages_under(before)?;
    let after_languages = languages_under(after)?;
    let languages = before_languages
        .union(&after_languages)
        .copied()
        .collect::<Vec<_>>();

    match languages.as_slice() {
        [language] => Ok(*language),
        [] => Err(std::io::Error::other(format!(
            "cannot infer a language from {} and {}; expected .rs, .ml, or .mli files",
            before.display(),
            after.display()
        ))
        .into()),
        _ => Err(std::io::Error::other(format!(
            "language detection is ambiguous ({}) ; use --language rust or --language ocaml",
            languages
                .iter()
                .map(|language| language.name())
                .collect::<Vec<_>>()
                .join(", ")
        ))
        .into()),
    }
}

fn languages_under(path: &Path) -> diffkit::DiffkitResult<BTreeSet<CliLanguage>> {
    if !path.exists() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("path does not exist: {}", path.display()),
        )
        .into());
    }
    let mut languages = BTreeSet::new();
    collect_languages(path, &mut languages)?;
    Ok(languages)
}

fn collect_languages(path: &Path, languages: &mut BTreeSet<CliLanguage>) -> std::io::Result<()> {
    if path.is_file() {
        if let Some(language) = language_from_extension(path) {
            languages.insert(language);
        }
        return Ok(());
    }

    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let file_type = entry.file_type()?;
        if file_type.is_symlink() {
            continue;
        }
        let entry_path = entry.path();
        if file_type.is_dir() {
            collect_languages(&entry_path, languages)?;
        } else if file_type.is_file()
            && let Some(language) = language_from_extension(&entry_path)
        {
            languages.insert(language);
        }
    }
    Ok(())
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
    fn parses_repeatable_entries_and_typed_modes() {
        let cli = Cli::try_parse_from([
            "diffkit",
            "before.rs",
            "after.rs",
            "--semantic",
            "--color=plain",
            "--language",
            "rust",
            "-e",
            "run<Postgres>",
            "-e",
            "run<S3>",
        ])
        .unwrap();

        assert_eq!(cli.before, PathBuf::from("before.rs"));
        assert_eq!(cli.after, PathBuf::from("after.rs"));
        assert_eq!(cli.language, Some(CliLanguage::Rust));
        assert_eq!(cli.color, CliColor::Plain);
        assert!(cli.semantic);
        assert_eq!(cli.entries, ["run<Postgres>", "run<S3>"]);
    }

    #[test]
    fn ansi_is_the_cli_default() {
        let cli = Cli::try_parse_from(["diffkit", "before.rs", "after.rs"]).unwrap();

        assert_eq!(cli.color, CliColor::Ansi);
        assert_eq!(cli.max_depth, 8);
    }
}
