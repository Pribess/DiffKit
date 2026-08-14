use std::error::Error;
use std::path::Path;

use crate::model::{LanguageId, SemanticCallGraph};

pub mod ocaml;
pub mod rust;

pub type FrontendResult<T> = Result<T, Box<dyn Error + Send + Sync>>;

pub struct FileContext<'a> {
    pub path: &'a Path,
    pub module: &'a [String],
}

pub struct ProjectContext<'a> {
    pub root: &'a Path,
    /// Executable used when a compiler requires DiffKit as a driver/wrapper.
    pub driver_executable: Option<&'a Path>,
    pub entries: &'a [String],
    pub cache: Option<ProjectCache<'a>>,
}

#[derive(Clone, Copy)]
pub struct ProjectCache<'a> {
    pub project_root: &'a Path,
    pub endpoint: &'a str,
    pub verbose: bool,
}

/// A language frontend owns its parser/compiler representation and emits the
/// small semantic call-graph result consumed by DiffKit. This is not a shared
/// compiler AST: language-native AST, Typedtree, and MIR types never leak into
/// the common engine.
pub trait LanguageBackend: Send + Sync {
    fn language(&self) -> LanguageId;
    fn extensions(&self) -> &'static [&'static str];
    fn analyze_file(
        &self,
        context: &FileContext<'_>,
        source: &str,
    ) -> FrontendResult<SemanticCallGraph>;
    fn analyze_project(&self, context: &ProjectContext<'_>) -> FrontendResult<SemanticCallGraph>;
}

pub fn backend_for_extension(path: &Path) -> Option<&'static dyn LanguageBackend> {
    let extension = path.extension()?.to_str()?;
    builtin_backends().into_iter().find(|backend| {
        backend
            .extensions()
            .iter()
            .any(|candidate| candidate.eq_ignore_ascii_case(extension))
    })
}

pub fn backend_for_language(language: &str) -> Option<&'static dyn LanguageBackend> {
    builtin_backends()
        .into_iter()
        .find(|backend| backend.language().0.eq_ignore_ascii_case(language))
}

pub fn builtin_backends() -> [&'static dyn LanguageBackend; 2] {
    [&rust::RUST_BACKEND, &ocaml::OCAML_BACKEND]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_routes_extensions_without_engine_language_branches() {
        assert_eq!(
            backend_for_extension(Path::new("service.RS"))
                .unwrap()
                .language()
                .0,
            "rust"
        );
        assert_eq!(
            backend_for_extension(Path::new("service.mli"))
                .unwrap()
                .language()
                .0,
            "ocaml"
        );
    }
}
