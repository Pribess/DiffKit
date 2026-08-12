use std::error::Error;
use std::path::Path;

use crate::model::{FileAnalysis, LanguageId};

pub mod ocaml;
pub mod rust;

pub type FrontendResult<T> = Result<T, Box<dyn Error + Send + Sync>>;

pub struct FileContext<'a> {
    pub path: &'a Path,
    pub module: &'a [String],
}

/// A language frontend owns its concrete parser and lowers directly into DiffKit IR.
/// Parser-specific AST types never leak into the core engine.
pub trait LanguageFrontend: Send + Sync {
    fn language(&self) -> LanguageId;
    fn extensions(&self) -> &'static [&'static str];
    fn analyze_file(&self, context: &FileContext<'_>, source: &str)
    -> FrontendResult<FileAnalysis>;
}
