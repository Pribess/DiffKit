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

/// A language frontend owns its parser/compiler representation and emits the
/// small semantic call-graph result consumed by DiffKit. This is not a shared
/// compiler AST: language-native AST, Typedtree, and MIR types never leak into
/// the common engine.
pub trait LanguageFrontend: Send + Sync {
    fn language(&self) -> LanguageId;
    fn extensions(&self) -> &'static [&'static str];
    fn analyze_file(&self, context: &FileContext<'_>, source: &str)
    -> FrontendResult<FileAnalysis>;
}
