use std::fmt;
use std::path::PathBuf;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct LanguageId(pub String);

impl LanguageId {
    pub fn new(value: impl Into<String>) -> Self {
        Self(value.into())
    }
}

impl fmt::Display for LanguageId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct SymbolId {
    pub language: LanguageId,
    pub module: Vec<String>,
    pub container: Option<String>,
    pub name: String,
}

impl SymbolId {
    pub fn short_name(&self) -> String {
        match &self.container {
            Some(container) => format!("{container}::{}", self.name),
            None => self.name.clone(),
        }
    }

    pub fn qualified_parts(&self) -> Vec<&str> {
        self.module
            .iter()
            .map(String::as_str)
            .chain(self.container.iter().map(String::as_str))
            .chain(std::iter::once(self.name.as_str()))
            .collect()
    }
}

impl fmt::Display for SymbolId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}://", self.language)?;
        let parts = self.qualified_parts();
        write!(f, "{}", parts.join("::"))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceSpan {
    pub file: PathBuf,
    pub start_line: usize,
    pub start_column: usize,
    pub start_byte: Option<usize>,
    pub end_line: usize,
    pub end_column: usize,
    pub end_byte: Option<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CallSyntax {
    Path(Vec<String>),
    SelfMethod(String),
    Method { receiver: String, method: String },
}

impl CallSyntax {
    pub fn key_fragment(&self) -> String {
        match self {
            Self::Path(parts) => parts.join("::"),
            Self::SelfMethod(method) => format!("self.{method}"),
            Self::Method { receiver, method } => format!("{receiver}.{method}"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallSite {
    pub syntax: CallSyntax,
    /// Authoritative semantic target supplied by rustc_public, ocaml-index, or
    /// another language backend. Syntax-only frontends leave this empty and
    /// the common graph uses conservative path resolution.
    pub target: Option<SymbolId>,
    /// Fully formatted by the owning language frontend. Core rendering never
    /// needs to know whether a call uses `f(x)` or `f x` syntax.
    pub label: CallLabel,
    pub span: SourceSpan,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallLabel {
    pub default: String,
    pub typed: Option<String>,
}

impl CallLabel {
    pub fn new(default: impl Into<String>) -> Self {
        Self {
            default: default.into(),
            typed: None,
        }
    }

    pub fn with_types(default: impl Into<String>, typed: impl Into<String>) -> Self {
        Self {
            default: default.into(),
            typed: Some(typed.into()),
        }
    }

    pub fn text(&self, show_types: bool) -> &str {
        if show_types {
            self.typed.as_deref().unwrap_or(&self.default)
        } else {
            &self.default
        }
    }

    pub fn with_suffix(&self, suffix: &str) -> Self {
        Self {
            default: format!("{}{suffix}", self.default),
            typed: self.typed.as_ref().map(|typed| format!("{typed}{suffix}")),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionInfo {
    pub id: SymbolId,
    /// Declaration-shaped label used only when this function is a tree root.
    pub label: CallLabel,
    pub public: bool,
    pub calls: Vec<CallSite>,
    pub span: SourceSpan,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LanguageFact {
    pub subject: SymbolId,
    pub namespace: LanguageId,
    pub kind: String,
    pub key: String,
    pub value: String,
    pub span: SourceSpan,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FileAnalysis {
    pub functions: Vec<FunctionInfo>,
    pub facts: Vec<LanguageFact>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallNode {
    pub key: String,
    pub label: CallLabel,
    pub children: Vec<CallNode>,
}
