use std::collections::BTreeSet;
use std::fmt;
use std::path::PathBuf;

use serde::{Deserialize, Serialize};

/// Stable identity of a semantic definition inside one analyzed program.
///
/// `SymbolId` is the public, language-neutral representation of a definition;
/// this alias makes the distinction between definition and edge identities
/// explicit in the graph/diff layers without duplicating the symbol payload.
pub type NodeId = SymbolId;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize)]
pub struct CallSiteId(pub String);

impl CallSiteId {
    pub fn source(syntax: &CallSyntax, span: &SourceSpan) -> Self {
        Self(format!(
            "{}@{}:{}-{}:{}",
            syntax.key_fragment(),
            span.start_line,
            span.start_column,
            span.end_line,
            span.end_column
        ))
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize)]
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

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize)]
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

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SourceSpan {
    pub file: PathBuf,
    pub start_line: usize,
    pub start_column: usize,
    pub start_byte: Option<usize>,
    pub end_line: usize,
    pub end_column: usize,
    pub end_byte: Option<usize>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
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

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct CallSite {
    /// Identity of this source call edge. Backends derive it from the owning
    /// definition and the call's structural source identity. It is kept
    /// separate from the callee because one function may call the same target
    /// more than once.
    pub id: CallSiteId,
    pub syntax: CallSyntax,
    /// Authoritative semantic target supplied by rustc_public, OCaml Typedtree, or
    /// another language backend. Syntax-only frontends use `Unresolved` and
    /// the common graph falls back to conservative path resolution.
    pub target: CallTarget,
    /// Fully formatted by the owning language frontend. Core rendering never
    /// needs to know whether a call uses `f(x)` or `f x` syntax.
    pub label: CallLabel,
    pub span: SourceSpan,
}

#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub enum CallTarget {
    #[default]
    Unresolved,
    /// A typed indirect call whose concrete callable value is not known.
    /// This is intentionally distinct from a syntax-resolution failure.
    Indirect {
        signature: Option<String>,
        reason: UnresolvedReason,
    },
    Direct(SymbolId),
    Dynamic {
        dispatch: SymbolId,
        candidates: Vec<DispatchCandidate>,
        resolution: DispatchResolution,
        evidence: DispatchEvidence,
        unresolved_reasons: BTreeSet<UnresolvedReason>,
    },
}

/// Why a candidate set is justified when it is complete.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub enum DispatchEvidence {
    /// Concrete values were followed to this exact call site.
    #[default]
    ExactFlow,
    /// The backend proved a closed candidate universe for this call site.
    ClosedSet,
}

impl fmt::Display for DispatchEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::ExactFlow => "exact-flow",
            Self::ClosedSet => "closed-set",
        })
    }
}

/// Machine-readable causes for an unresolved or partially resolved call.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum UnresolvedReason {
    OpaqueInput,
    ExternalCode,
    ExternalMemory,
    FunctionPointer,
    CrossCrateBoundary,
    AnalysisLimit,
    UnsupportedConstruct,
}

impl fmt::Display for UnresolvedReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::OpaqueInput => "opaque input",
            Self::ExternalCode => "external code",
            Self::ExternalMemory => "external memory",
            Self::FunctionPointer => "function pointer",
            Self::CrossCrateBoundary => "cross-crate boundary",
            Self::AnalysisLimit => "analysis limit",
            Self::UnsupportedConstruct => "unsupported construct",
        };
        f.write_str(text)
    }
}

/// How completely a language backend resolved an indirect call site.
///
/// Candidate names are emitted only when the backend has evidence that the
/// callable value can reach the call site. `Partial` keeps those proven
/// candidates while recording that another, opaque source may also reach it.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub enum DispatchResolution {
    #[default]
    Complete,
    Partial,
    Unresolved,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct DispatchCandidate {
    pub target: SymbolId,
    pub label: CallLabel,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
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

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct FunctionInfo {
    pub id: SymbolId,
    /// Declaration-shaped label used only when this function is a tree root.
    pub label: CallLabel,
    pub public: bool,
    pub calls: Vec<CallSite>,
    pub span: SourceSpan,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct LanguageFact {
    pub subject: SymbolId,
    pub namespace: LanguageId,
    pub kind: String,
    pub key: String,
    pub value: String,
    pub span: SourceSpan,
}

#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub struct SemanticCallGraph {
    pub functions: Vec<FunctionInfo>,
    pub facts: Vec<LanguageFact>,
    /// Source files successfully consumed by the frontend, including files
    /// that declare no callable functions.
    pub source_files: BTreeSet<PathBuf>,
    /// Compiler-provided roots when the backend has authoritative entry
    /// information. The common graph infers component roots only when empty.
    pub roots: BTreeSet<SymbolId>,
}

/// Compatibility name for the per-file graph fragment returned by source
/// adapters. Project backends return the same language-neutral graph shape.
pub type FileAnalysis = SemanticCallGraph;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallNode {
    pub key: String,
    /// The edge that introduced this node. Roots have no call-site identity.
    pub callsite: Option<CallSiteId>,
    pub label: CallLabel,
    /// The relationship from the parent node to this node. Roots use `Call`.
    pub relation: CallRelation,
    pub children: Vec<CallNode>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CallRelation {
    #[default]
    Call,
    DispatchCandidate,
    /// A recursive call to an ancestor already visible in the current tree.
    /// The node key identifies that ancestor; renderers should draw an edge
    /// back to it rather than repeating its label.
    BackEdge,
}
