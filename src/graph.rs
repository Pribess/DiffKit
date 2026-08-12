use std::collections::{BTreeMap, BTreeSet, HashSet};

use crate::model::{
    CallLabel, CallNode, CallRelation, CallSite, CallSyntax, CallTarget, DispatchCandidate,
    FileAnalysis, FunctionInfo, LanguageFact, SymbolId,
};

#[derive(Clone, Debug, Default)]
pub struct ProgramGraph {
    functions: BTreeMap<SymbolId, FunctionInfo>,
    facts: Vec<LanguageFact>,
}

impl ProgramGraph {
    pub fn from_files(files: impl IntoIterator<Item = FileAnalysis>) -> Result<Self, String> {
        let mut graph = Self::default();
        for file in files {
            for function in file.functions {
                if graph.functions.contains_key(&function.id) {
                    return Err(format!("duplicate symbol: {}", function.id));
                }
                graph.functions.insert(function.id.clone(), function);
            }
            graph.facts.extend(file.facts);
        }
        Ok(graph)
    }

    pub fn functions(&self) -> &BTreeMap<SymbolId, FunctionInfo> {
        &self.functions
    }

    pub fn facts(&self) -> &[LanguageFact] {
        &self.facts
    }

    pub fn public_symbols(&self) -> BTreeSet<SymbolId> {
        self.functions
            .values()
            .filter(|function| function.public)
            .map(|function| function.id.clone())
            .collect()
    }

    pub fn resolve_entry(&self, entry: &str) -> Result<Option<SymbolId>, String> {
        let normalized_entry = entry.replace('.', "::");
        let mut matches = self
            .functions
            .iter()
            .filter(|(id, function)| {
                let qualified = id.qualified_parts().join("::");
                let display = callable_prefix(&function.label.default);
                id.to_string() == entry
                    || id.short_name() == entry
                    || id.name == entry
                    || qualified == normalized_entry
                    || qualified.ends_with(&format!("::{normalized_entry}"))
                    || display == entry
                    || display == normalized_entry
            })
            .map(|(id, _)| id.clone())
            .collect::<Vec<_>>();
        matches.sort();
        matches.dedup();

        match matches.len() {
            0 => Ok(None),
            1 => Ok(matches.pop()),
            _ => Err(format!(
                "entry `{entry}` is ambiguous: {}",
                matches
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
        }
    }

    pub fn build_call_tree(&self, entry: &SymbolId, max_depth: usize) -> Option<CallNode> {
        self.functions.get(entry)?;
        Some(self.expand(
            entry,
            None,
            CallRelation::Call,
            0,
            max_depth,
            &mut HashSet::new(),
        ))
    }

    fn expand(
        &self,
        symbol: &SymbolId,
        callsite_label: Option<&CallLabel>,
        relation: CallRelation,
        depth: usize,
        max_depth: usize,
        visiting: &mut HashSet<SymbolId>,
    ) -> CallNode {
        let function = self
            .functions
            .get(symbol)
            .expect("expanded symbols must exist in the function index");
        let label = callsite_label
            .cloned()
            .unwrap_or_else(|| function.label.clone());

        if depth >= max_depth {
            return CallNode {
                key: symbol.to_string(),
                label,
                relation,
                children: Vec::new(),
            };
        }

        if !visiting.insert(symbol.clone()) {
            return CallNode {
                key: symbol.to_string(),
                label: label.with_suffix(" ⇄"),
                relation,
                children: Vec::new(),
            };
        }

        let children = function
            .calls
            .iter()
            .map(|call| self.expand_call(symbol, call, depth + 1, max_depth, visiting))
            .collect();

        visiting.remove(symbol);
        CallNode {
            key: symbol.to_string(),
            label,
            relation,
            children,
        }
    }

    fn expand_call(
        &self,
        caller: &SymbolId,
        call: &CallSite,
        depth: usize,
        max_depth: usize,
        visiting: &mut HashSet<SymbolId>,
    ) -> CallNode {
        match &call.target {
            CallTarget::Dynamic {
                dispatch,
                candidates,
                open,
            } => self.expand_dynamic_call(
                dispatch,
                &call.label,
                candidates,
                *open,
                depth,
                max_depth,
                visiting,
            ),
            CallTarget::Direct(target) => self.expand_direct_call(
                target.clone(),
                &call.label,
                CallRelation::Call,
                depth,
                max_depth,
                visiting,
            ),
            CallTarget::Unresolved => {
                let target = self.resolve_call(caller, &call.syntax);
                if let Some(target) = target {
                    self.expand_direct_call(
                        target,
                        &call.label,
                        CallRelation::Call,
                        depth,
                        max_depth,
                        visiting,
                    )
                } else {
                    CallNode {
                        key: format!("{}://?{}", caller.language, call.syntax.key_fragment()),
                        label: call.label.clone(),
                        relation: CallRelation::Call,
                        children: Vec::new(),
                    }
                }
            }
        }
    }

    fn expand_direct_call(
        &self,
        target: SymbolId,
        label: &CallLabel,
        relation: CallRelation,
        depth: usize,
        max_depth: usize,
        visiting: &mut HashSet<SymbolId>,
    ) -> CallNode {
        if self.functions.contains_key(&target) {
            self.expand(&target, Some(label), relation, depth, max_depth, visiting)
        } else {
            CallNode {
                key: target.to_string(),
                label: label.clone(),
                relation,
                children: Vec::new(),
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn expand_dynamic_call(
        &self,
        dispatch: &SymbolId,
        label: &CallLabel,
        candidates: &[DispatchCandidate],
        open: bool,
        depth: usize,
        max_depth: usize,
        visiting: &mut HashSet<SymbolId>,
    ) -> CallNode {
        let children = if depth >= max_depth {
            Vec::new()
        } else {
            candidates
                .iter()
                .map(|candidate| {
                    self.expand_direct_call(
                        candidate.target.clone(),
                        &candidate.label,
                        CallRelation::DispatchCandidate,
                        depth + 1,
                        max_depth,
                        visiting,
                    )
                })
                .chain(open.then(|| CallNode {
                    key: format!("{dispatch}#external"),
                    label: CallLabel::new("? external implementation"),
                    relation: CallRelation::DispatchCandidate,
                    children: Vec::new(),
                }))
                .collect()
        };

        CallNode {
            key: dispatch.to_string(),
            label: label.clone(),
            relation: CallRelation::Call,
            children,
        }
    }

    fn resolve_call(&self, caller: &SymbolId, call: &CallSyntax) -> Option<SymbolId> {
        let mut preferred = Vec::new();

        match call {
            CallSyntax::SelfMethod(method) => {
                if let Some(container) = &caller.container {
                    preferred.extend(self.functions.keys().filter(|candidate| {
                        candidate.language == caller.language
                            && candidate.module == caller.module
                            && candidate.container.as_ref() == Some(container)
                            && candidate.name == *method
                    }));
                }
            }
            CallSyntax::Path(parts) if !parts.is_empty() => {
                let name = parts.last().expect("non-empty path");
                if parts.first().is_some_and(|part| part == "Self") {
                    if let Some(container) = &caller.container {
                        preferred.extend(self.functions.keys().filter(|candidate| {
                            candidate.language == caller.language
                                && candidate.module == caller.module
                                && candidate.container.as_ref() == Some(container)
                                && candidate.name == *name
                        }));
                    }
                } else if parts.len() == 1 {
                    preferred.extend(self.functions.keys().filter(|candidate| {
                        candidate.language == caller.language
                            && candidate.module == caller.module
                            && candidate.container.is_none()
                            && candidate.name == *name
                    }));
                } else {
                    preferred.extend(self.functions.keys().filter(|candidate| {
                        candidate.language == caller.language
                            && candidate.name == *name
                            && path_suffix_matches(candidate, parts)
                    }));
                }
            }
            CallSyntax::Method { receiver, method } => {
                // Static-looking receiver names can be matched without type inference.
                if receiver.chars().next().is_some_and(char::is_uppercase) {
                    preferred.extend(self.functions.keys().filter(|candidate| {
                        candidate.language == caller.language
                            && candidate.name == *method
                            && candidate
                                .container
                                .as_deref()
                                .is_some_and(|container| base_container(container) == receiver)
                    }));
                }
            }
            CallSyntax::Path(_) => {}
        }

        let preferred = unique(preferred);
        if preferred.len() == 1 {
            return preferred.into_iter().next().cloned();
        }
        if preferred.len() > 1 {
            return None;
        }

        let name = match call {
            CallSyntax::Path(parts) => parts.last()?,
            CallSyntax::SelfMethod(method) | CallSyntax::Method { method, .. } => method,
        };
        let fallback =
            unique(self.functions.keys().filter(|candidate| {
                candidate.language == caller.language && candidate.name == *name
            }));
        (fallback.len() == 1).then(|| fallback[0].clone())
    }
}

fn callable_prefix(label: &str) -> &str {
    let mut depth = 0usize;
    for (index, character) in label.char_indices().rev() {
        match character {
            ')' => depth += 1,
            '(' => {
                let Some(next_depth) = depth.checked_sub(1) else {
                    return label;
                };
                depth = next_depth;
                if depth == 0 {
                    return &label[..index];
                }
            }
            _ => {}
        }
    }
    label
}

fn unique<'a>(values: impl IntoIterator<Item = &'a SymbolId>) -> Vec<&'a SymbolId> {
    values
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn base_container(container: &str) -> &str {
    container
        .split_once(" as ")
        .map_or(container, |(base, _)| base)
}

fn path_suffix_matches(candidate: &SymbolId, raw: &[String]) -> bool {
    let raw = raw
        .iter()
        .filter(|part| !matches!(part.as_str(), "crate" | "self" | "super"))
        .map(String::as_str)
        .collect::<Vec<_>>();
    let candidate = candidate.qualified_parts();
    raw.len() <= candidate.len() && candidate[candidate.len() - raw.len()..] == raw
}
