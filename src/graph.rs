use std::collections::{BTreeMap, BTreeSet, HashSet};

use crate::model::{
    CallLabel, CallNode, CallRelation, CallSite, CallSyntax, CallTarget, DispatchCandidate,
    DispatchResolution, FileAnalysis, FunctionInfo, LanguageFact, SymbolId,
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

    pub fn source_files(&self) -> BTreeSet<std::path::PathBuf> {
        self.functions
            .values()
            .map(|function| function.span.file.clone())
            .collect()
    }

    pub fn has_functions_in_file(&self, file: &std::path::Path) -> bool {
        self.functions
            .values()
            .any(|function| same_file(&function.span.file, file))
    }

    pub fn public_symbols(&self) -> BTreeSet<SymbolId> {
        self.functions
            .values()
            .filter(|function| function.public)
            .map(|function| function.id.clone())
            .collect()
    }

    /// Return one deterministic root for every source component in the graph.
    /// Functions with no incoming call are natural roots. A closed recursive
    /// component has no such function, so its earliest source definition is
    /// used as that component's presentation root.
    pub fn inferred_roots(&self) -> BTreeSet<SymbolId> {
        let mut incoming = self
            .functions
            .keys()
            .cloned()
            .map(|symbol| (symbol, 0usize))
            .collect::<BTreeMap<_, _>>();
        let mut adjacency = BTreeMap::<SymbolId, BTreeSet<SymbolId>>::new();

        for (caller, function) in &self.functions {
            for call in &function.calls {
                for target in self.call_targets(caller, call) {
                    if self.functions.contains_key(&target) {
                        *incoming.entry(target.clone()).or_default() += 1;
                        adjacency.entry(caller.clone()).or_default().insert(target);
                    }
                }
            }
        }

        let natural = incoming
            .iter()
            .filter_map(|(symbol, count)| (*count == 0).then_some(symbol.clone()))
            .collect::<BTreeSet<_>>();
        let mut covered = BTreeSet::new();
        for root in &natural {
            mark_reachable(root, &adjacency, &mut covered);
        }

        let mut roots = natural;
        while let Some(uncovered) = self
            .functions
            .values()
            .filter(|function| !covered.contains(&function.id))
            .min_by_key(|function| {
                (
                    function.span.file.clone(),
                    function.span.start_line,
                    function.span.start_column,
                    function.id.clone(),
                )
            })
            .map(|function| function.id.clone())
        {
            roots.insert(uncovered.clone());
            mark_reachable(&uncovered, &adjacency, &mut covered);
        }
        roots
    }

    pub fn roots_in_file(&self, file: &std::path::Path) -> BTreeSet<SymbolId> {
        let functions = self
            .functions
            .values()
            .filter(|function| same_file(&function.span.file, file))
            .map(|function| function.id.clone())
            .collect::<BTreeSet<_>>();
        if functions.is_empty() {
            return BTreeSet::new();
        }

        let mut incoming = functions
            .iter()
            .cloned()
            .map(|symbol| (symbol, 0usize))
            .collect::<BTreeMap<_, _>>();
        let mut adjacency = BTreeMap::<SymbolId, BTreeSet<SymbolId>>::new();
        for caller in &functions {
            let Some(function) = self.functions.get(caller) else {
                continue;
            };
            for call in &function.calls {
                for target in self.call_targets(caller, call) {
                    if functions.contains(&target) {
                        *incoming.entry(target.clone()).or_default() += 1;
                        adjacency.entry(caller.clone()).or_default().insert(target);
                    }
                }
            }
        }

        let natural = incoming
            .iter()
            .filter_map(|(symbol, count)| (*count == 0).then_some(symbol.clone()))
            .collect::<BTreeSet<_>>();
        let mut covered = BTreeSet::new();
        for root in &natural {
            mark_reachable(root, &adjacency, &mut covered);
        }
        let mut roots = natural;
        while let Some(uncovered) = functions.iter().find(|symbol| !covered.contains(*symbol)) {
            roots.insert(uncovered.clone());
            mark_reachable(uncovered, &adjacency, &mut covered);
        }
        roots
    }

    pub fn resolve_entry(&self, entry: &str) -> Result<Option<SymbolId>, String> {
        let mut matches = self.resolve_entries(entry)?;
        match matches.len() {
            0 => Ok(None),
            1 => Ok(matches.pop()),
            _ => Err(format!(
                "entry `{entry}` resolves to multiple call contexts: {}",
                matches
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
        }
    }

    /// Resolve an entry to all compiler-proven call contexts of the same
    /// source function. Ordinary name ambiguity remains an error.
    pub fn resolve_entries(&self, entry: &str) -> Result<Vec<SymbolId>, String> {
        let normalized_entry = entry.replace('.', "::");
        let mut matches = self
            .functions
            .iter()
            .filter(|(id, function)| {
                let qualified = id.qualified_parts().join("::");
                let qualified_base = strip_context_suffix(&qualified);
                let name_base = strip_context_suffix(&id.name);
                let display = callable_prefix(&function.label.default);
                id.to_string() == entry
                    || id.short_name() == entry
                    || id.name == entry
                    || name_base == entry
                    || qualified == normalized_entry
                    || qualified_base == normalized_entry
                    || qualified.ends_with(&format!("::{normalized_entry}"))
                    || qualified_base.ends_with(&format!("::{normalized_entry}"))
                    || display == entry
                    || display == normalized_entry
            })
            .map(|(id, _)| id.clone())
            .collect::<Vec<_>>();
        matches.sort();
        matches.dedup();

        if matches.len() <= 1 || self.same_contextual_function(&matches) {
            Ok(matches)
        } else {
            Err(format!(
                "entry `{entry}` is ambiguous: {}",
                matches
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ))
        }
    }

    fn same_contextual_function(&self, symbols: &[SymbolId]) -> bool {
        let Some((first_symbol, remaining)) = symbols.split_first() else {
            return true;
        };
        let Some(first) = self.functions.get(first_symbol) else {
            return false;
        };
        let first_key = strip_context_suffix(&first_symbol.name);
        remaining.iter().all(|symbol| {
            let Some(function) = self.functions.get(symbol) else {
                return false;
            };
            let key = strip_context_suffix(&symbol.name);
            key == first_key
                && function.label.default == first.label.default
                && function.span == first.span
        })
    }

    pub fn build_call_tree(&self, entry: &SymbolId, max_depth: usize) -> Option<CallNode> {
        self.build_call_tree_in_file(entry, max_depth, None)
    }

    pub fn build_call_tree_in_file(
        &self,
        entry: &SymbolId,
        max_depth: usize,
        file: Option<&std::path::Path>,
    ) -> Option<CallNode> {
        self.functions.get(entry)?;
        Some(self.expand(
            entry,
            None,
            CallRelation::Call,
            0,
            max_depth,
            file,
            &mut HashSet::new(),
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn expand(
        &self,
        symbol: &SymbolId,
        callsite_label: Option<&CallLabel>,
        relation: CallRelation,
        depth: usize,
        max_depth: usize,
        file: Option<&std::path::Path>,
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
                label: CallLabel::new(""),
                relation: CallRelation::BackEdge,
                children: Vec::new(),
            };
        }

        let children = function
            .calls
            .iter()
            .map(|call| self.expand_call(symbol, call, depth + 1, max_depth, file, visiting))
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
        file: Option<&std::path::Path>,
        visiting: &mut HashSet<SymbolId>,
    ) -> CallNode {
        match &call.target {
            CallTarget::Dynamic {
                dispatch,
                candidates,
                resolution,
            } => self.expand_dynamic_call(
                dispatch,
                &call.label,
                candidates,
                *resolution,
                depth,
                max_depth,
                file,
                visiting,
            ),
            CallTarget::Direct(target) => self.expand_direct_call(
                target.clone(),
                &call.label,
                CallRelation::Call,
                depth,
                max_depth,
                file,
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
                        file,
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

    #[allow(clippy::too_many_arguments)]
    fn expand_direct_call(
        &self,
        target: SymbolId,
        label: &CallLabel,
        relation: CallRelation,
        depth: usize,
        max_depth: usize,
        file: Option<&std::path::Path>,
        visiting: &mut HashSet<SymbolId>,
    ) -> CallNode {
        let can_expand = self
            .functions
            .get(&target)
            .is_some_and(|function| file.is_none_or(|file| same_file(&function.span.file, file)));
        if can_expand {
            self.expand(
                &target,
                Some(label),
                relation,
                depth,
                max_depth,
                file,
                visiting,
            )
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
        resolution: DispatchResolution,
        depth: usize,
        max_depth: usize,
        file: Option<&std::path::Path>,
        visiting: &mut HashSet<SymbolId>,
    ) -> CallNode {
        let children = if depth >= max_depth || resolution == DispatchResolution::Unresolved {
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
                        file,
                        visiting,
                    )
                })
                .chain(
                    (resolution == DispatchResolution::Partial).then(|| CallNode {
                        key: format!("{dispatch}#unresolved"),
                        label: CallLabel::new("… unresolved targets"),
                        relation: CallRelation::DispatchCandidate,
                        children: Vec::new(),
                    }),
                )
                .collect()
        };

        let label = match resolution {
            DispatchResolution::Complete => label.clone(),
            DispatchResolution::Partial => label.with_suffix(" [partial]"),
            DispatchResolution::Unresolved => label.with_suffix(" [unresolved]"),
        };

        CallNode {
            key: dispatch.to_string(),
            label,
            relation: CallRelation::Call,
            children,
        }
    }

    fn call_targets(&self, caller: &SymbolId, call: &CallSite) -> Vec<SymbolId> {
        match &call.target {
            CallTarget::Direct(target) => vec![target.clone()],
            CallTarget::Dynamic { candidates, .. } => candidates
                .iter()
                .map(|candidate| candidate.target.clone())
                .collect(),
            CallTarget::Unresolved => self
                .resolve_call(caller, &call.syntax)
                .into_iter()
                .collect(),
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

fn mark_reachable(
    root: &SymbolId,
    adjacency: &BTreeMap<SymbolId, BTreeSet<SymbolId>>,
    covered: &mut BTreeSet<SymbolId>,
) {
    if !covered.insert(root.clone()) {
        return;
    }
    if let Some(targets) = adjacency.get(root) {
        for target in targets {
            mark_reachable(target, adjacency, covered);
        }
    }
}

fn same_file(left: &std::path::Path, right: &std::path::Path) -> bool {
    left == right
        || left
            .canonicalize()
            .ok()
            .zip(right.canonicalize().ok())
            .is_some_and(|(left, right)| left == right)
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

fn strip_context_suffix(value: &str) -> &str {
    value.split_once("#ctx[").map_or(value, |(base, _)| base)
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
