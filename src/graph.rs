use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};

use crate::model::{
    CallLabel, CallNode, CallRelation, CallSite, CallSyntax, CallTarget, DispatchCandidate,
    DispatchResolution, FileAnalysis, FunctionInfo, LanguageFact, SymbolId,
};

#[derive(Clone, Debug, Default)]
pub struct ProgramGraph {
    functions: BTreeMap<SymbolId, FunctionInfo>,
    functions_by_name: BTreeMap<(crate::model::LanguageId, String), BTreeSet<SymbolId>>,
    facts: Vec<LanguageFact>,
    source_files: BTreeSet<std::path::PathBuf>,
    declared_roots: BTreeSet<SymbolId>,
}

struct Expansion<'a> {
    max_depth: usize,
    file: Option<&'a std::path::Path>,
    relevant: Option<&'a BTreeSet<SymbolId>>,
    context: Option<&'a BTreeSet<SymbolId>>,
    boundary_marker: Option<&'a str>,
}

/// Identity of a callee subtree for sibling-call presentation. Every source
/// call remains visible; only the last equivalent call expands this subtree.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum CallExpansionKey {
    Direct(SymbolId),
    Dynamic(SymbolId, Vec<SymbolId>, DispatchResolution),
}

impl ProgramGraph {
    pub fn from_files(files: impl IntoIterator<Item = FileAnalysis>) -> Result<Self, String> {
        let mut graph = Self::default();
        for file in files {
            graph.source_files.extend(file.source_files);
            graph.declared_roots.extend(file.roots);
            for function in file.functions {
                graph.source_files.insert(function.span.file.clone());
                if graph.functions.contains_key(&function.id) {
                    return Err(format!("duplicate symbol: {}", function.id));
                }
                graph
                    .functions_by_name
                    .entry((function.id.language.clone(), function.id.name.clone()))
                    .or_default()
                    .insert(function.id.clone());
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

    pub fn resolution_diagnostics(&self) -> Vec<String> {
        let mut diagnostics = BTreeSet::new();
        for function in self.functions.values() {
            for call in &function.calls {
                match &call.target {
                    CallTarget::Dynamic {
                        resolution,
                        evidence,
                        unresolved_reasons,
                        ..
                    } => {
                        let reasons = unresolved_reasons
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ");
                        diagnostics.insert(format!(
                            "{}:{}:{}: {}: {:?}, evidence={evidence}{}",
                            call.span.file.display(),
                            call.span.start_line,
                            call.span.start_column,
                            call.label.default,
                            resolution,
                            if reasons.is_empty() {
                                String::new()
                            } else {
                                format!(", unresolved={reasons}")
                            }
                        ));
                    }
                    CallTarget::Indirect { signature, reason } => {
                        diagnostics.insert(format!(
                            "{}:{}:{}: {}: indirect{}, unresolved={reason}",
                            call.span.file.display(),
                            call.span.start_line,
                            call.span.start_column,
                            call.label.default,
                            signature
                                .as_ref()
                                .map_or_else(String::new, |signature| format!(" ({signature})")),
                        ));
                    }
                    // A direct target outside the analyzed graph is a normal external
                    // leaf, not incomplete resolution. Keep verbose diagnostics focused
                    // on call sites whose candidate completeness needs explanation.
                    CallTarget::Direct(_) | CallTarget::Unresolved => {}
                }
            }
        }
        diagnostics.into_iter().collect()
    }

    pub fn source_files(&self) -> BTreeSet<std::path::PathBuf> {
        self.source_files.clone()
    }

    pub fn analyzes_file(&self, file: &std::path::Path) -> bool {
        self.source_files
            .iter()
            .any(|analyzed| same_file(analyzed, file))
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
        if !self.declared_roots.is_empty() {
            return self
                .declared_roots
                .iter()
                .filter(|root| self.functions.contains_key(*root))
                .cloned()
                .collect();
        }
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
        let match_generic_base = !normalized_entry.contains('<');
        let mut matches = self
            .functions
            .iter()
            .filter(|(id, function)| {
                let qualified = id.qualified_parts().join("::");
                let qualified_context_base = strip_context_suffix(&qualified);
                let name_context_base = strip_context_suffix(&id.name);
                let display = callable_prefix(&function.label.default);
                id.to_string() == entry
                    || id.short_name() == entry
                    || id.name == entry
                    || qualified == normalized_entry
                    || qualified.ends_with(&format!("::{normalized_entry}"))
                    || display == entry
                    || display == normalized_entry
                    || (match_generic_base
                        && [qualified_context_base, name_context_base, display]
                            .into_iter()
                            .flat_map(callable_aliases)
                            .any(|alias| {
                                alias == entry
                                    || alias == normalized_entry
                                    || alias.ends_with(&format!("::{normalized_entry}"))
                            }))
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

    /// Resolve only definitions whose bodies belong to `file`. This keeps an
    /// explicit entry in file mode from silently selecting an equally named
    /// function in another project file.
    pub fn resolve_entries_in_file(
        &self,
        entry: &str,
        file: &std::path::Path,
    ) -> Result<Vec<SymbolId>, String> {
        let matches = self.resolve_entries(entry)?;
        Ok(matches
            .into_iter()
            .filter(|symbol| {
                self.functions
                    .get(symbol)
                    .is_some_and(|function| same_file(&function.span.file, file))
            })
            .collect())
    }

    fn same_contextual_function(&self, symbols: &[SymbolId]) -> bool {
        let Some((first_symbol, remaining)) = symbols.split_first() else {
            return true;
        };
        let Some(first) = self.functions.get(first_symbol) else {
            return false;
        };
        let first_display = strip_generic_arguments(callable_prefix(&first.label.default));
        remaining.iter().all(|symbol| {
            let Some(function) = self.functions.get(symbol) else {
                return false;
            };
            strip_generic_arguments(callable_prefix(&function.label.default)) == first_display
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
        let expansion = Expansion {
            max_depth,
            file,
            relevant: None,
            context: None,
            boundary_marker: None,
        };
        Some(self.expand(
            entry,
            None,
            CallRelation::Call,
            0,
            &expansion,
            &mut HashSet::new(),
        ))
    }

    pub(crate) fn build_diff_call_tree(
        &self,
        entry: &SymbolId,
        max_depth: usize,
        file: Option<&std::path::Path>,
        relevant: &BTreeSet<SymbolId>,
        context: &BTreeSet<SymbolId>,
        boundary_marker: &str,
    ) -> Option<CallNode> {
        self.functions.get(entry)?;
        let expansion = Expansion {
            max_depth,
            file,
            relevant: Some(relevant),
            context: Some(context),
            boundary_marker: Some(boundary_marker),
        };
        Some(self.expand(
            entry,
            None,
            CallRelation::Call,
            0,
            &expansion,
            &mut HashSet::new(),
        ))
    }

    /// A function's local call shape, without expanding callees. Dynamic
    /// dispatch candidates remain part of the shape because changing the
    /// candidate set is itself a call-graph change.
    pub(crate) fn local_call_shape(
        &self,
        symbol: &SymbolId,
        file: Option<&std::path::Path>,
    ) -> Option<CallNode> {
        let function = self.functions.get(symbol)?;
        let expansion = Expansion {
            max_depth: 2,
            file,
            relevant: None,
            context: None,
            boundary_marker: None,
        };
        let mut visiting = HashSet::from([symbol.clone()]);
        let children = function
            .calls
            .iter()
            .map(|call| {
                let dynamic = matches!(call.target, CallTarget::Dynamic { .. });
                let mut node = self.expand_call(symbol, call, 1, &expansion, true, &mut visiting);
                if !dynamic {
                    node.children.clear();
                } else {
                    for candidate in &mut node.children {
                        candidate.children.clear();
                    }
                }
                node
            })
            .collect();
        Some(CallNode {
            key: symbol.to_string(),
            callsite: None,
            // Declaration labels are only visible when the function itself is
            // selected as an entry. They must not propagate to every caller.
            label: CallLabel::new(""),
            relation: CallRelation::Call,
            children,
        })
    }

    /// Return every function in this graph that can reach one of `targets`.
    /// This graph-level pass is linear in the call graph and avoids first
    /// materializing a potentially exponential call tree.
    pub(crate) fn symbols_reaching(
        &self,
        targets: &BTreeSet<SymbolId>,
        file: Option<&std::path::Path>,
    ) -> BTreeSet<SymbolId> {
        let included = |symbol: &SymbolId| {
            self.functions.get(symbol).is_some_and(|function| {
                file.is_none_or(|file| same_file(&function.span.file, file))
            })
        };
        let mut reverse = BTreeMap::<SymbolId, BTreeSet<SymbolId>>::new();
        for (caller, function) in &self.functions {
            if !included(caller) {
                continue;
            }
            for call in &function.calls {
                for target in self.call_targets(caller, call) {
                    if included(&target) {
                        reverse.entry(target).or_default().insert(caller.clone());
                    }
                }
            }
        }

        let mut reaching = BTreeSet::new();
        let mut pending = targets
            .iter()
            .filter(|target| included(target))
            .cloned()
            .collect::<VecDeque<_>>();
        while let Some(symbol) = pending.pop_front() {
            if !reaching.insert(symbol.clone()) {
                continue;
            }
            if let Some(callers) = reverse.get(&symbol) {
                pending.extend(callers.iter().cloned());
            }
        }
        reaching
    }

    pub(crate) fn dispatch_context_symbols(
        &self,
        file: Option<&std::path::Path>,
    ) -> BTreeSet<SymbolId> {
        let dispatchers = self
            .functions
            .iter()
            .filter(|(_, function)| {
                file.is_none_or(|file| same_file(&function.span.file, file))
                    && function
                        .calls
                        .iter()
                        .any(|call| matches!(call.target, CallTarget::Dynamic { .. }))
            })
            .map(|(symbol, _)| symbol.clone())
            .collect();
        self.symbols_reaching(&dispatchers, file)
    }

    #[allow(clippy::too_many_arguments)]
    fn expand(
        &self,
        symbol: &SymbolId,
        callsite_label: Option<&CallLabel>,
        relation: CallRelation,
        depth: usize,
        expansion: &Expansion<'_>,
        visiting: &mut HashSet<SymbolId>,
    ) -> CallNode {
        let function = self
            .functions
            .get(symbol)
            .expect("expanded symbols must exist in the function index");
        let label = callsite_label
            .cloned()
            .unwrap_or_else(|| function.label.clone());

        if depth >= expansion.max_depth {
            let children = expansion
                .boundary_marker
                .filter(|_| {
                    expansion
                        .relevant
                        .is_some_and(|relevant| relevant.contains(symbol))
                })
                .map(|marker| CallNode {
                    key: format!("{symbol}#{marker}"),
                    callsite: None,
                    label: CallLabel::new(""),
                    relation: CallRelation::Call,
                    children: Vec::new(),
                })
                .into_iter()
                .collect();
            return CallNode {
                key: symbol.to_string(),
                callsite: None,
                label,
                relation,
                children,
            };
        }

        if !visiting.insert(symbol.clone()) {
            return CallNode {
                key: symbol.to_string(),
                callsite: None,
                label,
                relation: CallRelation::BackEdge,
                children: Vec::new(),
            };
        }

        let last_expansions = function
            .calls
            .iter()
            .enumerate()
            .filter_map(|(index, call)| {
                self.call_expansion_key(symbol, call)
                    .map(|key| (key, index))
            })
            .collect::<BTreeMap<_, _>>();
        let children = function
            .calls
            .iter()
            .enumerate()
            .map(|(index, call)| {
                let expand_target = self
                    .call_expansion_key(symbol, call)
                    .is_none_or(|key| last_expansions.get(&key) == Some(&index));
                self.expand_call(symbol, call, depth + 1, expansion, expand_target, visiting)
            })
            .collect();

        visiting.remove(symbol);
        CallNode {
            key: symbol.to_string(),
            callsite: None,
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
        expansion: &Expansion<'_>,
        expand_target: bool,
        visiting: &mut HashSet<SymbolId>,
    ) -> CallNode {
        match &call.target {
            CallTarget::Dynamic {
                dispatch,
                candidates,
                resolution,
                ..
            } => {
                let mut node = self.expand_dynamic_call(
                    dispatch,
                    &call.label,
                    candidates,
                    *resolution,
                    depth,
                    expansion,
                    expand_target,
                    visiting,
                );
                node.callsite = Some(call.id.clone());
                node
            }
            CallTarget::Direct(target) => {
                let mut node = self.expand_direct_call(
                    target.clone(),
                    &call.label,
                    CallRelation::Call,
                    depth,
                    expansion,
                    expand_target,
                    visiting,
                );
                node.callsite = Some(call.id.clone());
                node
            }
            CallTarget::Indirect { .. } => CallNode {
                key: format!("{}://indirect/{}", caller.language, call.id.0),
                callsite: Some(call.id.clone()),
                label: call.label.with_suffix(" [indirect]"),
                relation: CallRelation::Call,
                children: Vec::new(),
            },
            CallTarget::Unresolved => {
                let target = self.resolve_call(caller, &call.syntax);
                if let Some(target) = target {
                    let mut node = self.expand_direct_call(
                        target,
                        &call.label,
                        CallRelation::Call,
                        depth,
                        expansion,
                        expand_target,
                        visiting,
                    );
                    node.callsite = Some(call.id.clone());
                    node
                } else {
                    CallNode {
                        key: format!("{}://?{}", caller.language, call.syntax.key_fragment()),
                        callsite: Some(call.id.clone()),
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
        expansion: &Expansion<'_>,
        expand_target: bool,
        visiting: &mut HashSet<SymbolId>,
    ) -> CallNode {
        let can_expand = self.functions.get(&target).is_some_and(|function| {
            expansion
                .file
                .is_none_or(|file| same_file(&function.span.file, file))
        }) && expansion.relevant.is_none_or(|relevant| {
            relevant.contains(&target)
                || expansion
                    .context
                    .is_some_and(|context| context.contains(&target))
        });
        if can_expand && expand_target {
            self.expand(&target, Some(label), relation, depth, expansion, visiting)
        } else {
            CallNode {
                key: target.to_string(),
                callsite: None,
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
        expansion: &Expansion<'_>,
        expand_target: bool,
        visiting: &mut HashSet<SymbolId>,
    ) -> CallNode {
        let children = if !expand_target
            || depth >= expansion.max_depth
            || resolution == DispatchResolution::Unresolved
        {
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
                        expansion,
                        true,
                        visiting,
                    )
                })
                .chain(
                    (resolution == DispatchResolution::Partial).then(|| CallNode {
                        key: format!("{dispatch}#unresolved"),
                        callsite: None,
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
            callsite: None,
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
            CallTarget::Indirect { .. } => Vec::new(),
            CallTarget::Unresolved => self
                .resolve_call(caller, &call.syntax)
                .into_iter()
                .collect(),
        }
    }

    fn call_expansion_key(&self, caller: &SymbolId, call: &CallSite) -> Option<CallExpansionKey> {
        match &call.target {
            CallTarget::Direct(target) => Some(CallExpansionKey::Direct(target.clone())),
            CallTarget::Unresolved => self
                .resolve_call(caller, &call.syntax)
                .map(CallExpansionKey::Direct),
            CallTarget::Dynamic {
                dispatch,
                candidates,
                resolution,
                ..
            } => Some(CallExpansionKey::Dynamic(
                dispatch.clone(),
                candidates
                    .iter()
                    .map(|candidate| candidate.target.clone())
                    .collect(),
                *resolution,
            )),
            CallTarget::Indirect { .. } => None,
        }
    }

    fn resolve_call(&self, caller: &SymbolId, call: &CallSyntax) -> Option<SymbolId> {
        let mut preferred = Vec::new();

        match call {
            CallSyntax::SelfMethod(method) => {
                if let Some(container) = &caller.container {
                    preferred.extend(self.named_symbols(&caller.language, method).filter(
                        |candidate| {
                            candidate.module == caller.module
                                && candidate.container.as_ref() == Some(container)
                        },
                    ));
                }
            }
            CallSyntax::Path(parts) if !parts.is_empty() => {
                let name = parts.last().expect("non-empty path");
                if parts.first().is_some_and(|part| part == "Self") {
                    if let Some(container) = &caller.container {
                        preferred.extend(self.named_symbols(&caller.language, name).filter(
                            |candidate| {
                                candidate.module == caller.module
                                    && candidate.container.as_ref() == Some(container)
                            },
                        ));
                    }
                } else if parts.len() == 1 {
                    preferred.extend(self.named_symbols(&caller.language, name).filter(
                        |candidate| {
                            candidate.module == caller.module && candidate.container.is_none()
                        },
                    ));
                } else {
                    preferred.extend(
                        self.named_symbols(&caller.language, name)
                            .filter(|candidate| path_suffix_matches(candidate, parts)),
                    );
                }
            }
            CallSyntax::Method { receiver, method } => {
                // Static-looking receiver names can be matched without type inference.
                if receiver.chars().next().is_some_and(char::is_uppercase) {
                    preferred.extend(self.named_symbols(&caller.language, method).filter(
                        |candidate| {
                            candidate
                                .container
                                .as_deref()
                                .is_some_and(|container| base_container(container) == receiver)
                        },
                    ));
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
        let fallback = unique(self.named_symbols(&caller.language, name));
        (fallback.len() == 1).then(|| fallback[0].clone())
    }

    fn named_symbols<'a>(
        &'a self,
        language: &crate::model::LanguageId,
        name: &str,
    ) -> impl Iterator<Item = &'a SymbolId> {
        self.functions_by_name
            .get(&(language.clone(), name.to_owned()))
            .into_iter()
            .flatten()
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

fn strip_generic_arguments(value: &str) -> String {
    let mut stripped = String::with_capacity(value.len());
    let mut depth = 0usize;
    for character in value.chars() {
        match character {
            '<' => depth += 1,
            '>' if depth > 0 => depth -= 1,
            _ if depth == 0 => stripped.push(character),
            _ => {}
        }
    }
    stripped
}

fn callable_aliases(value: &str) -> Vec<String> {
    if let Some((self_type, trait_name, method)) = qualified_trait_callable(value) {
        let self_type = strip_generic_arguments(self_type);
        let trait_name = strip_generic_arguments(trait_name);
        let method = strip_generic_arguments(method);
        return vec![
            format!("{self_type} as {trait_name}::{method}"),
            format!("{self_type}::{method}"),
            format!("{trait_name}::{method}"),
        ];
    }
    let callable = strip_generic_arguments(value);
    let mut aliases = vec![callable.clone()];
    if let Some((self_type, trait_method)) = callable.split_once(" as ")
        && let Some((_, method)) = trait_method.rsplit_once("::")
    {
        aliases.push(format!("{self_type}::{method}"));
        aliases.push(trait_method.to_owned());
    }
    aliases
}

fn qualified_trait_callable(value: &str) -> Option<(&str, &str, &str)> {
    if !value.starts_with('<') {
        return None;
    }
    let mut depth = 0usize;
    let mut qualification_end = None;
    for (index, character) in value.char_indices() {
        match character {
            '<' => depth += 1,
            '>' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    qualification_end = Some(index);
                    break;
                }
            }
            _ => {}
        }
    }
    let qualification_end = qualification_end?;
    let qualification = &value[1..qualification_end];
    let method = value[qualification_end + 1..].strip_prefix("::")?;
    let (self_type, trait_name) = qualification.rsplit_once(" as ")?;
    Some((self_type, trait_name, method))
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
