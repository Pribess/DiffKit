use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use proc_macro2::Span;
use quote::ToTokens;
use rustc_public::CompilerError;
use rustc_public::crate_def::CrateDef;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{CastKind, PointerCoercion, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{
    AssocContainer, ExistentialTraitRef, RigidTy, TraitRef, Ty, TyKind, VtblEntry,
};
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{
    Expr, ExprCall, ExprClosure, ExprMethodCall, FnArg, ImplItem, Item, ItemFn, ItemImpl,
    ItemTrait, Pat, ReturnType, Signature, TraitItem, Visibility,
};

use super::{FileContext, FrontendResult, LanguageFrontend};
use crate::model::{
    CallLabel, CallSite, CallSyntax, CallTarget, DispatchCandidate, FileAnalysis, FunctionInfo,
    LanguageFact, LanguageId, SourceSpan, SymbolId,
};

#[derive(Default)]
pub struct RustFrontend;

static RUSTC_DRIVER_LOCK: Mutex<()> = Mutex::new(());
static TEMP_SOURCE_SEQUENCE: AtomicU64 = AtomicU64::new(0);

/// Analyze a standalone, compilable Rust source file with rustc's typed MIR.
///
/// The regular [`RustFrontend`] intentionally remains syntax-only. This entry
/// point is used by `rustdiff --semantic` and replaces syntactic targets with
/// the concrete `Instance`s selected by rustc (including monomorphized generic
/// functions and statically dispatched trait methods).
pub fn analyze_semantic_file(path: &Path) -> FrontendResult<FileAnalysis> {
    analyze_semantic_file_with_entries(path, &[])
}

pub fn analyze_semantic_file_with_entries(
    path: &Path,
    entries: &[String],
) -> FrontendResult<FileAnalysis> {
    if !path.is_file() {
        return Err(std::io::Error::other(format!(
            "Rust semantic mode currently requires a standalone .rs file: {}",
            path.display()
        ))
        .into());
    }

    let source = fs::read_to_string(path)?;
    let syntax = RustFrontend.analyze_file(&FileContext { path, module: &[] }, &source)?;
    let semantic = collect_rustc_program(path)?;
    let analysis = merge_semantic_program(syntax.clone(), semantic);
    let missing_entries = entries
        .iter()
        .filter(|entry| entry.contains('<') && !analysis_has_entry(&analysis, entry))
        .cloned()
        .collect::<Vec<_>>();
    if missing_entries.is_empty() {
        return Ok(analysis);
    }

    let Some(seeded_source) = append_entry_seeds(&source, &missing_entries)? else {
        return Ok(analysis);
    };
    let temporary = TemporaryRustSource::create(&seeded_source)?;
    let semantic = collect_rustc_program(&temporary.path())?;
    Ok(merge_semantic_program(syntax, semantic))
}

pub fn analyze_semantic_source(source: &str, entries: &[String]) -> FrontendResult<FileAnalysis> {
    let temporary = TemporaryRustSource::create(source)?;
    analyze_semantic_file_with_entries(&temporary.path(), entries)
}

fn analysis_has_entry(analysis: &FileAnalysis, entry: &str) -> bool {
    let expected = entry.replace('.', "::").replace("::<", "<");
    analysis.functions.iter().any(|function| {
        let label = &function.label.default;
        let callable =
            outer_call_arguments_start(label).map_or(label.as_str(), |index| &label[..index]);
        callable == expected || callable.ends_with(&format!("::{expected}"))
    })
}

fn append_entry_seeds(source: &str, entries: &[String]) -> FrontendResult<Option<String>> {
    let file = syn::parse_file(source)?;
    let mut functions = Vec::new();
    collect_seedable_functions(&file.items, &[], &mut functions);
    let mut seeds = Vec::new();

    for entry in entries {
        let Some(generic_start) = entry.find('<') else {
            continue;
        };
        if !entry.ends_with('>') || entry.starts_with('<') {
            continue;
        }
        let base = entry[..generic_start]
            .trim_end_matches("::")
            .replace('.', "::");
        let generic_arguments = &entry[generic_start + 1..entry.len() - 1];
        let lookup = base.strip_prefix("crate::").unwrap_or(&base);
        let mut matches = functions
            .iter()
            .filter(|function| {
                lookup == function.qualified_name
                    || (!lookup.contains("::") && lookup == function.name)
            })
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            continue;
        }
        let function = matches.pop().expect("one seedable function matched");
        let arguments = (0..function.argument_count)
            .map(|_| "::core::mem::MaybeUninit::uninit().assume_init()")
            .collect::<Vec<_>>()
            .join(", ");
        seeds.push(format!(
            "\n#[doc(hidden)]\n#[allow(dead_code, invalid_value, unused_unsafe)]\nfn __diffkit_seed_{}() {{\n    unsafe {{ let _ = {}::<{}>({}); }}\n}}\n",
            seeds.len(), function.qualified_name, generic_arguments, arguments
        ));
    }

    if seeds.is_empty() {
        Ok(None)
    } else {
        let mut seeded = source.to_owned();
        seeded.extend(seeds);
        Ok(Some(seeded))
    }
}

struct SeedableFunction {
    name: String,
    qualified_name: String,
    argument_count: usize,
}

fn collect_seedable_functions(
    items: &[Item],
    module: &[String],
    functions: &mut Vec<SeedableFunction>,
) {
    for item in items {
        match item {
            Item::Fn(function) => {
                let name = function.sig.ident.to_string();
                let qualified_name = module
                    .iter()
                    .map(String::as_str)
                    .chain(std::iter::once(name.as_str()))
                    .collect::<Vec<_>>()
                    .join("::");
                functions.push(SeedableFunction {
                    name,
                    qualified_name,
                    argument_count: function.sig.inputs.len(),
                });
            }
            Item::Mod(item_mod) => {
                if let Some((_, nested)) = &item_mod.content {
                    let mut nested_module = module.to_vec();
                    nested_module.push(item_mod.ident.to_string());
                    collect_seedable_functions(nested, &nested_module, functions);
                }
            }
            _ => {}
        }
    }
}

impl TemporaryRustSource {
    fn create(source: &str) -> std::io::Result<Self> {
        let sequence = TEMP_SOURCE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir().join(format!(
            "diffkit-rust-source-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory)?;
        let temporary = TemporaryRustSource { directory };
        let path = temporary.directory.join("input.rs");
        fs::write(&path, source)?;
        Ok(temporary)
    }

    fn path(&self) -> PathBuf {
        self.directory.join("input.rs")
    }
}

struct TemporaryRustSource {
    directory: PathBuf,
}

impl Drop for TemporaryRustSource {
    fn drop(&mut self) {
        let _ = fs::remove_file(self.directory.join("input.rs"));
        let _ = fs::remove_dir(&self.directory);
    }
}

#[derive(Debug)]
struct SemanticProgram {
    functions: Vec<SemanticFunction>,
}

#[derive(Debug)]
struct SemanticFunction {
    key: String,
    display: String,
    body_span: SourceSpan,
    calls: Vec<SemanticCall>,
}

#[derive(Debug)]
struct SemanticCall {
    target: SemanticCallTarget,
    definition_name: String,
    span: SourceSpan,
}

#[derive(Debug)]
enum SemanticCallTarget {
    Direct {
        key: String,
        display: String,
    },
    Dynamic {
        dispatch_id: usize,
        key: String,
        display: String,
        candidates: Vec<SemanticDispatchCandidate>,
        open: bool,
    },
}

#[derive(Debug)]
struct SemanticDispatchCandidate {
    key: String,
    display: String,
}

fn collect_rustc_program(path: &Path) -> FrontendResult<SemanticProgram> {
    let _driver_guard = RUSTC_DRIVER_LOCK
        .lock()
        .map_err(|_| std::io::Error::other("rustc semantic driver lock was poisoned"))?;
    let arguments = vec![
        "rustc".to_owned(),
        path.display().to_string(),
        "--crate-name=diffkit_input".to_owned(),
        "--crate-type=lib".to_owned(),
        "--edition=2024".to_owned(),
        "--cap-lints=allow".to_owned(),
    ];

    match rustc_public::run!(&arguments, || {
        std::ops::ControlFlow::<SemanticProgram, ()>::Break(collect_instances())
    }) {
        Err(CompilerError::Interrupted(program)) => Ok(program),
        Err(CompilerError::Failed) => Err(std::io::Error::other(format!(
            "rustc failed to compile {} for semantic analysis",
            path.display()
        ))
        .into()),
        Err(CompilerError::Skipped) => Err(std::io::Error::other(
            "rustc skipped semantic analysis before its callback ran",
        )
        .into()),
        Ok(()) => Err(std::io::Error::other(
            "rustc semantic callback unexpectedly completed without analysis",
        )
        .into()),
    }
}

fn collect_instances() -> SemanticProgram {
    let mut queue = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| matches!(item.kind(), rustc_public::ItemKind::Fn))
        .filter_map(|item| Instance::try_from(item).ok())
        .collect::<VecDeque<_>>();
    let mut visited = HashSet::new();
    let mut functions = Vec::new();
    let mut observed_vtables = Vec::new();
    let mut dynamic_instances = Vec::new();
    let trait_method_implementations = trait_method_implementations();

    loop {
        while let Some(instance) = queue.pop_front() {
            if !visited.insert(instance) {
                continue;
            }
            let Some(body) = instance.body() else {
                continue;
            };

            collect_observed_vtables(&body, &mut observed_vtables);

            let mut calls = Vec::new();
            for block in &body.blocks {
                let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                    continue;
                };
                let Ok(function_type) = func.ty(body.locals()) else {
                    continue;
                };
                let function_kind = function_type.kind();
                let Some((definition, arguments)) = function_kind.fn_def() else {
                    continue;
                };
                let Ok(target) = Instance::resolve(definition, arguments) else {
                    continue;
                };
                let name = target.name();
                let semantic_target = match target.kind {
                    InstanceKind::Virtual { .. } => {
                        let dispatch_id = dynamic_instances.len();
                        dynamic_instances.push(target);
                        SemanticCallTarget::Dynamic {
                            dispatch_id,
                            key: normalize_instance_key(&name),
                            display: normalize_instance_display(&name),
                            candidates: Vec::new(),
                            open: false,
                        }
                    }
                    _ => SemanticCallTarget::Direct {
                        key: normalize_instance_key(&name),
                        display: normalize_instance_display(&name),
                    },
                };

                calls.push(SemanticCall {
                    target: semantic_target,
                    definition_name: target.def.name(),
                    span: rustc_source_span(block.terminator.span),
                });

                if !matches!(target.kind, InstanceKind::Virtual { .. })
                    && target.def.krate().is_local
                    && target.has_body()
                {
                    queue.push_back(target);
                }
            }
            calls.sort_by_key(|call| {
                (
                    call.span.start_line,
                    call.span.start_column,
                    call.span.end_line,
                    call.span.end_column,
                )
            });

            functions.push(SemanticFunction {
                key: normalize_instance_key(&instance.name()),
                display: normalize_instance_display(&instance.name()),
                body_span: rustc_source_span(body.span),
                calls,
            });
        }

        resolve_dynamic_candidates(
            &mut functions,
            &dynamic_instances,
            &observed_vtables,
            &trait_method_implementations,
            &visited,
            &mut queue,
        );
        if queue.is_empty() {
            break;
        }
    }
    functions.sort_by(|left, right| left.key.cmp(&right.key));
    SemanticProgram { functions }
}

fn collect_observed_vtables(body: &rustc_public::mir::Body, observed: &mut Vec<TraitRef>) {
    for block in &body.blocks {
        for statement in &block.statements {
            let StatementKind::Assign(
                _,
                Rvalue::Cast(
                    CastKind::PointerCoercion(PointerCoercion::Unsize),
                    operand,
                    target_ty,
                ),
            ) = &statement.kind
            else {
                continue;
            };
            let Ok(source_ty) = operand.ty(body.locals()) else {
                continue;
            };
            let Some((concrete_ty, principal)) = dyn_coercion(source_ty, *target_ty) else {
                continue;
            };
            let trait_ref = TraitRef::new(principal.def_id, concrete_ty, &principal.generic_args);
            if !observed.contains(&trait_ref) {
                observed.push(trait_ref);
            }
        }
    }
}

fn dyn_coercion(source: Ty, target: Ty) -> Option<(Ty, ExistentialTraitRef)> {
    let target_kind = target.kind();
    if let Some(principal) = target_kind.trait_principal() {
        // A trait upcast (`dyn Child` -> `dyn Parent`) does not reveal a
        // concrete implementation. Only thin-to-wide coercions contribute an
        // RTA candidate here.
        return (!source.kind().is_trait()).then_some((source, principal.value));
    }

    match (source.kind(), target_kind) {
        (
            TyKind::RigidTy(RigidTy::Ref(_, source, _)),
            TyKind::RigidTy(RigidTy::Ref(_, target, _)),
        )
        | (
            TyKind::RigidTy(RigidTy::RawPtr(source, _)),
            TyKind::RigidTy(RigidTy::RawPtr(target, _)),
        ) => dyn_coercion(source, target),
        (
            TyKind::RigidTy(RigidTy::Adt(source_def, source_args)),
            TyKind::RigidTy(RigidTy::Adt(target_def, target_args)),
        ) if source_def == target_def => source_args
            .0
            .iter()
            .zip(&target_args.0)
            .filter_map(|(source, target)| Some((*source.ty()?, *target.ty()?)))
            .find_map(|(source, target)| dyn_coercion(source, target)),
        _ => None,
    }
}

fn trait_method_implementations() -> HashMap<rustc_public::DefId, rustc_public::DefId> {
    rustc_public::all_trait_impls()
        .into_iter()
        .flat_map(|implementation| implementation.associated_items())
        .filter_map(|item| match item.container {
            AssocContainer::TraitImpl(trait_item) => {
                Some((item.def_id.def_id(), trait_item.def_id()))
            }
            AssocContainer::InherentImpl | AssocContainer::Trait => None,
        })
        .collect()
}

fn resolve_dynamic_candidates(
    functions: &mut [SemanticFunction],
    dynamic_instances: &[Instance],
    observed_vtables: &[TraitRef],
    trait_method_implementations: &HashMap<rustc_public::DefId, rustc_public::DefId>,
    visited: &HashSet<Instance>,
    queue: &mut VecDeque<Instance>,
) {
    for call in functions
        .iter_mut()
        .flat_map(|function| &mut function.calls)
    {
        let SemanticCallTarget::Dynamic {
            dispatch_id,
            candidates,
            ..
        } = &mut call.target
        else {
            continue;
        };
        let dispatch = dynamic_instances[*dispatch_id];
        let InstanceKind::Virtual { idx } = dispatch.kind else {
            continue;
        };
        let trait_method = dispatch.def.def_id();

        for trait_ref in observed_vtables {
            let Some(VtblEntry::Method(candidate)) = trait_ref.vtable_entry(idx) else {
                continue;
            };
            let candidate_method = candidate.def.def_id();
            let implements_dispatch = candidate_method == trait_method
                || trait_method_implementations.get(&candidate_method) == Some(&trait_method);
            if !implements_dispatch {
                continue;
            }

            let key = normalize_instance_key(&candidate.name());
            if candidates.iter().any(|existing| existing.key == key) {
                continue;
            }
            candidates.push(SemanticDispatchCandidate {
                key,
                display: normalize_instance_display(&candidate.name()),
            });
            if candidate.def.krate().is_local
                && candidate.has_body()
                && !visited.contains(&candidate)
            {
                queue.push_back(candidate);
            }
        }
        candidates.sort_by(|left, right| left.key.cmp(&right.key));
    }
}

fn merge_semantic_program(syntax: FileAnalysis, semantic: SemanticProgram) -> FileAnalysis {
    let mut analysis = FileAnalysis::default();

    for semantic_function in semantic.functions {
        let Some(template) =
            best_function_template(&syntax.functions, &semantic_function.body_span)
        else {
            // Compiler-generated functions (drop glue, coroutine shims, etc.)
            // are intentionally omitted until they have explicit source syntax.
            continue;
        };
        let id = semantic_symbol(semantic_function.key);
        let mut claimed_calls = HashSet::new();
        let calls = template
            .calls
            .iter()
            .map(|call| {
                let match_index =
                    best_semantic_call(call, &semantic_function.calls, &claimed_calls);
                let mut resolved = call.clone();
                if let Some(index) = match_index {
                    claimed_calls.insert(index);
                    let semantic_call = &semantic_function.calls[index];
                    match &semantic_call.target {
                        SemanticCallTarget::Direct { key, display } => {
                            resolved.target = CallTarget::Direct(semantic_symbol(key.clone()));
                            resolved.label = replace_label_callee(&resolved.label, display);
                        }
                        SemanticCallTarget::Dynamic {
                            key,
                            display,
                            candidates,
                            open,
                            ..
                        } => {
                            resolved.target = CallTarget::Dynamic {
                                dispatch: semantic_symbol(key.clone()),
                                candidates: candidates
                                    .iter()
                                    .map(|candidate| DispatchCandidate {
                                        target: semantic_symbol(candidate.key.clone()),
                                        label: replace_label_callee(
                                            &resolved.label,
                                            &candidate.display,
                                        ),
                                    })
                                    .collect(),
                                open: *open,
                            };
                            resolved.label = replace_label_callee(&resolved.label, display);
                        }
                    }
                }
                resolved
            })
            .collect();

        analysis.functions.push(FunctionInfo {
            id: id.clone(),
            label: replace_label_callee(&template.label, &semantic_function.display),
            public: template.public,
            calls,
            span: template.span.clone(),
        });
        analysis.facts.extend(
            syntax
                .facts
                .iter()
                .filter(|fact| fact.subject == template.id)
                .cloned()
                .map(|mut fact| {
                    fact.subject = id.clone();
                    fact
                }),
        );
    }

    analysis
}

fn best_function_template<'a>(
    functions: &'a [FunctionInfo],
    body_span: &SourceSpan,
) -> Option<&'a FunctionInfo> {
    functions
        .iter()
        .filter(|function| span_contains(&function.span, body_span))
        .min_by_key(|function| span_size(&function.span))
}

fn best_semantic_call(
    syntax_call: &CallSite,
    semantic_calls: &[SemanticCall],
    claimed: &HashSet<usize>,
) -> Option<usize> {
    let syntax_name = match &syntax_call.syntax {
        CallSyntax::Path(parts) => parts.last().map(String::as_str),
        CallSyntax::SelfMethod(method) | CallSyntax::Method { method, .. } => Some(method.as_str()),
    }?;

    semantic_calls
        .iter()
        .enumerate()
        .filter(|(index, call)| {
            !claimed.contains(index) && spans_overlap(&syntax_call.span, &call.span)
        })
        .min_by_key(|(_, call)| {
            let definition_leaf = call
                .definition_name
                .rsplit("::")
                .next()
                .unwrap_or(&call.definition_name);
            let name_penalty = usize::from(definition_leaf != syntax_name) * 1_000_000;
            name_penalty + span_distance(&syntax_call.span, &call.span)
        })
        .map(|(index, _)| index)
}

fn semantic_symbol(name: String) -> SymbolId {
    SymbolId {
        language: LanguageId::new("rust"),
        module: Vec::new(),
        container: None,
        name,
    }
}

fn normalize_instance_key(name: &str) -> String {
    name.replace("::<", "<")
}

fn normalize_instance_display(name: &str) -> String {
    let compact = name.replace("diffkit_input::", "").replace("::<", "<");
    collapse_trait_qualification(&compact)
}

fn collapse_trait_qualification(name: &str) -> String {
    let Some(rest) = name.strip_prefix('<') else {
        return name.to_owned();
    };
    let Some((qualification, method)) = rest.rsplit_once(">::") else {
        return name.to_owned();
    };
    let Some((self_type, _trait_name)) = qualification.rsplit_once(" as ") else {
        return name.to_owned();
    };
    format!("{self_type}::{method}")
}

fn replace_label_callee(label: &CallLabel, callee: &str) -> CallLabel {
    CallLabel {
        default: replace_callee_text(&label.default, callee),
        typed: label
            .typed
            .as_ref()
            .map(|typed| replace_callee_text(typed, callee)),
    }
}

fn replace_callee_text(label: &str, callee: &str) -> String {
    let Some(arguments_start) = outer_call_arguments_start(label) else {
        return callee.to_owned();
    };
    format!("{callee}{}", &label[arguments_start..])
}

fn outer_call_arguments_start(label: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (index, character) in label.char_indices().rev() {
        match character {
            ')' => depth += 1,
            '(' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(index);
                }
            }
            _ => {}
        }
    }
    None
}

fn rustc_source_span(span: rustc_public::ty::Span) -> SourceSpan {
    let lines = span.get_lines();
    SourceSpan {
        file: PathBuf::from(span.get_filename()),
        start_line: lines.start_line,
        start_column: lines.start_col.saturating_sub(1),
        start_byte: None,
        end_line: lines.end_line.max(lines.start_line),
        end_column: lines.end_col.saturating_sub(1),
        end_byte: None,
    }
}

fn span_contains(outer: &SourceSpan, inner: &SourceSpan) -> bool {
    position_le(
        outer.start_line,
        outer.start_column,
        inner.start_line,
        inner.start_column,
    ) && position_le(
        inner.end_line,
        inner.end_column,
        outer.end_line,
        outer.end_column,
    )
}

fn spans_overlap(left: &SourceSpan, right: &SourceSpan) -> bool {
    position_le(
        left.start_line,
        left.start_column,
        right.end_line,
        right.end_column,
    ) && position_le(
        right.start_line,
        right.start_column,
        left.end_line,
        left.end_column,
    )
}

fn position_le(
    left_line: usize,
    left_column: usize,
    right_line: usize,
    right_column: usize,
) -> bool {
    (left_line, left_column) <= (right_line, right_column)
}

fn span_size(span: &SourceSpan) -> usize {
    (span.end_line.saturating_sub(span.start_line) * 10_000)
        + span.end_column.saturating_sub(span.start_column)
}

fn span_distance(left: &SourceSpan, right: &SourceSpan) -> usize {
    left.start_line.abs_diff(right.start_line) * 10_000
        + left.start_column.abs_diff(right.start_column)
}

impl LanguageFrontend for RustFrontend {
    fn language(&self) -> LanguageId {
        LanguageId::new("rust")
    }

    fn extensions(&self) -> &'static [&'static str] {
        &["rs"]
    }

    fn analyze_file(
        &self,
        context: &FileContext<'_>,
        source: &str,
    ) -> FrontendResult<FileAnalysis> {
        let syntax = syn::parse_file(source)?;
        let mut analysis = FileAnalysis::default();
        analyze_items(context.path, context.module, &syntax.items, &mut analysis);
        Ok(analysis)
    }
}

fn analyze_items(file: &Path, module: &[String], items: &[Item], analysis: &mut FileAnalysis) {
    for item in items {
        match item {
            Item::Fn(function) => {
                let function_info = function_from_item(file, module, None, function);
                add_signature_facts(file, &function_info, &function.sig, analysis);
                analysis.functions.push(function_info);
            }
            Item::Impl(item_impl) => analyze_impl(file, module, item_impl, analysis),
            Item::Trait(item_trait) => analyze_trait(file, module, item_trait, analysis),
            Item::Mod(item_mod) => {
                if let Some((_, nested)) = &item_mod.content {
                    let mut nested_module = module.to_vec();
                    nested_module.push(item_mod.ident.to_string());
                    analyze_items(file, &nested_module, nested, analysis);
                }
            }
            _ => {}
        }
    }
}

fn function_from_item(
    file: &Path,
    module: &[String],
    container: Option<String>,
    function: &ItemFn,
) -> FunctionInfo {
    function_from_parts(
        file,
        module,
        container,
        &function.sig,
        &function.block,
        is_public(&function.vis),
        function.span(),
    )
}

fn analyze_impl(file: &Path, module: &[String], item_impl: &ItemImpl, analysis: &mut FileAnalysis) {
    let self_ty = compact_tokens(&item_impl.self_ty);
    let trait_name = item_impl
        .trait_
        .as_ref()
        .map(|(_, path, _)| compact_tokens(path));
    let container = trait_name
        .as_ref()
        .map(|trait_name| format!("{self_ty} as {trait_name}"))
        .unwrap_or_else(|| self_ty.clone());

    for item in &item_impl.items {
        let ImplItem::Fn(method) = item else {
            continue;
        };
        let function = function_from_parts(
            file,
            module,
            Some(container.clone()),
            &method.sig,
            &method.block,
            is_public(&method.vis) || trait_name.is_some(),
            method.span(),
        );

        add_signature_facts(file, &function, &method.sig, analysis);
        if let Some(trait_name) = &trait_name {
            analysis.facts.push(LanguageFact {
                subject: function.id.clone(),
                namespace: LanguageId::new("rust"),
                kind: "impl-trait".to_owned(),
                key: trait_name.clone(),
                value: self_ty.clone(),
                span: function.span.clone(),
            });
        }
        analysis.functions.push(function);
    }
}

fn analyze_trait(
    file: &Path,
    module: &[String],
    item_trait: &ItemTrait,
    analysis: &mut FileAnalysis,
) {
    let trait_name = item_trait.ident.to_string();
    for item in &item_trait.items {
        let TraitItem::Fn(method) = item else {
            continue;
        };
        let Some(block) = &method.default else {
            continue;
        };
        let function = function_from_parts(
            file,
            module,
            Some(trait_name.clone()),
            &method.sig,
            block,
            is_public(&item_trait.vis),
            method.span(),
        );
        add_signature_facts(file, &function, &method.sig, analysis);
        analysis.functions.push(function);
    }
}

fn function_from_parts(
    file: &Path,
    module: &[String],
    container: Option<String>,
    signature: &Signature,
    block: &syn::Block,
    public: bool,
    span: Span,
) -> FunctionInfo {
    let id = SymbolId {
        language: LanguageId::new("rust"),
        module: module.to_vec(),
        container,
        name: signature.ident.to_string(),
    };
    let mut collector = CallCollector {
        file,
        calls: Vec::new(),
    };
    collector.visit_block(block);

    FunctionInfo {
        label: function_label(&id, signature),
        id,
        public,
        calls: collector.calls,
        span: source_span(file, span),
    }
}

fn add_signature_facts(
    file: &Path,
    function: &FunctionInfo,
    signature: &Signature,
    analysis: &mut FileAnalysis,
) {
    for input in &signature.inputs {
        match input {
            FnArg::Receiver(receiver) => {
                let mode = match (&receiver.reference, receiver.mutability.is_some()) {
                    (Some(_), true) => "&mut self",
                    (Some(_), false) => "&self",
                    (None, true) => "mut self",
                    (None, false) => "self",
                };
                analysis.facts.push(LanguageFact {
                    subject: function.id.clone(),
                    namespace: LanguageId::new("rust"),
                    kind: "receiver".to_owned(),
                    key: "self".to_owned(),
                    value: mode.to_owned(),
                    span: source_span(file, receiver.span()),
                });
            }
            FnArg::Typed(argument) => {
                analysis.facts.push(LanguageFact {
                    subject: function.id.clone(),
                    namespace: LanguageId::new("rust"),
                    kind: "parameter".to_owned(),
                    key: compact_tokens(&argument.pat),
                    value: compact_tokens(&argument.ty),
                    span: source_span(file, argument.span()),
                });
            }
        }
    }

    if signature.asyncness.is_some() {
        push_modifier_fact(function, "async", file, signature.span(), analysis);
    }
    if signature.unsafety.is_some() {
        push_modifier_fact(function, "unsafe", file, signature.span(), analysis);
    }
    if signature.constness.is_some() {
        push_modifier_fact(function, "const", file, signature.span(), analysis);
    }
    if let ReturnType::Type(_, ty) = &signature.output {
        analysis.facts.push(LanguageFact {
            subject: function.id.clone(),
            namespace: LanguageId::new("rust"),
            kind: "return-type".to_owned(),
            key: "return".to_owned(),
            value: compact_tokens(ty),
            span: source_span(file, ty.span()),
        });
    }
}

fn push_modifier_fact(
    function: &FunctionInfo,
    modifier: &str,
    file: &Path,
    span: Span,
    analysis: &mut FileAnalysis,
) {
    analysis.facts.push(LanguageFact {
        subject: function.id.clone(),
        namespace: LanguageId::new("rust"),
        kind: "modifier".to_owned(),
        key: modifier.to_owned(),
        value: "true".to_owned(),
        span: source_span(file, span),
    });
}

fn parameter_names(signature: &Signature) -> String {
    signature
        .inputs
        .iter()
        .map(|input| match input {
            FnArg::Receiver(receiver) => match (&receiver.reference, receiver.mutability.is_some())
            {
                (Some(_), true) => "&mut self".to_owned(),
                (Some(_), false) => "&self".to_owned(),
                (None, true) => "mut self".to_owned(),
                (None, false) => "self".to_owned(),
            },
            FnArg::Typed(argument) => pattern_name(&argument.pat),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn function_label(id: &SymbolId, signature: &Signature) -> CallLabel {
    let generic_names = signature
        .generics
        .params
        .iter()
        .map(|parameter| match parameter {
            syn::GenericParam::Lifetime(lifetime) => lifetime.lifetime.to_string(),
            syn::GenericParam::Type(parameter) => parameter.ident.to_string(),
            syn::GenericParam::Const(parameter) => parameter.ident.to_string(),
        })
        .collect::<Vec<_>>();
    let generics = if generic_names.is_empty() {
        String::new()
    } else {
        format!("<{}>", generic_names.join(", "))
    };
    let default = format!(
        "{}{generics}({})",
        id.short_name(),
        parameter_names(signature)
    );
    let typed = format!(
        "{}{generics}({})",
        id.short_name(),
        typed_parameters(signature)
    );
    CallLabel::with_types(default, typed)
}

fn typed_parameters(signature: &Signature) -> String {
    signature
        .inputs
        .iter()
        .map(|input| match input {
            FnArg::Receiver(_) => pattern_name_from_argument(input),
            FnArg::Typed(argument) => {
                format!(
                    "{}: {}",
                    pattern_name(&argument.pat),
                    compact_tokens(&argument.ty)
                )
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn pattern_name_from_argument(argument: &FnArg) -> String {
    match argument {
        FnArg::Receiver(receiver) => match (&receiver.reference, receiver.mutability.is_some()) {
            (Some(_), true) => "&mut self".to_owned(),
            (Some(_), false) => "&self".to_owned(),
            (None, true) => "mut self".to_owned(),
            (None, false) => "self".to_owned(),
        },
        FnArg::Typed(argument) => pattern_name(&argument.pat),
    }
}

fn pattern_name(pattern: &Pat) -> String {
    match pattern {
        Pat::Ident(ident) => ident.ident.to_string(),
        Pat::Reference(reference) => pattern_name(&reference.pat),
        Pat::Wild(_) => "_".to_owned(),
        _ => compact_tokens(pattern),
    }
}

fn is_public(visibility: &Visibility) -> bool {
    matches!(visibility, Visibility::Public(_))
}

fn compact_tokens(tokens: &impl ToTokens) -> String {
    tokens.to_token_stream().to_string().replace(' ', "")
}

fn source_span(file: &Path, span: Span) -> SourceSpan {
    let start = span.start();
    let end = span.end();
    SourceSpan {
        file: file.to_path_buf(),
        start_line: start.line,
        start_column: start.column,
        start_byte: None,
        end_line: end.line.max(start.line),
        end_column: end.column,
        end_byte: None,
    }
}

struct CallCollector<'a> {
    file: &'a Path,
    calls: Vec<CallSite>,
}

impl<'ast> Visit<'ast> for CallCollector<'_> {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if let Some(parts) = callable_path(&node.func) {
            self.calls.push(CallSite {
                syntax: CallSyntax::Path(parts),
                target: CallTarget::Unresolved,
                label: CallLabel::new(call_expression_label(node)),
                span: source_span(self.file, node.span()),
            });
        }
        visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        let method = node.method.to_string();
        let syntax = if is_self_expr(&node.receiver) {
            CallSyntax::SelfMethod(method)
        } else {
            CallSyntax::Method {
                receiver: receiver_name(&node.receiver),
                method,
            }
        };
        self.calls.push(CallSite {
            syntax,
            target: CallTarget::Unresolved,
            label: CallLabel::new(method_call_label(node)),
            span: source_span(self.file, node.span()),
        });
        visit::visit_expr_method_call(self, node);
    }

    // Nested closures and local functions own their calls; do not attribute them
    // to the enclosing function.
    fn visit_expr_closure(&mut self, _node: &'ast ExprClosure) {}

    fn visit_item_fn(&mut self, _node: &'ast ItemFn) {}
}

fn call_expression_label(node: &ExprCall) -> String {
    let function = compact_tokens(&node.func).replace("::<", "<");
    let arguments = node.args.iter().map(compact_tokens).collect::<Vec<_>>();
    format!("{function}({})", arguments.join(", "))
}

fn method_call_label(node: &ExprMethodCall) -> String {
    let receiver = compact_tokens(&node.receiver);
    let generics = node
        .turbofish
        .as_ref()
        .map(compact_tokens)
        .unwrap_or_default()
        .replace("::<", "<");
    let arguments = node.args.iter().map(compact_tokens).collect::<Vec<_>>();
    format!(
        "{receiver}.{}{generics}({})",
        node.method,
        arguments.join(", ")
    )
}

fn callable_path(expression: &Expr) -> Option<Vec<String>> {
    match expression {
        Expr::Path(path) => Some(
            path.path
                .segments
                .iter()
                .map(|segment| segment.ident.to_string())
                .collect(),
        ),
        Expr::Group(group) => callable_path(&group.expr),
        Expr::Paren(paren) => callable_path(&paren.expr),
        _ => None,
    }
}

fn is_self_expr(expression: &Expr) -> bool {
    matches!(expression, Expr::Path(path) if path.path.is_ident("self"))
}

fn receiver_name(expression: &Expr) -> String {
    match expression {
        Expr::Path(path) => path
            .path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect::<Vec<_>>()
            .join("::"),
        _ => "<expr>".to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;

    use super::*;

    #[test]
    fn extracts_functions_methods_calls_and_signature_facts() {
        let source = r#"
            pub trait Store {
                fn save(&mut self, value: Item) {
                    validate(value);
                }
            }

            struct Database;

            impl Store for Database {
                fn save(&mut self, value: Item) {
                    self.prepare();
                    persist(value);
                }
            }
        "#;
        let frontend = RustFrontend;
        let analysis = frontend
            .analyze_file(
                &FileContext {
                    path: Path::new("src/lib.rs"),
                    module: &[],
                },
                source,
            )
            .unwrap();

        assert_eq!(analysis.functions.len(), 2);
        let implementation = analysis
            .functions
            .iter()
            .find(|function| function.id.container.as_deref() == Some("Database as Store"))
            .unwrap();
        assert_eq!(implementation.calls.len(), 2);
        assert!(analysis.facts.iter().any(|fact| {
            fact.subject == implementation.id
                && fact.kind == "receiver"
                && fact.value == "&mut self"
        }));
        assert!(analysis.facts.iter().any(|fact| {
            fact.subject == implementation.id && fact.kind == "impl-trait" && fact.key == "Store"
        }));
    }

    #[test]
    fn rustc_public_can_analyze_a_compilable_file() {
        let directory =
            std::env::temp_dir().join(format!("diffkit-rustc-public-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("input.rs");
        fs::write(&path, "pub fn entry() { helper(); } fn helper() {}\n").unwrap();

        let analysis = analyze_semantic_file(&path).unwrap();

        assert!(
            analysis
                .functions
                .iter()
                .any(|function| function.id.name.ends_with("::entry"))
        );
        assert!(
            analysis
                .functions
                .iter()
                .any(|function| function.id.name.ends_with("::helper"))
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn rustc_public_resolves_generic_trait_dispatch() {
        let directory = std::env::temp_dir().join(format!(
            "diffkit-rustc-public-generics-{}",
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("input.rs");
        fs::write(
            &path,
            r#"
                #[derive(Clone, Copy)]
                pub struct Order;
                trait Store { fn save(&self, order: Order); }
                struct Postgres;
                impl Store for Postgres {
                    fn save(&self, order: Order) {
                        sql::begin();
                        sql::insert(order);
                        sql::commit();
                    }
                }
                struct S3;
                impl Store for S3 {
                    fn save(&self, order: Order) {
                        aws::sign(order);
                        aws::put_object(order);
                    }
                }
                fn run<S: Store>(storage: &S, order: Order) {
                    validate(order);
                    storage.save(order);
                    finalize(order);
                }
                pub fn entry(order: Order) {
                    run(&Postgres, order);
                    run(&S3, order);
                }
                fn validate(_: Order) {}
                fn finalize(_: Order) {}
                mod sql {
                    use super::Order;
                    pub fn begin() {}
                    pub fn insert(_: Order) {}
                    pub fn commit() {}
                }
                mod aws {
                    use super::Order;
                    pub fn sign(_: Order) {}
                    pub fn put_object(_: Order) {}
                }
            "#,
        )
        .unwrap();

        let analysis = analyze_semantic_file(&path).unwrap();
        let labels = analysis
            .functions
            .iter()
            .map(|function| {
                (
                    function.label.default.clone(),
                    function
                        .calls
                        .iter()
                        .map(|call| call.label.default.clone())
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>();
        assert!(labels.iter().any(|(label, calls)| {
            label == "run<Postgres>(storage, order)"
                && calls.iter().any(|call| call == "Postgres::save(order)")
        }));
        assert!(labels.iter().any(|(label, calls)| {
            label == "run<S3>(storage, order)" && calls.iter().any(|call| call == "S3::save(order)")
        }));
        fs::remove_dir_all(directory).unwrap();
    }
}
