#![feature(rustc_private)]

use diffkit::graph::ProgramGraph;
use diffkit::language::ocaml::OcamlFrontend;
use diffkit::language::{FileContext, LanguageBackend};
use diffkit::model::{CallRelation, CallSyntax};
use diffkit::{
    ColorMode, DiffOptions, DiffReport, RenderOptions, ocamldiff_sources,
    render_call_tree_with_options, render_report_with_options,
};
use std::path::Path;

fn render_plain(report: &DiffReport) -> String {
    render_report_with_options(
        report,
        &RenderOptions {
            show_types: false,
            color: ColorMode::Plain,
        },
    )
}

#[test]
fn renders_ocaml_calls_in_native_application_syntax() {
    let before = include_str!("../examples/ocaml/before.ml");
    let after = include_str!("../examples/ocaml/after.ml");

    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "ocamldiff before.ml → after.ml\n\n  run order\n  ├─ validate order\n  ├─ Postgres.save order\n+ │  ├─ Sql.begin_tx order\n  │  ├─ Sql.insert order\n+ │  └─ Sql.commit order\n  └─ finalize order"
    );
}

#[test]
fn preserves_curried_labeled_optional_and_unit_arguments() {
    let before = r#"
        let charge ~currency order amount = ()
        let find ?limit ~tenant key = ()
        let commit () = ()

        let run order =
          charge ~currency:"KRW" order 100;
          find ?limit:None ~tenant:"acme" order;
          commit ()
    "#;
    let after = before.replace("100", "200");

    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        &after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "ocamldiff before.ml → after.ml\n\n  run order\n- ├─ charge ~currency:\"KRW\" order 100\n+ ├─ charge ~currency:\"KRW\" order 200\n  ├─ find ?limit:None ~tenant:\"acme\" order\n  └─ commit ()"
    );
}

#[test]
fn preserves_repeated_ocaml_call_sites_and_all_arguments() {
    let before = r#"
        let touch first second third = ()
        let run first second third =
          touch first second third;
          touch first second third;
          touch first second third
    "#;
    let after = r#"
        let touch first second third = ()
        let run first second third =
          touch first second third;
          touch first second third;
          touch first second third;
          touch first second third
    "#;

    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "ocamldiff before.ml → after.ml\n\n  run first second third\n  ├─ touch first second third\n  ├─ touch first second third\n  ├─ touch first second third\n+ └─ touch first second third"
    );
}

#[test]
fn expands_only_the_last_repeated_call_to_the_same_function() {
    let source = r#"
        let leaf first second third = ()
        let touch first second third = leaf first second third
        let run first second third =
          touch first second third;
          touch second third first;
          touch third first second
    "#;
    let path = Path::new("calls.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(
        tree.children
            .iter()
            .map(|call| call.label.default.as_str())
            .collect::<Vec<_>>(),
        [
            "touch first second third",
            "touch second third first",
            "touch third first second",
        ]
    );
    assert!(tree.children[0].children.is_empty());
    assert!(tree.children[1].children.is_empty());
    assert_eq!(tree.children[2].children.len(), 1);
    assert_eq!(
        tree.children[2].children[0].label.default,
        "leaf first second third"
    );
}

#[test]
fn connects_only_the_last_repeated_recursive_call_back_to_its_ancestor() {
    let source = "let rec walk value = walk value; walk value; walk value";
    let path = Path::new("recursive.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let walk = graph.resolve_entry("walk").unwrap().unwrap();
    let tree = graph.build_call_tree(&walk, 8).unwrap();

    assert_eq!(tree.children.len(), 3);
    assert_eq!(tree.children[0].relation, CallRelation::Call);
    assert_eq!(tree.children[1].relation, CallRelation::Call);
    assert_eq!(tree.children[2].relation, CallRelation::BackEdge);

    let rendered = render_call_tree_with_options(
        &tree,
        &RenderOptions {
            show_types: false,
            color: ColorMode::Plain,
        },
    );
    assert!(rendered.lines().next().unwrap().contains('◀'), "{rendered}");
}

#[test]
fn keeps_all_arguments_on_recursive_back_edges() {
    let before = r#"
        let rec walk left right = walk left right
    "#;
    let after = r#"
        let finish left right = ()
        let rec walk left right =
          walk left right;
          finish left right
    "#;

    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &DiffOptions {
            entries: vec!["walk".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);

    assert_eq!(rendered.matches("walk left right").count(), 2, "{rendered}");
    assert!(rendered.contains("├─ walk left right"), "{rendered}");
    assert!(rendered.contains("finish left right"), "{rendered}");
    assert!(rendered.contains('◀'), "{rendered}");
    assert!(rendered.contains('┘'), "{rendered}");
}

#[test]
fn treats_unrelated_before_and_after_roots_as_removed_and_added_forests() {
    let report = ocamldiff_sources(
        "before.ml",
        "let old x = helper x\nand helper x = x\n",
        "after.ml",
        "let replacement x = worker x\nand worker x = x\n",
        &DiffOptions::default(),
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "ocamldiff before.ml → after.ml\n\n- old x\n- └─ helper x\n\n+ replacement x\n+ └─ worker x"
    );
}

#[test]
fn includes_changed_detached_components_as_their_own_trees() {
    let report = ocamldiff_sources(
        "before.ml",
        "let entry x = stable x\nand stable x = x\nlet detached x = old_leaf x\nand old_leaf x = x\n",
        "after.ml",
        "let entry x = stable x\nand stable x = x\nlet detached x = new_leaf x\nand new_leaf x = x\n",
        &DiffOptions::default(),
    )
    .unwrap();

    assert_eq!(report.trees.len(), 1);
    assert_eq!(report.trees[0].entry.name, "detached");
    let rendered = render_plain(&report);
    assert!(rendered.contains("- ├─ old_leaf x"), "{rendered}");
    assert!(rendered.contains("+ └─ new_leaf x"), "{rendered}");
}

#[test]
fn repeats_a_changed_shared_subtree_under_each_real_root() {
    let before =
        "let left x = shared x\nlet right x = shared x\nand shared x = leaf x\nand leaf x = x\n";
    let after = "let left x = shared x\nlet right x = shared x\nand shared x = leaf x; added x\nand leaf x = x\nand added x = x\n";
    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &DiffOptions::default(),
    )
    .unwrap();

    assert_eq!(
        report
            .trees
            .iter()
            .map(|tree| tree.entry.name.as_str())
            .collect::<Vec<_>>(),
        ["left", "right"]
    );
}

#[test]
fn renders_local_ocaml_functions_as_closure_nodes() {
    let before = r#"
        let write value = ()
        let run order =
          let persist value = write value in
          persist order
    "#;
    let after = r#"
        let write value = ()
        let commit value = ()
        let run order =
          let persist value = write value; commit value in
          persist order
    "#;
    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "ocamldiff before.ml → after.ml\n\n  run order\n  └─ persist order [closure#0]\n     ├─ write value\n+    └─ commit value"
    );
}

#[test]
fn marks_ocaml_object_method_calls_unresolved_without_runtime_targets() {
    let before = "let run store order = store#save order";
    let after = "let run store order = store#save order; finish order\nlet finish order = ()";
    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);
    assert!(
        rendered.contains("store#save order [unresolved]"),
        "{rendered}"
    );
}

#[test]
fn resolves_ocaml_function_parameters_from_connected_callers() {
    let before = r#"
        let write value = ()
        let postgres_save value = write value
        let run save value = save value
        let entry value = run postgres_save value
    "#;
    let after = r#"
        let write value = ()
        let commit value = ()
        let postgres_save value = write value; commit value
        let run save value = save value
        let entry value = run postgres_save value
    "#;
    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &DiffOptions {
            entries: vec!["entry".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);
    assert!(rendered.contains("run postgres_save value"), "{rendered}");
    assert!(rendered.contains("╚═ postgres_save value"), "{rendered}");
    assert!(rendered.contains("commit value"), "{rendered}");
    assert!(!rendered.contains("[unresolved]"), "{rendered}");
}

#[test]
fn keeps_internal_and_root_function_value_contexts_separate() {
    let before = r#"
        let local value = write value
        and write value = ()
        let run save value = save value
        let internal value = run local value
        let external save value = run save value
    "#;
    let after = r#"
        let local value = write value; finish value
        and write value = ()
        and finish value = ()
        let run save value = save value
        let internal value = run local value
        let external save value = run save value
    "#;
    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);
    assert!(rendered.contains("╚═ local value"), "{rendered}");
    assert!(!rendered.contains("[partial]"), "{rendered}");
    assert!(!rendered.contains("… unresolved targets"), "{rendered}");
}

#[test]
fn marks_an_opaque_ocaml_function_parameter_unresolved() {
    let before = "let run save value = save value";
    let after = "let run save value = save value; finish value\nlet finish value = ()";
    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);
    assert!(rendered.contains("save value [unresolved]"), "{rendered}");
    assert!(!rendered.contains("… unresolved targets"), "{rendered}");
}

#[test]
fn marks_a_join_of_local_and_opaque_ocaml_function_values_partial() {
    let before = r#"
        let write value = ()
        let local value = write value
        let run save value = save value
        let wrapper save choose_local value =
          run (if choose_local then local else save) value
    "#;
    let after = r#"
        let write value = ()
        let finish value = ()
        let local value = write value; finish value
        let run save value = save value
        let wrapper save choose_local value =
          run (if choose_local then local else save) value
    "#;
    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &DiffOptions {
            entries: vec!["wrapper".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);
    assert!(rendered.contains("save value [partial]"), "{rendered}");
    assert!(rendered.contains("╠═ local value"), "{rendered}");
    assert!(rendered.contains("… unresolved targets"), "{rendered}");
}

#[test]
fn accepts_ocaml_qualified_entry_names() {
    let before = include_str!("../examples/ocaml/before.ml");
    let after = include_str!("../examples/ocaml/after.ml");
    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &DiffOptions {
            entries: vec!["Postgres.save".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "ocamldiff before.ml → after.ml\n\n  Postgres.save order\n+ ├─ Sql.begin_tx order\n  ├─ Sql.insert order\n+ └─ Sql.commit order"
    );
}

#[test]
fn unresolved_qualified_paths_do_not_bind_to_an_unrelated_same_named_function() {
    let source = r#"
        module Database = struct
          let save value = write value
          let write value = value
        end
        module Make = struct
          let run value = wrong value
          let wrong value = value
        end
        let entry value =
          Alias.save value;
          Service.run value
    "#;
    let path = Path::new("qualified.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let entry = graph.resolve_entry("entry").unwrap().unwrap();
    let tree = graph.build_call_tree(&entry, 8).unwrap();

    assert_eq!(tree.children.len(), 2, "{tree:#?}");
    assert!(
        tree.children.iter().all(|call| call.children.is_empty()),
        "{tree:#?}"
    );
    assert_eq!(tree.children[0].label.default, "Alias.save value");
    assert_eq!(tree.children[1].label.default, "Service.run value");
}

#[test]
fn ocaml_local_open_calls_keep_the_opened_module_path() {
    let source = r#"
        module Database = struct
          let save value = write value
          let write value = ()
        end
        let run value = Database.(save value)
    "#;
    let path = Path::new("local-open.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "Database.save value");
    assert_eq!(tree.children[0].children[0].label.default, "write value");
}

#[test]
fn ocaml_module_aliases_resolve_to_the_aliased_definition() {
    let source = r#"
        module Database = struct
          let save value = write value
          let write value = ()
        end
        module Alias = Database
        let run value = Alias.save value
    "#;
    let path = Path::new("module-alias.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "Alias.save value");
    assert_eq!(tree.children[0].children[0].label.default, "write value");
}

#[test]
fn ocaml_functor_instances_substitute_their_module_argument() {
    let source = r#"
        module Database = struct
          let save value = write value
          let write value = ()
        end
        module Make (Store : sig val save : int -> unit end) = struct
          let run value = Store.save value
        end
        module Service = Make (Database)
        let entry value = Service.run value
    "#;
    let path = Path::new("functor-instance.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let entry = graph.resolve_entry("entry").unwrap().unwrap();
    let tree = graph.build_call_tree(&entry, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "Service.run value");
    assert_eq!(
        tree.children[0].children[0].label.default,
        "Database.save value"
    );
    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "write value"
    );
}

#[test]
fn ocaml_curried_functors_substitute_each_module_argument() {
    let source = r#"
        module Database = struct let save value = value end
        module Logger = struct let record value = value end
        module Make
          (Store : sig val save : int -> int end)
          (Audit : sig val record : int -> int end) = struct
          let run value = Audit.record (Store.save value)
        end
        module Service = Make (Database) (Logger)
        let entry value = Service.run value
    "#;
    let path = Path::new("curried-functor.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let entry = graph.resolve_entry("entry").unwrap().unwrap();
    let tree = graph.build_call_tree(&entry, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "Service.run value");
    assert_eq!(
        tree.children[0]
            .children
            .iter()
            .map(|call| call.label.default.as_str())
            .collect::<Vec<_>>(),
        ["Database.save value", "Logger.record (Database.save value)"]
    );
}

#[test]
fn explicit_ocaml_callable_expressions_are_not_dropped() {
    let source = r#"
        type handler = { run : int -> unit }
        let choose callback = callback
        let leaf value = ()
        let entry handler value =
          (choose leaf) value;
          handler.run value
    "#;
    let path = Path::new("callables.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let entry = analysis
        .functions
        .iter()
        .find(|function| function.id.name == "entry")
        .unwrap();

    assert_eq!(
        entry
            .calls
            .iter()
            .map(|call| call.label.default.as_str())
            .collect::<Vec<_>>(),
        ["choose leaf", "(choose leaf) value", "handler.run value"]
    );
    assert!(matches!(entry.calls[1].syntax, CallSyntax::Expression(_)));
    assert!(matches!(entry.calls[2].syntax, CallSyntax::Expression(_)));
}

#[test]
fn returned_ocaml_function_values_form_an_exact_candidate_set() {
    let source = r#"
        let write value = ()
        let upload value = ()
        let choose use_upload = if use_upload then upload else write
        let run use_upload value = (choose use_upload) value
    "#;
    let path = Path::new("returned.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let returned_call = &tree.children[1];

    assert_eq!(returned_call.label.default, "(choose use_upload) value");
    assert_eq!(
        returned_call
            .children
            .iter()
            .map(|candidate| candidate.label.default.as_str())
            .collect::<Vec<_>>(),
        ["upload value", "write value"]
    );
    assert!(
        returned_call
            .children
            .iter()
            .all(|candidate| candidate.relation == CallRelation::DispatchCandidate)
    );
}

#[test]
fn returned_ocaml_parameter_values_keep_the_callers_context() {
    let source = r#"
        let write value = ()
        let identity callback = callback
        let run value = (identity write) value
    "#;
    let path = Path::new("returned-parameter.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(tree.children[1].children.len(), 1, "{tree:#?}");
    assert_eq!(tree.children[1].children[0].label.default, "write value");
}

#[test]
fn callable_values_flow_through_destructured_tuple_parameters() {
    let source = r#"
        let write value = ()
        let apply_pair (callback, value) = callback value
        let run value = apply_pair (write, value)
    "#;
    let path = Path::new("tuple-callback.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "apply_pair (write, value)");
    assert_eq!(tree.children[0].children[0].label.default, "callback value");
    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "write value"
    );
}

#[test]
fn immutable_tuple_projections_keep_the_exact_callable_candidates() {
    let source = r#"
        let write value = write_leaf value
        let upload value = upload_leaf value
        let write_leaf value = ()
        let upload_leaf value = ()
        let run flag value =
          let callbacks = (write, upload) in
          let selected = if flag then fst callbacks else snd callbacks in
          selected value
    "#;
    let path = Path::new("tuple-projection.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let selected = tree
        .children
        .iter()
        .find(|call| call.label.default == "selected value")
        .unwrap();

    assert_eq!(
        selected
            .children
            .iter()
            .map(|candidate| candidate.label.default.as_str())
            .collect::<Vec<_>>(),
        ["upload value", "write value"]
    );
    assert!(
        selected
            .children
            .iter()
            .all(|candidate| candidate.relation == CallRelation::DispatchCandidate)
    );
}

#[test]
fn destructured_local_tuple_bindings_keep_each_callable_projection() {
    let source = r#"
        let write value = write_leaf value
        let upload value = upload_leaf value
        let write_leaf value = ()
        let upload_leaf value = ()
        let run value =
          let (first, second) = (write, upload) in
          first value;
          second value
    "#;
    let path = Path::new("local-tuple-binding.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "first value");
    assert_eq!(tree.children[0].children[0].label.default, "write value");
    assert_eq!(tree.children[1].label.default, "second value");
    assert_eq!(tree.children[1].children[0].label.default, "upload value");
}

#[test]
fn callable_values_flow_through_constructor_parameters() {
    let source = r#"
        type callback = Callback of (int -> unit)
        let write value = leaf value
        let leaf value = ()
        let invoke (Callback callback) value = callback value
        let run value = invoke (Callback write) value
    "#;
    let path = Path::new("constructor-callback.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = format!("{tree:#?}");

    assert_eq!(
        tree.children[0].label.default,
        "invoke (Callback write) value"
    );
    assert_eq!(tree.children[0].children[0].label.default, "callback value");
    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "write value"
    );
    assert_eq!(
        tree.children[0].children[0].children[0].children[0]
            .label
            .default,
        "leaf value"
    );
    assert!(!rendered.contains("Unresolved"), "{rendered}");
}

#[test]
fn callable_values_refined_by_a_match_pattern_keep_their_constructor_payload() {
    let source = r#"
        type callback = Callback of (int -> unit)
        let write value = leaf value
        let leaf value = ()
        let invoke wrapped value =
          match wrapped with
          | Callback callback -> callback value
        let run value = invoke (Callback write) value
    "#;
    let path = Path::new("matched-constructor-callback.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = format!("{tree:#?}");

    assert_eq!(tree.children[0].children[0].label.default, "callback value");
    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "write value"
    );
    assert_eq!(
        tree.children[0].children[0].children[0].children[0]
            .label
            .default,
        "leaf value"
    );
    assert!(!rendered.contains("Unresolved"), "{rendered}");
}

#[test]
fn callable_values_flow_through_record_parameters() {
    let source = r#"
        type handler = { callback : int -> unit }
        let write value = leaf value
        let leaf value = ()
        let invoke { callback } value = callback value
        let run value = invoke { callback = write } value
    "#;
    let path = Path::new("record-parameter-callback.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = format!("{tree:#?}");

    assert_eq!(
        tree.children[0].label.default,
        "invoke { callback = write } value"
    );
    assert_eq!(tree.children[0].children[0].label.default, "callback value");
    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "write value"
    );
    assert_eq!(
        tree.children[0].children[0].children[0].children[0]
            .label
            .default,
        "leaf value"
    );
    assert!(!rendered.contains("Unresolved"), "{rendered}");
}

#[test]
fn local_function_value_aliases_shadow_same_named_global_functions() {
    let source = r#"
        let write value = wrong value
        let upload value = right value
        let wrong value = ()
        let right value = ()
        let run value =
          let write = upload in
          write value
    "#;
    let path = Path::new("local-alias.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "write value");
    assert_eq!(tree.children[0].children[0].label.default, "upload value");
    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "right value"
    );
    assert!(!format!("{tree:#?}").contains("wrong value"), "{tree:#?}");
}

#[test]
fn a_nonrecursive_local_alias_rhs_uses_the_outer_binding() {
    let source = r#"
        let write value = leaf value
        let leaf value = ()
        let run value =
          let write = write in
          write value
    "#;
    let path = Path::new("nonrecursive-alias.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "write value");
    assert_eq!(tree.children[0].children[0].label.default, "write value");
    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "leaf value"
    );
}

#[test]
fn local_function_scope_does_not_leak_past_its_let_body() {
    let source = r#"
        let write value = global_leaf value
        let global_leaf value = ()
        let local_leaf value = ()
        let run value =
          let first =
            let write item = local_leaf item in
            write value
          in
          write first
    "#;
    let path = Path::new("local-function-scope.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = format!("{tree:#?}");

    assert_eq!(tree.children.len(), 2, "{rendered}");
    assert_eq!(tree.children[0].label.default, "write value [closure#0]");
    assert_eq!(
        tree.children[0].children[0].label.default,
        "local_leaf item"
    );
    assert_eq!(tree.children[1].label.default, "write first");
    assert_eq!(
        tree.children[1].children[0].label.default,
        "global_leaf value"
    );
}

#[test]
fn top_level_shadowed_bindings_keep_source_order_identity() {
    let source = r#"
        let old_leaf value = ()
        let new_leaf value = ()
        let write value = old_leaf value
        let before value = write value
        let write value = new_leaf value
        let after value = write value
    "#;
    let path = Path::new("top-level-shadow.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let before = graph.resolve_entry("before").unwrap().unwrap();
    let after = graph.resolve_entry("after").unwrap().unwrap();
    let before = graph.build_call_tree(&before, 8).unwrap();
    let after = graph.build_call_tree(&after, 8).unwrap();

    assert_eq!(before.children[0].label.default, "write value");
    assert_eq!(
        before.children[0].children[0].label.default,
        "old_leaf value"
    );
    assert_eq!(after.children[0].label.default, "write value");
    assert_eq!(
        after.children[0].children[0].label.default,
        "new_leaf value"
    );
}

#[test]
fn a_shadowing_recursive_binding_calls_its_new_definition() {
    let source = r#"
        let old_leaf () = ()
        let new_leaf () = ()
        let rec walk count = old_leaf ()
        let before count = walk count
        let rec walk count =
          if count = 0 then new_leaf () else walk (count - 1)
        let after count = walk count
    "#;
    let path = Path::new("shadowing-recursive-binding.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let before = graph.resolve_entry("before").unwrap().unwrap();
    let after = graph.resolve_entry("after").unwrap().unwrap();
    let before = graph.build_call_tree(&before, 8).unwrap();
    let after = graph.build_call_tree(&after, 8).unwrap();
    let rendered = format!("{after:#?}");

    assert_eq!(before.children[0].children[0].label.default, "old_leaf ()");
    assert!(
        after.children[0]
            .children
            .iter()
            .any(|call| call.label.default == "new_leaf ()"),
        "{rendered}"
    );
    assert!(
        after.children[0]
            .children
            .iter()
            .any(|call| call.relation == CallRelation::BackEdge),
        "{rendered}"
    );
}

#[test]
fn an_explicit_shadowed_entry_selects_the_last_exported_binding() {
    let source = r#"
        let old_leaf value = ()
        let new_leaf value = ()
        let write value = old_leaf value
        let write value = new_leaf value
    "#;
    let path = Path::new("shadowed-entry.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let write = graph.resolve_entry("write").unwrap().unwrap();
    let tree = graph.build_call_tree(&write, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "new_leaf value");
}

#[test]
fn a_shadowing_mutual_recursive_group_uses_its_own_members() {
    let source = r#"
        let old_leaf value = ()
        let right value = old_leaf value
        let rec left value = right value
        and right value = if value = 0 then () else left (value - 1)
        let run value = left value
    "#;
    let path = Path::new("shadowing-mutual-recursion.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = format!("{tree:#?}");

    assert_eq!(tree.children[0].label.default, "left value");
    assert_eq!(tree.children[0].children[0].label.default, "right value");
    assert_eq!(
        tree.children[0].children[0].children[0].relation,
        CallRelation::BackEdge,
        "{rendered}"
    );
    assert!(!rendered.contains("old_leaf value"), "{rendered}");
}

#[test]
fn typed_anonymous_function_parameters_keep_their_lambda_identity() {
    let source = r#"
        let leaf value = ()
        let run () = (fun (value : int) -> leaf value) 1
    "#;
    let path = Path::new("typed-anonymous-function.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = format!("{tree:#?}");

    assert_eq!(tree.children[0].label.default, "λ#1 1", "{rendered}");
    assert_eq!(
        tree.children[0].children[0].label.default, "leaf value",
        "{rendered}"
    );
}

#[test]
fn aliases_of_in_scope_named_local_functions_keep_the_local_target() {
    let source = r#"
        let leaf value = ()
        let run value =
          let write item = leaf item in
          let callback = write in
          callback value
    "#;
    let path = Path::new("local-function-alias.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "callback value");
    assert_eq!(
        tree.children[0].children[0].label.default,
        "write value [closure#0]"
    );
    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "leaf item"
    );
}

#[test]
fn identical_anonymous_function_expressions_keep_distinct_call_sites() {
    let source = r#"
        let leaf value = ()
        let run value =
          (fun item -> leaf item) value;
          (fun item -> leaf item) value
    "#;
    let path = Path::new("identical-lambdas.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = format!("{tree:#?}");

    assert_eq!(tree.children.len(), 2, "{rendered}");
    assert_eq!(tree.children[0].label.default, "λ#1 value");
    assert_eq!(tree.children[1].label.default, "λ#2 value");
    assert!(
        tree.children
            .iter()
            .all(|lambda| lambda.children[0].label.default == "leaf item"),
        "{rendered}"
    );
}

#[test]
fn known_record_function_fields_form_exact_dispatch_edges() {
    let source = r#"
        type handler = { run : int -> unit }
        let write value = leaf value
        let leaf value = ()
        let execute value =
          let handler = { run = write } in
          handler.run value
    "#;
    let path = Path::new("record-flow.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let execute = graph.resolve_entry("execute").unwrap().unwrap();
    let tree = graph.build_call_tree(&execute, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "handler.run value");
    assert_eq!(tree.children[0].children[0].label.default, "write value");
    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "leaf value"
    );
    assert!(!format!("{tree:#?}").contains("Unresolved"), "{tree:#?}");
}

#[test]
fn record_updates_preserve_unchanged_function_fields_and_replace_changed_ones() {
    let source = r#"
        type handler = { run : int -> unit; stop : int -> unit }
        let write value = write_leaf value
        let upload value = upload_leaf value
        let stop value = stop_leaf value
        let write_leaf value = ()
        let upload_leaf value = ()
        let stop_leaf value = ()
        let execute value =
          let base = { run = write; stop } in
          let changed = { base with run = upload } in
          changed.run value;
          changed.stop value
    "#;
    let path = Path::new("record-update-flow.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let execute = graph.resolve_entry("execute").unwrap().unwrap();
    let tree = graph.build_call_tree(&execute, 8).unwrap();
    let rendered = format!("{tree:#?}");

    assert_eq!(tree.children.len(), 2, "{rendered}");
    assert_eq!(tree.children[0].children[0].label.default, "upload value");
    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "upload_leaf value"
    );
    assert_eq!(tree.children[1].children[0].label.default, "stop value");
    assert_eq!(
        tree.children[1].children[0].children[0].label.default,
        "stop_leaf value"
    );
    assert!(!rendered.contains("write_leaf"), "{rendered}");
}

#[test]
fn conditional_local_function_values_keep_all_and_only_branch_candidates() {
    let source = r#"
        let write value = local value
        let upload value = remote value
        let unused value = wrong value
        let local value = ()
        let remote value = ()
        let wrong value = ()
        let run choose_upload value =
          let callback = if choose_upload then upload else write in
          callback value
    "#;
    let path = Path::new("conditional-local-flow.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "callback value");
    assert_eq!(
        tree.children[0]
            .children
            .iter()
            .map(|candidate| candidate.label.default.as_str())
            .collect::<Vec<_>>(),
        ["upload value", "write value"]
    );
    assert!(
        tree.children[0]
            .children
            .iter()
            .all(|candidate| candidate.relation == CallRelation::DispatchCandidate)
    );
    assert!(!format!("{tree:#?}").contains("unused"), "{tree:#?}");
}

#[test]
fn first_class_module_arguments_resolve_the_called_module_member() {
    let source = r#"
        module type STORE = sig val save : int -> unit end
        module Database = struct
          let save value = write value
          let write value = ()
        end
        let persist (module Store : STORE) value = Store.save value
        let run value = persist (module Database) value
    "#;
    let path = Path::new("first-class-module.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(
        tree.children[0].label.default,
        "persist (module Database) value"
    );
    assert_eq!(
        tree.children[0].children[0].label.default,
        "Store.save value"
    );
    assert_eq!(tree.children[0].children[0].children.len(), 1, "{tree:#?}");
    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "Database.save value"
    );
    assert_eq!(
        tree.children[0].children[0].children[0].children[0]
            .label
            .default,
        "write value"
    );
    assert_eq!(
        tree.children[0].children[0].children[0].relation,
        CallRelation::DispatchCandidate
    );
}

#[test]
fn first_class_modules_keep_their_identity_through_wrappers() {
    let source = r#"
        module type STORE = sig val save : int -> unit end
        module Database = struct
          let save value = write value
          let write value = ()
        end
        let persist (module Store : STORE) value = Store.save value
        let forward store value = persist store value
        let run value = forward (module Database) value
    "#;
    let path = Path::new("first-class-module-wrapper.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = format!("{tree:#?}");

    assert!(rendered.contains("Database.save value"), "{rendered}");
    assert!(rendered.contains("write value"), "{rendered}");
    assert!(!rendered.contains("Unresolved"), "{rendered}");
}

#[test]
fn unresolved_ocaml_callable_expressions_are_marked_instead_of_silent() {
    let source = r#"
        type handler = { run : int -> unit }
        let execute handler value = handler.run value
    "#;
    let path = Path::new("record-call.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let execute = graph.resolve_entry("execute").unwrap().unwrap();
    let tree = graph.build_call_tree(&execute, 8).unwrap();

    assert_eq!(
        tree.children[0].label.default,
        "handler.run value [unresolved]"
    );
}

#[test]
fn anonymous_ocaml_functions_are_connected_as_lambda_nodes() {
    let before = r#"
        let apply callback value = callback value
        let write value = ()
        let run order = apply (fun value -> write value) order
    "#;
    let after = r#"
        let apply callback value = callback value
        let write value = ()
        let commit value = ()
        let run order = apply (fun value -> write value; commit value) order
    "#;
    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    assert_eq!(report.trees.len(), 1, "{:#?}", report.trees);
    let rendered = render_plain(&report);

    assert!(rendered.contains("λ#1"), "{rendered}");
    assert!(rendered.contains("apply (λ#1) order"), "{rendered}");
    assert!(rendered.contains("write value"), "{rendered}");
    assert!(rendered.contains("commit value"), "{rendered}");
    assert!(!rendered.contains("fun value"), "{rendered}");
    assert!(!rendered.contains("[unresolved]"), "{rendered}");
}

#[test]
fn connected_anonymous_functions_are_not_emitted_as_duplicate_roots() {
    let source = r#"
        let apply callback value = callback value
        let write value = ()
        let run order = apply (fun value -> write value) order
    "#;
    let path = Path::new("anonymous.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let roots = graph.inferred_roots();

    assert_eq!(
        roots
            .iter()
            .map(|root| graph.functions()[root].label.default.as_str())
            .collect::<Vec<_>>(),
        ["run order"]
    );
}

#[test]
fn a_named_fun_binding_does_not_create_a_second_anonymous_root() {
    let source = r#"
        let write value = ()
        let run order =
          let persist = fun value -> write value in
          persist order
    "#;
    let path = Path::new("named-fun.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let roots = graph.inferred_roots();

    assert_eq!(
        roots
            .iter()
            .map(|root| graph.functions()[root].label.default.as_str())
            .collect::<Vec<_>>(),
        ["run order"]
    );
}

#[test]
fn local_mutual_recursion_stays_in_one_connected_tree() {
    let source = r#"
        let run value =
          let rec left item = right item
          and right item = left item
          in
          left value
    "#;
    let path = Path::new("mutual.ml");
    let analysis = OcamlFrontend
        .analyze_file(&FileContext { path, module: &[] }, source)
        .unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let roots = graph.inferred_roots();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(roots, [run].into_iter().collect());
    assert_eq!(tree.children[0].label.default, "left value [closure#0]");
    assert_eq!(
        tree.children[0].children[0].label.default,
        "right item [closure#1]"
    );
    assert_eq!(
        tree.children[0].children[0].children[0].relation,
        CallRelation::BackEdge
    );
}
