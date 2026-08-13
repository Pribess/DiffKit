#![feature(rustc_private)]

use diffkit::{
    ColorMode, DiffOptions, DiffReport, RenderOptions, ocamldiff_sources,
    render_report_with_options,
};

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
