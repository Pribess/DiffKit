#![feature(rustc_private)]

use diffkit::{
    ColorMode, DiffReport, OcamlDiffOptions, RenderOptions, ocamldiff_sources,
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
        &OcamlDiffOptions {
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
        &OcamlDiffOptions {
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
fn accepts_ocaml_qualified_entry_names() {
    let before = include_str!("../examples/ocaml/before.ml");
    let after = include_str!("../examples/ocaml/after.ml");
    let report = ocamldiff_sources(
        "before.ml",
        before,
        "after.ml",
        after,
        &OcamlDiffOptions {
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
