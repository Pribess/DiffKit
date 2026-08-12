#![feature(rustc_private)]

use diffkit::{
    ColorMode, DiffReport, RenderOptions, RustAnalysisMode, RustDiffOptions,
    render_report_with_options, rustdiff_sources,
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
fn renders_a_basic_rust_call_tree_diff() {
    let before = r#"
        pub fn checkout(total: u64) {
            validate(total);
            charge(total);
            receipt();
        }
        fn validate(_total: u64) {}
        fn charge(_total: u64) {}
        fn receipt() {}
    "#;
    let after = r#"
        pub fn checkout(total: u64) {
            prepare(total);
            charge(total);
        }
        fn prepare(total: u64) {
            validate(total);
            reserve();
        }
        fn validate(_total: u64) {}
        fn reserve() {}
        fn charge(_total: u64) {}
    "#;

    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        after,
        &RustDiffOptions {
            entries: vec!["checkout".to_owned()],
            max_depth: 8,
            ..RustDiffOptions::default()
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  checkout(total)\n- ├─ validate(total)\n+ ├─ prepare(total)\n+ │  ├─ validate(total)\n+ │  └─ reserve()\n  ├─ charge(total)\n- └─ receipt()"
    );
}

#[test]
fn child_labels_use_rust_callsite_arguments_but_diff_by_symbol() {
    let before = r#"
        pub fn run(order: Order) { save(order); }
        fn save(value: Order) {}
    "#;
    let after = r#"
        pub fn run(order: Order) { save(next_order); }
        fn save(value: Order) {}
    "#;

    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        after,
        &RustDiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
            ..RustDiffOptions::default()
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  run(order)\n- └─ save(order)\n+ └─ save(next_order)"
    );
}

#[test]
fn keeps_generic_arguments_on_rust_callsite_labels() {
    let before = r#"
        pub fn entry(order: Order) { run::<Postgres>(order); }
        fn run<S>(order: Order) { validate(order); }
        fn validate(order: Order) {}
    "#;
    let after = r#"
        pub fn entry(order: Order) { run::<Postgres>(order); }
        fn run<S>(order: Order) { validate(order); finalize(order); }
        fn validate(order: Order) {}
        fn finalize(order: Order) {}
    "#;

    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        after,
        &RustDiffOptions {
            entries: vec!["entry".to_owned()],
            max_depth: 8,
            ..RustDiffOptions::default()
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  entry(order)\n  └─ run<Postgres>(order)\n     ├─ validate(order)\n+    └─ finalize(order)"
    );
}

#[test]
fn semantic_mode_uses_concrete_generic_and_trait_targets() {
    let report = rustdiff_sources(
        "before.rs",
        include_str!("../examples/rust/before.rs"),
        "after.rs",
        include_str!("../examples/rust/after.rs"),
        &RustDiffOptions {
            entries: vec!["run<Postgres>".to_owned(), "run<S3>".to_owned()],
            max_depth: 8,
            mode: RustAnalysisMode::Semantic,
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  run<Postgres>(storage, order)\n  ├─ validate(order)\n  ├─ Postgres::save(order)\n+ │  ├─ sql::begin()\n  │  ├─ sql::insert(order)\n+ │  └─ sql::commit()\n  └─ finalize(order)\n\n  run<S3>(storage, order)\n  ├─ validate(order)\n  ├─ S3::save(order)\n  │  ├─ aws::sign(order)\n+ │  └─ aws::put_object(order)\n  └─ finalize(order)"
    );
}

#[test]
fn semantic_entry_instantiates_an_uncalled_generic_function() {
    let before = r#"
        #[derive(Clone, Copy)]
        struct Order;
        trait Store { fn save(&self, order: Order); }
        struct Postgres;
        impl Store for Postgres { fn save(&self, order: Order) { write(order); } }
        fn run<S: Store>(storage: &S, order: Order) { storage.save(order); }
        fn write(_: Order) {}
    "#;
    let after = r#"
        #[derive(Clone, Copy)]
        struct Order;
        trait Store { fn save(&self, order: Order); }
        struct Postgres;
        impl Store for Postgres { fn save(&self, order: Order) { write(order); commit(); } }
        fn run<S: Store>(storage: &S, order: Order) { storage.save(order); }
        fn write(_: Order) {}
        fn commit() {}
    "#;

    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        after,
        &RustDiffOptions {
            entries: vec!["run<Postgres>".to_owned()],
            max_depth: 8,
            mode: RustAnalysisMode::Semantic,
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  run<Postgres>(storage, order)\n  └─ Postgres::save(order)\n     ├─ write(order)\n+    └─ commit()"
    );
}

#[test]
fn semantic_mode_renders_reachable_dyn_candidates_as_double_line_relations() {
    let before = r#"
        #[derive(Clone, Copy)]
        pub struct Order;
        trait Store { fn save(&self, order: Order); }
        struct Postgres;
        impl Store for Postgres {
            fn save(&self, order: Order) { sql::insert(order); }
        }
        struct S3;
        impl Store for S3 {
            fn save(&self, order: Order) { aws::put_object(order); }
        }
        fn run(storage: &dyn Store, order: Order) { storage.save(order); }
        pub fn entry(order: Order) { run(&Postgres, order); }
        mod sql {
            use super::Order;
            pub fn insert(_: Order) {}
        }
        mod aws {
            use super::Order;
            pub fn put_object(_: Order) {}
        }
    "#;
    let after = r#"
        #[derive(Clone, Copy)]
        pub struct Order;
        trait Store { fn save(&self, order: Order); }
        struct Postgres;
        impl Store for Postgres {
            fn save(&self, order: Order) { sql::insert(order); }
        }
        struct S3;
        impl Store for S3 {
            fn save(&self, order: Order) { aws::put_object(order); }
        }
        fn run(storage: &dyn Store, order: Order) { storage.save(order); }
        pub fn entry(order: Order) {
            run(&Postgres, order);
            run(&S3, order);
        }
        mod sql {
            use super::Order;
            pub fn insert(_: Order) {}
        }
        mod aws {
            use super::Order;
            pub fn put_object(_: Order) {}
        }
    "#;

    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        after,
        &RustDiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
            mode: RustAnalysisMode::Semantic,
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  run(storage, order)\n  └─ dyn Store::save(order)\n     ╠═ Postgres::save(order)\n     ║  └─ sql::insert(order)\n+    ╚═ S3::save(order)\n+       └─ aws::put_object(order)"
    );
}
