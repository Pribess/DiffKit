#![feature(rustc_private)]

use diffkit::{
    ColorMode, DiffOptions, DiffReport, RenderOptions, render_report_with_options, rustdiff_sources,
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
        &DiffOptions {
            entries: vec!["checkout".to_owned()],
            max_depth: 8,
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
        #[derive(Clone, Copy)]
        struct Order;
        pub fn run(order: Order) { save(order); }
        fn save(value: Order) {}
    "#;
    let after = r#"
        #[derive(Clone, Copy)]
        struct Order;
        pub fn run(order: Order) { let next_order = order; save(next_order); }
        fn save(value: Order) {}
    "#;

    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  run(order)\n- └─ save(order)\n+ └─ save(next_order)"
    );
}

#[test]
fn unrelated_rust_file_roots_render_as_removed_and_added_forests() {
    let report = rustdiff_sources(
        "before.rs",
        "fn old(value: u64) { helper(value); } fn helper(_: u64) {}",
        "after.rs",
        "fn replacement(value: u64) { worker(value); } fn worker(_: u64) {}",
        &DiffOptions::default(),
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n- old(value)\n- └─ helper(value)\n\n+ replacement(value)\n+ └─ worker(value)"
    );
}

#[test]
fn keeps_generic_arguments_on_rust_callsite_labels() {
    let before = r#"
        #[derive(Clone, Copy)]
        struct Order;
        struct Postgres;
        pub fn entry(order: Order) { run::<Postgres>(order); }
        fn run<S>(order: Order) { validate(order); }
        fn validate(order: Order) {}
    "#;
    let after = r#"
        #[derive(Clone, Copy)]
        struct Order;
        struct Postgres;
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
        &DiffOptions {
            entries: vec!["entry".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  entry(order)\n  └─ run<Postgres>(order)\n     ├─ validate(order)\n+    └─ finalize(order)"
    );
}

#[test]
fn rust_analysis_uses_concrete_generic_and_trait_targets() {
    let report = rustdiff_sources(
        "before.rs",
        include_str!("../examples/rust/before.rs"),
        "after.rs",
        include_str!("../examples/rust/after.rs"),
        &DiffOptions {
            entries: vec!["run<Postgres>".to_owned(), "run<S3>".to_owned()],
            max_depth: 8,
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
        &DiffOptions {
            entries: vec!["run<Postgres>".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  run<Postgres>(storage, order)\n  └─ Postgres::save(order)\n     ├─ write(order)\n+    └─ commit()"
    );
}

#[test]
fn rust_analysis_renders_reachable_dyn_candidates_as_double_line_relations() {
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
        &DiffOptions {
            entries: vec!["entry".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();

    let rendered = render_plain(&report);
    assert!(rendered.contains("run(&Postgres, order)"), "{rendered}");
    assert!(rendered.contains("Postgres::save(order)"), "{rendered}");
    assert!(rendered.contains("run(&S3, order)"), "{rendered}");
    assert!(rendered.contains("S3::save(order)"), "{rendered}");
    assert!(!rendered.contains("[partial]"), "{rendered}");
    assert!(!rendered.contains("[unresolved]"), "{rendered}");
}

#[test]
fn dyn_root_without_a_concrete_provenance_is_unresolved() {
    let before = r#"
        trait Store { fn save(&self); }
        fn run(storage: &dyn Store) { storage.save(); }
    "#;
    let after = r#"
        trait Store { fn save(&self); }
        fn run(storage: &dyn Store) { storage.save(); finish(); }
        fn finish() {}
    "#;
    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);
    assert!(
        rendered.contains("dyn Store::save() [unresolved]"),
        "{rendered}"
    );
    assert!(!rendered.contains("… unresolved targets"), "{rendered}");
}

#[test]
fn dyn_root_with_local_candidates_is_partial_and_keeps_the_unknown_tail() {
    let before = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        impl Store for Postgres { fn save(&self) { write(); } }
        fn run(storage: &dyn Store, local: bool) {
            let selected: &dyn Store = if local { &Postgres } else { storage };
            selected.save();
        }
        fn write() {}
    "#;
    let after = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        impl Store for Postgres { fn save(&self) { write(); commit(); } }
        fn run(storage: &dyn Store, local: bool) {
            let selected: &dyn Store = if local { &Postgres } else { storage };
            selected.save();
        }
        fn write() {}
        fn commit() {}
    "#;
    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);
    assert!(
        rendered.contains("dyn Store::save() [partial]"),
        "{rendered}"
    );
    assert!(rendered.contains("Postgres::save()"), "{rendered}");
    assert!(rendered.contains("… unresolved targets"), "{rendered}");
}

#[test]
fn unrelated_vtable_construction_does_not_pollute_a_dyn_receiver() {
    let before = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        impl Store for Postgres { fn save(&self) { write(); } }
        fn accept(_: &dyn Store) {}
        fn unrelated() { accept(&Postgres); }
        fn run(storage: &dyn Store) { storage.save(); }
        fn write() {}
    "#;
    let after =
        before.replace("storage.save();", "storage.save(); finish();") + "\nfn finish() {}\n";
    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        &after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);
    assert!(
        rendered.contains("dyn Store::save() [unresolved]"),
        "{rendered}"
    );
    assert!(!rendered.contains("Postgres::save()"), "{rendered}");
}

#[test]
fn dyn_provenance_crosses_direct_arguments_and_return_values() {
    let before = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        impl Store for Postgres { fn save(&self) { write(); } }
        struct S3;
        impl Store for S3 { fn save(&self) { upload(); } }
        fn identity(value: &dyn Store) -> &dyn Store { value }
        fn run(value: &dyn Store) { identity(value).save(); }
        fn write() {}
        fn upload() {}
        fn entry() { run(&Postgres); run(&S3); }
    "#;
    let after = before.replace("fn write() {}", "fn write() { commit(); } fn commit() {}");
    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        &after,
        &DiffOptions {
            entries: vec!["entry".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);
    let postgres = rendered
        .split("run(&Postgres)")
        .nth(1)
        .and_then(|tail| tail.split("run(&S3)").next())
        .unwrap_or_default();
    let s3 = rendered.split("run(&S3)").nth(1).unwrap_or_default();
    assert!(postgres.contains("Postgres::save()"), "{rendered}");
    assert!(!postgres.contains("S3::save()"), "{rendered}");
    assert!(s3.contains("S3::save()"), "{rendered}");
    assert!(!s3.contains("Postgres::save()"), "{rendered}");
}

#[test]
fn renders_closure_instances_without_attributing_their_body_to_the_parent() {
    let before = r#"
        fn run(order: u64) {
            let persist = |value| { write(value); };
            persist(order);
        }
        fn write(_: u64) {}
    "#;
    let after = r#"
        fn run(order: u64) {
            let persist = |value| { write(value); commit(); };
            persist(order);
        }
        fn write(_: u64) {}
        fn commit() {}
    "#;
    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  run(order)\n  └─ persist(order) [closure#0]\n     ├─ write(value)\n+    └─ commit()"
    );
}

#[test]
fn keeps_async_trees_source_logical_instead_of_showing_poll_runtime() {
    let before = r#"
        async fn run(order: u64) { fetch(order).await; }
        async fn fetch(_: u64) {}
    "#;
    let after = r#"
        async fn run(order: u64) { fetch(order).await; finish(order); }
        async fn fetch(_: u64) {}
        fn finish(_: u64) {}
    "#;
    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);
    assert!(rendered.contains("fetch(order)"), "{rendered}");
    assert!(rendered.contains("finish(order)"), "{rendered}");
    assert!(!rendered.contains("poll"), "{rendered}");
    assert!(!rendered.contains("Future"), "{rendered}");
}

#[test]
fn recursive_calls_render_one_ancestor_and_a_direct_back_edge() {
    let before = "fn a() { b(); }\nfn b() { a(); }\n";
    let after = "fn a() { b(); }\nfn b() { finish(); a(); }\nfn finish() {}\n";
    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        after,
        &DiffOptions {
            entries: vec!["a".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);
    assert_eq!(rendered.matches("a()").count(), 1, "{rendered}");
    assert!(rendered.contains('◀'), "{rendered}");
    assert!(rendered.contains('┘'), "{rendered}");
    assert!(rendered.contains("finish()"), "{rendered}");
}
