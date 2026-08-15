#![feature(rustc_private)]

use diffkit::graph::ProgramGraph;
use diffkit::model::{CallNode, CallRelation};
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

fn contains_back_edge(node: &CallNode) -> bool {
    node.relation == CallRelation::BackEdge || node.children.iter().any(contains_back_edge)
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
fn bare_entry_resolves_every_closure_monomorphization_of_one_generic_method() {
    let before = r#"
        struct Walker;
        impl Walker {
            fn run<F: FnOnce()>(self, visit: F) { visit(); }
        }
        fn left() {}
        fn right() {}
        pub fn entry() {
            Walker.run(|| left());
            Walker.run(|| right());
        }
    "#;
    let after = before.replace("fn left() {}", "fn left() { changed(); } fn changed() {}");

    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        &after,
        &DiffOptions {
            // Real crates such as ripgrep expose one rustc instance per
            // closure type. A source-level entry selects all of them.
            entries: vec!["Walker::run".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();

    let rendered = render_plain(&report);
    assert!(rendered.contains("Walker::run<λ#"), "{rendered}");
    assert!(rendered.contains("left()"), "{rendered}");
    assert!(rendered.contains("changed()"), "{rendered}");
    assert!(!rendered.contains("right()"), "{rendered}");
}

#[test]
fn generic_impl_entry_can_omit_container_and_method_arguments() {
    let before = r#"
        trait Access { fn visit<V>(&self, value: V); }
        struct Variant<T>(T);
        impl<T> Access for Variant<T> {
            fn visit<V>(&self, _value: V) { work(); }
        }
        fn work() {}
        pub fn entry() { Variant(1_u8).visit(2_u16); }
    "#;
    let after = before.replace("fn work() {}", "fn work() { finish(); } fn finish() {}");

    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        &after,
        &DiffOptions {
            entries: vec!["Variant::visit".to_owned()],
            max_depth: 8,
        },
    )
    .unwrap();

    let rendered = render_plain(&report);
    assert!(rendered.contains("Variant<u8>::visit<u16>"), "{rendered}");
    assert!(rendered.contains("finish()"), "{rendered}");
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
    assert!(
        report
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("evidence=exact-flow")
                && diagnostic.contains("opaque input")),
        "{:?}",
        report.diagnostics
    );
}

#[test]
fn expands_candidates_only_on_the_last_equivalent_dynamic_call() {
    let before = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        impl Store for Postgres { fn save(&self) { write(); } }
        fn run(storage: &dyn Store) {
            storage.save();
            storage.save();
            storage.save();
        }
        fn entry() { run(&Postgres); }
        fn write() {}
    "#;
    let after = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        impl Store for Postgres { fn save(&self) { write(); commit(); } }
        fn run(storage: &dyn Store) {
            storage.save();
            storage.save();
            storage.save();
        }
        fn entry() { run(&Postgres); }
        fn write() {}
        fn commit() {}
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

    assert_eq!(
        rendered.matches("dyn Store::save()").count(),
        3,
        "{rendered}"
    );
    assert_eq!(
        rendered.matches("Postgres::save()").count(),
        1,
        "{rendered}"
    );
    assert_eq!(rendered.matches("commit()").count(), 1, "{rendered}");
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
        "rustdiff before.rs → after.rs\n\n  run(order)\n  └─ λpersist(order)\n     ├─ write(value)\n+    └─ commit()"
    );
}

#[test]
fn renders_generic_closure_instances_as_lambda_trees() {
    let before = r#"
        fn apply<F: Fn()>(f: F) { f(); }
        pub fn run() {
            apply(|| db::save());
            apply(|| cache::save());
        }
        mod db { pub fn save() { write(); } fn write() {} }
        mod cache { pub fn save() { store(); } fn store() {} }
    "#;
    let after = before
        .replace(
            "pub fn save() { write(); }",
            "pub fn save() { write(); audit(); } fn audit() {}",
        )
        .replace(
            "pub fn save() { store(); }",
            "pub fn save() { store(); flush(); } fn flush() {}",
        );
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

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  run()\n  ├─ apply<λ#1>()\n  │  └─ λ#1()\n  │     └─ db::save()\n  │        ├─ write()\n+ │        └─ audit()\n  └─ apply<λ#2>()\n     └─ λ#2()\n        └─ cache::save()\n           ├─ store()\n+          └─ flush()"
    );
}

#[test]
fn closure_instances_inherit_their_parent_generic_arguments() {
    let before = r#"
        trait Storage { fn save(&self); }
        struct Postgres;
        impl Storage for Postgres { fn save(&self) { sql(); } }
        struct S3;
        impl Storage for S3 { fn save(&self) { upload(); } }
        fn process<S: Storage>(storage: S) {
            let save = || storage.save();
            save();
        }
        pub fn entry() { process(Postgres); process(S3); }
        fn sql() {}
        fn upload() {}
    "#;
    let after = before
        .replace("fn sql() {}", "fn sql() { commit(); } fn commit() {}")
        .replace("fn upload() {}", "fn upload() { flush(); } fn flush() {}");
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

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  entry()\n  ├─ process<Postgres>(Postgres)\n  │  └─ λsave<Postgres>()\n  │     └─ Postgres::save()\n  │        └─ sql()\n+ │           └─ commit()\n  └─ process<S3>(S3)\n     └─ λsave<S3>()\n        └─ S3::save()\n           └─ upload()\n+             └─ flush()"
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
fn renders_async_closures_with_the_same_lambda_shape() {
    let before = r#"
        pub async fn run() {
            let task = async || { worker().await; };
            task().await;
        }
        async fn worker() {}
    "#;
    let after = r#"
        pub async fn run() {
            let task = async || { worker().await; finish(); };
            task().await;
        }
        async fn worker() {}
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

    assert_eq!(
        render_plain(&report),
        "rustdiff before.rs → after.rs\n\n  run()\n  └─ λtask()\n     ├─ worker()\n+    └─ finish()"
    );
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
    assert_eq!(rendered.matches("a()").count(), 2, "{rendered}");
    assert!(rendered.contains('◀'), "{rendered}");
    assert!(rendered.contains('┘'), "{rendered}");
    assert!(rendered.contains("finish()"), "{rendered}");
}

#[test]
fn expands_only_the_last_repeated_rust_call_to_the_same_function() {
    let before = r#"
        fn leaf(value: i32) {}
        fn helper(value: i32) { leaf(value); }
        pub fn run() { helper(1); helper(2); helper(3); }
    "#;
    let after = r#"
        fn leaf(value: i32) {}
        fn finish(value: i32) {}
        fn helper(value: i32) { leaf(value); finish(value); }
        pub fn run() { helper(1); helper(2); helper(3); }
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
        "rustdiff before.rs → after.rs\n\n  run()\n  ├─ helper(1)\n  ├─ helper(2)\n  └─ helper(3)\n     ├─ leaf(value)\n+    └─ finish(value)"
    );
}

#[test]
fn moving_the_last_expansion_to_a_new_call_does_not_remove_unchanged_children() {
    let before = r#"
        fn leaf(value: i32) {}
        fn helper(value: i32) { leaf(value); }
        pub fn run() { helper(1); helper(2); }
    "#;
    let after = r#"
        fn leaf(value: i32) {}
        fn helper(value: i32) { leaf(value); }
        pub fn run() { helper(1); helper(2); helper(3); }
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
        "rustdiff before.rs → after.rs\n\n  run()\n  ├─ helper(1)\n  ├─ helper(2)\n+ └─ helper(3)"
    );
}

#[test]
fn expands_the_last_call_of_each_concrete_generic_instance() {
    let before = r#"
        fn leaf<T>() {}
        fn helper<T>() { leaf::<T>(); }
        pub fn run() { helper::<u32>(); helper::<String>(); helper::<u32>(); }
    "#;
    let after = r#"
        fn leaf<T>() {}
        fn finish<T>() {}
        fn helper<T>() { leaf::<T>(); finish::<T>(); }
        pub fn run() { helper::<u32>(); helper::<String>(); helper::<u32>(); }
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

    assert_eq!(rendered.matches("helper<u32>()").count(), 2, "{rendered}");
    assert_eq!(
        rendered.matches("helper<String>()").count(),
        1,
        "{rendered}"
    );
    assert_eq!(rendered.matches("finish<").count(), 2, "{rendered}");
}

#[test]
fn keeps_an_uninstantiated_generic_definition_as_an_open_call_tree() {
    let before = r#"
        trait Store { fn save(&self); }
        pub fn run<T: Store>(storage: T) { storage.save(); }
    "#;
    let after = r#"
        trait Store { fn save(&self); }
        pub fn run<T: Store>(storage: T) { validate(); storage.save(); }
        fn validate() {}
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
        "rustdiff before.rs → after.rs\n\n  run<T: Store>(storage)\n+ ├─ validate()\n  └─ T::save()"
    );
}

#[test]
fn distinguishes_a_function_pointer_call_from_an_unresolved_name() {
    let before = "pub fn run(callback: fn()) { callback(); }";
    let after = "pub fn run(callback: fn()) { callback(); finish(); } fn finish() {}";
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
    assert!(rendered.contains("callback() [indirect]"), "{rendered}");
    assert!(rendered.contains("finish()"), "{rendered}");
    assert!(report.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("indirect") && diagnostic.contains("function pointer")
    }));
}

#[test]
fn dyn_provenance_survives_a_standard_library_container() {
    let before = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        impl Store for Postgres { fn save(&self) { write(); } }
        fn write() {}
        fn stores() -> Vec<Box<dyn Store>> {
            let mut values: Vec<Box<dyn Store>> = Vec::new();
            values.push(Box::new(Postgres));
            values
        }
        pub fn run() { let values = stores(); values[0].save(); }
    "#;
    let after = before.replace("fn write() {}", "fn write() { commit(); } fn commit() {}");
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
    assert!(rendered.contains("Postgres::save()"), "{rendered}");
    assert!(
        !rendered.contains("dyn Store::save() [unresolved]"),
        "{rendered}"
    );
    assert!(!rendered.contains("[partial]"), "{rendered}");
    assert!(!rendered.contains("… unresolved targets"), "{rendered}");
    assert!(rendered.contains("commit()"), "{rendered}");
}

#[test]
fn max_depth_is_applied_after_a_deep_change_is_detected() {
    let before = "pub fn root() { a(); } fn a() { b(); } fn b() { leaf(); } fn leaf() {}";
    let after = "pub fn root() { a(); } fn a() { b(); } fn b() { leaf(); changed(); } fn leaf() {} fn changed() {}";
    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        after,
        &DiffOptions {
            entries: vec!["root".to_owned()],
            max_depth: 1,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);
    assert!(!rendered.contains("No rust call changes"), "{rendered}");
    assert!(rendered.contains("… changed below max depth"), "{rendered}");
}

#[test]
fn inserting_an_unrelated_closure_does_not_renumber_existing_closure_identity() {
    let before = r#"
        fn apply<F: Fn()>(f: F) { f(); }
        fn old() {}
        pub fn run() { apply(|| old()); }
    "#;
    let after = r#"
        fn apply<F: Fn()>(f: F) { f(); }
        fn apply_one<F: Fn(u8)>(f: F) { f(1); }
        fn inserted() {}
        fn old() {}
        pub fn run() {
            apply_one(|_| inserted());
            apply(|| old());
        }
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
    assert!(rendered.contains("  └─ apply<λ#2>()"), "{rendered}");
    assert!(
        !rendered.lines().any(|line| {
            (line.starts_with("- ") || line.starts_with("+ ")) && line.contains("apply<λ#2>()")
        }),
        "{rendered}"
    );
    assert!(
        !rendered
            .lines()
            .any(|line| line.starts_with("- ") && line.contains("old()")),
        "{rendered}"
    );

    let analysis = diffkit::language::rust::analyze_semantic_source(after, &[]).unwrap();
    assert!(
        analysis
            .functions
            .iter()
            .all(|function| !function.id.name.contains("{closure#"))
    );
}

#[test]
fn inserting_a_same_signature_closure_does_not_churn_existing_closures() {
    let before = r#"
        fn apply<F: Fn()>(callback: F) { callback(); }
        fn first() {}
        fn second() {}
        pub fn run() {
            apply(|| first());
            apply(|| second());
        }
    "#;
    let after = r#"
        fn apply<F: Fn()>(callback: F) { callback(); }
        fn inserted() {}
        fn first() {}
        fn second() {}
        pub fn run() {
            apply(|| inserted());
            apply(|| first());
            apply(|| second());
        }
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

    for stable in ["first()", "second()"] {
        assert!(
            !rendered
                .lines()
                .any(|line| line.starts_with("- ") && line.contains(stable)),
            "{rendered}"
        );
    }
    assert!(rendered.contains("inserted()"), "{rendered}");
}

#[test]
fn deeply_nested_closure_types_finish_without_inventing_recursion() {
    let source = r#"
        fn duplicate(f: impl Fn(i32) -> i32) -> impl Fn(i32) -> i32 {
            move |value| f(value * 2)
        }

        pub fn run() {
            let callback = |value| value;
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let callback = duplicate(callback);
            let _ = callback(1);
        }
    "#;

    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 64).unwrap();

    assert_eq!(graph.inferred_roots(), [run].into_iter().collect());
    assert!(!contains_back_edge(&tree), "{tree:#?}");
}

#[test]
fn dyn_provenance_crosses_a_mutating_helper_without_becoming_partial() {
    let before = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        impl Store for Postgres { fn save(&self) { write(); } }
        fn write() {}
        fn install(slot: &mut Option<Box<dyn Store>>, value: Box<dyn Store>) {
            *slot = Some(value);
        }
        pub fn run() {
            let mut slot: Option<Box<dyn Store>> = None;
            install(&mut slot, Box::new(Postgres));
            slot.unwrap().save();
        }
    "#;
    let after = before.replace("fn write() {}", "fn write() { commit(); } fn commit() {}");
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

    assert!(rendered.contains("install(&mut slot,"), "{rendered}");
    assert!(rendered.contains("Postgres::save()"), "{rendered}");
    assert!(rendered.contains("commit()"), "{rendered}");
    assert!(!rendered.contains("[partial]"), "{rendered}");
    assert!(!rendered.contains("[unresolved]"), "{rendered}");
}

#[test]
fn a_returned_mutable_reference_updates_the_original_dyn_place() {
    let source = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        struct S3;
        impl Store for Postgres { fn save(&self) { postgres_leaf(); } }
        impl Store for S3 { fn save(&self) { s3_leaf(); } }
        fn postgres_leaf() {}
        fn s3_leaf() {}
        fn expose(value: &mut Box<dyn Store>) -> &mut Box<dyn Store> { value }
        pub fn run() {
            let mut store: Box<dyn Store> = Box::new(Postgres);
            *expose(&mut store) = Box::new(S3);
            store.save();
        }
        struct Pair {
            left: Box<dyn Store>,
            right: Box<dyn Store>,
        }
        fn expose_left(pair: &mut Pair) -> &mut Box<dyn Store> { &mut pair.left }
        pub fn update_left() {
            let mut pair = Pair {
                left: Box::new(Postgres),
                right: Box::new(Postgres),
            };
            *expose_left(&mut pair) = Box::new(S3);
            pair.left.save();
        }
        pub fn preserve_right() {
            let mut pair = Pair {
                left: Box::new(Postgres),
                right: Box::new(Postgres),
            };
            *expose_left(&mut pair) = Box::new(S3);
            pair.right.save();
        }
    "#;
    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let dispatch = tree
        .children
        .iter()
        .find(|call| call.label.default == "dyn Store::save()")
        .unwrap();

    assert_eq!(
        dispatch
            .children
            .iter()
            .map(|candidate| candidate.label.default.as_str())
            .collect::<Vec<_>>(),
        ["S3::save()"]
    );

    for (entry, expected) in [
        ("update_left", "S3::save()"),
        ("preserve_right", "Postgres::save()"),
    ] {
        let root = graph.resolve_entry(entry).unwrap().unwrap();
        let tree = graph.build_call_tree(&root, 8).unwrap();
        let dispatch = tree
            .children
            .iter()
            .find(|call| call.label.default == "dyn Store::save()")
            .unwrap();
        assert_eq!(dispatch.children[0].label.default, expected);
    }
}

#[test]
fn writes_through_an_opaque_external_guard_do_not_keep_a_stale_exact_candidate() {
    let source = r#"
        use std::cell::RefCell;
        trait Store { fn save(&self); }
        struct Postgres;
        struct S3;
        impl Store for Postgres { fn save(&self) {} }
        impl Store for S3 { fn save(&self) {} }
        pub fn run() {
            let store: RefCell<Box<dyn Store>> = RefCell::new(Box::new(Postgres));
            *store.borrow_mut() = Box::new(S3);
            store.borrow().save();
        }
        pub fn read_only() {
            let store: RefCell<Box<dyn Store>> = RefCell::new(Box::new(Postgres));
            store.borrow().save();
        }
    "#;
    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let dispatch = tree
        .children
        .iter()
        .find(|call| call.label.default.starts_with("dyn Store::save()"))
        .unwrap();

    assert_eq!(dispatch.label.default, "dyn Store::save() [unresolved]");
    assert!(dispatch.children.is_empty(), "{dispatch:#?}");

    let read_only = graph.resolve_entry("read_only").unwrap().unwrap();
    let read_only_tree = graph.build_call_tree(&read_only, 8).unwrap();
    let read_dispatch = read_only_tree
        .children
        .iter()
        .find(|call| call.label.default == "dyn Store::save()")
        .unwrap();
    assert_eq!(read_dispatch.children[0].label.default, "Postgres::save()");
}

#[test]
fn exact_dyn_provenance_survives_option_reference_adapters() {
    let before = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        impl Store for Postgres { fn save(&self) { write(); } }
        fn write() {}
        fn install(slot: &mut Option<Box<dyn Store>>) {
            *slot = Some(Box::new(Postgres));
        }
        pub fn run() {
            let mut slot: Option<Box<dyn Store>> = None;
            install(&mut slot);
            slot.as_ref().unwrap().save();
        }
    "#;
    let after = before.replace("fn write() {}", "fn write() { commit(); } fn commit() {}");
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

    assert!(rendered.contains("Postgres::save()"), "{rendered}");
    assert!(rendered.contains("commit()"), "{rendered}");
    assert!(!rendered.contains("[partial]"), "{rendered}");
}

#[test]
fn a_non_storing_helper_does_not_invent_a_dyn_candidate() {
    let before = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        struct S3;
        impl Store for Postgres { fn save(&self) { postgres(); } }
        impl Store for S3 { fn save(&self) { s3(); } }
        fn postgres() {}
        fn s3() {}
        fn inspect(_: &mut Option<Box<dyn Store>>, _: Box<dyn Store>) {}
        pub fn run() {
            let mut slot: Option<Box<dyn Store>> = Some(Box::new(Postgres));
            inspect(&mut slot, Box::new(S3));
            slot.unwrap().save();
        }
    "#;
    let after = before.replace(
        "fn postgres() {}",
        "fn postgres() { commit(); } fn commit() {}",
    );
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

    assert!(rendered.contains("Postgres::save()"), "{rendered}");
    assert!(!rendered.contains("S3::save()"), "{rendered}");
    assert!(!rendered.contains("[partial]"), "{rendered}");
}

#[test]
fn local_array_dynamic_index_has_the_exact_closed_candidate_set() {
    let before = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        struct S3;
        impl Store for Postgres { fn save(&self) { postgres(); } }
        impl Store for S3 { fn save(&self) { s3(); } }
        fn postgres() {}
        fn s3() {}
        pub fn run(index: usize) {
            let stores: [Box<dyn Store>; 2] = [Box::new(Postgres), Box::new(S3)];
            stores[index].save();
        }
    "#;
    let after = before.replace("fn s3() {}", "fn s3() { upload(); } fn upload() {}");
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

    assert!(rendered.contains("Postgres::save()"), "{rendered}");
    assert!(rendered.contains("S3::save()"), "{rendered}");
    assert!(rendered.contains("upload()"), "{rendered}");
    assert!(!rendered.contains("[partial]"), "{rendered}");
}

#[test]
fn enum_control_flow_has_the_exact_closed_candidate_set() {
    let before = r#"
        trait Store { fn save(&self); }
        struct Postgres;
        struct S3;
        impl Store for Postgres { fn save(&self) { postgres(); } }
        impl Store for S3 { fn save(&self) { s3(); } }
        enum Choice { Postgres(Box<dyn Store>), S3(Box<dyn Store>) }
        fn postgres() {}
        fn s3() {}
        pub fn run(use_s3: bool) {
            let choice = if use_s3 {
                Choice::S3(Box::new(S3))
            } else {
                Choice::Postgres(Box::new(Postgres))
            };
            let store = match choice {
                Choice::Postgres(store) | Choice::S3(store) => store,
            };
            store.save();
        }
    "#;
    let after = before.replace("fn s3() {}", "fn s3() { upload(); } fn upload() {}");
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

    assert!(rendered.contains("Postgres::save()"), "{rendered}");
    assert!(rendered.contains("S3::save()"), "{rendered}");
    assert!(rendered.contains("upload()"), "{rendered}");
    assert!(!rendered.contains("[partial]"), "{rendered}");
}

#[test]
fn enum_match_arms_keep_variant_specific_dynamic_provenance() {
    let source = r#"
        trait Work { fn work(&self); }
        struct A;
        struct B;
        impl Work for A { fn work(&self) { a(); } }
        impl Work for B { fn work(&self) { b(); } }
        fn a() {}
        fn b() {}
        enum Choice { A(Box<dyn Work>), B(Box<dyn Work>) }
        fn inspect_a(value: &dyn Work) { value.work(); }
        fn inspect_b(value: &dyn Work) { value.work(); }
        pub fn run(use_b: bool) {
            let choice = if use_b {
                Choice::B(Box::new(B))
            } else {
                Choice::A(Box::new(A))
            };
            match choice {
                Choice::A(value) => inspect_a(&*value),
                Choice::B(value) => inspect_b(&*value),
            }
        }
    "#;
    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = diffkit::render_call_tree_with_options(
        &tree,
        &RenderOptions {
            show_types: false,
            color: ColorMode::Plain,
        },
    );

    let inspect_a = tree
        .children
        .iter()
        .find(|child| child.label.default == "inspect_a(&*value)")
        .unwrap();
    let inspect_b = tree
        .children
        .iter()
        .find(|child| child.label.default == "inspect_b(&*value)")
        .unwrap();
    assert_eq!(
        inspect_a.children[0].children[0].label.default, "A::work()",
        "{rendered}"
    );
    assert_eq!(inspect_a.children[0].children.len(), 1);
    assert_eq!(
        inspect_b.children[0].children[0].label.default, "B::work()",
        "{rendered}"
    );
    assert_eq!(inspect_b.children[0].children.len(), 1);
}

#[test]
fn writes_through_branch_merged_mutable_aliases_keep_each_paths_candidates() {
    let source = r#"
        trait Work { fn work(&self); }
        struct A;
        struct B;
        struct C;
        impl Work for A { fn work(&self) { a(); } }
        impl Work for B { fn work(&self) { b(); } }
        impl Work for C { fn work(&self) { c(); } }
        fn a() {}
        fn b() {}
        fn c() {}
        fn inspect_left(value: &dyn Work) { value.work(); }
        fn inspect_right(value: &dyn Work) { value.work(); }
        pub fn run(use_left: bool) {
            let mut left: &dyn Work = &A;
            let mut right: &dyn Work = &B;
            let slot = if use_left { &mut left } else { &mut right };
            *slot = &C;
            inspect_left(left);
            inspect_right(right);
        }
    "#;
    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = diffkit::render_call_tree_with_options(
        &tree,
        &RenderOptions {
            show_types: false,
            color: ColorMode::Plain,
        },
    );

    let left = &tree.children[0].children[0];
    let right = &tree.children[1].children[0];
    assert_eq!(
        left.children
            .iter()
            .map(|candidate| candidate.label.default.as_str())
            .collect::<Vec<_>>(),
        ["A::work()", "C::work()"],
        "{rendered}"
    );
    assert_eq!(
        right
            .children
            .iter()
            .map(|candidate| candidate.label.default.as_str())
            .collect::<Vec<_>>(),
        ["B::work()", "C::work()"],
        "{rendered}"
    );
}

#[test]
fn writes_through_a_runtime_array_index_weakly_update_every_possible_element() {
    let source = r#"
        trait Work { fn work(&self); }
        struct A;
        struct B;
        struct C;
        impl Work for A { fn work(&self) { a(); } }
        impl Work for B { fn work(&self) { b(); } }
        impl Work for C { fn work(&self) { c(); } }
        fn a() {}
        fn b() {}
        fn c() {}
        fn inspect_first(value: &dyn Work) { value.work(); }
        fn inspect_second(value: &dyn Work) { value.work(); }
        pub fn run(index: usize) {
            let mut values: [&dyn Work; 2] = [&A, &B];
            values[index] = &C;
            let [first, second] = values;
            inspect_first(first);
            inspect_second(second);
        }
    "#;
    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = diffkit::render_call_tree_with_options(
        &tree,
        &RenderOptions {
            show_types: false,
            color: ColorMode::Plain,
        },
    );

    assert_eq!(
        tree.children[0].children[0]
            .children
            .iter()
            .map(|candidate| candidate.label.default.as_str())
            .collect::<Vec<_>>(),
        ["A::work()", "C::work()"],
        "{rendered}"
    );
    assert_eq!(
        tree.children[1].children[0]
            .children
            .iter()
            .map(|candidate| candidate.label.default.as_str())
            .collect::<Vec<_>>(),
        ["B::work()", "C::work()"],
        "{rendered}"
    );
}

#[test]
fn compile_time_array_indices_do_not_merge_unrelated_elements() {
    let source = r#"
        trait Work { fn work(&self); }
        struct A;
        struct B;
        impl Work for A { fn work(&self) { a(); } }
        impl Work for B { fn work(&self) { b(); } }
        fn a() {}
        fn b() {}
        fn inspect_first(value: &dyn Work) { value.work(); }
        fn inspect_second(value: &dyn Work) { value.work(); }
        pub fn run() {
            let values: [&dyn Work; 2] = [&A, &B];
            inspect_first(values[0]);
            inspect_second(values[1]);
        }
    "#;
    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "A::work()"
    );
    assert_eq!(tree.children[0].children[0].children.len(), 1);
    assert_eq!(
        tree.children[1].children[0].children[0].label.default,
        "B::work()"
    );
    assert_eq!(tree.children[1].children[0].children.len(), 1);
}

#[test]
fn async_closure_through_fn_mut_does_not_panic_or_leak_compiler_types() {
    let source = r#"
        fn needs_fn_mut<T>(mut callback: impl FnMut() -> T) { callback(); }
        fn hello(value: &Worker) {
            needs_fn_mut(async || { value.work(); });
        }
        struct Worker;
        impl Worker { fn work(&self) {} }
        pub fn run() { hello(&Worker); }
    "#;
    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let call_labels = analysis
        .functions
        .iter()
        .flat_map(|function| &function.calls)
        .map(|call| call.label.default.as_str())
        .collect::<Vec<_>>();

    assert!(
        call_labels
            .iter()
            .any(|label| label.contains("needs_fn_mut<λ#1>()")),
        "{call_labels:#?}"
    );
    assert!(
        call_labels
            .iter()
            .all(|label| !label.contains("async closure body@")),
        "{call_labels:#?}"
    );
}

#[test]
fn method_called_inside_an_async_closure_keeps_its_impl_body_connected() {
    let before = r#"
        struct Ty;
        impl Ty { fn hello(&self) { leaf(); } }
        fn leaf() {}
        fn needs_fn_mut<T>(mut callback: impl FnMut() -> T) { callback(); }
        fn hello(value: &Ty) { needs_fn_mut(async || { value.hello(); }); }
        pub fn run() { hello(&Ty); }
    "#;
    let after = before.replace("fn leaf() {}", "fn leaf() { changed(); } fn changed() {}");
    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        &after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 12,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);

    assert!(rendered.contains("Ty::hello()"), "{rendered}");
    assert!(rendered.contains("leaf()"), "{rendered}");
    assert!(rendered.contains("changed()"), "{rendered}");
}

#[test]
fn async_closure_dyn_dispatch_keeps_the_captured_concrete_value() {
    let before = r#"
        trait Work { fn work(&self); }
        struct Local;
        struct Unrelated;
        impl Work for Local { fn work(&self) { local(); } }
        impl Work for Unrelated { fn work(&self) { unrelated(); } }
        fn local() {}
        fn unrelated() {}
        pub async fn run() {
            let worker: Box<dyn Work> = Box::new(Local);
            let task = async move || { worker.work(); };
            task().await;
        }
    "#;
    let after = before.replace("fn local() {}", "fn local() { changed(); } fn changed() {}");
    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        &after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 12,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);

    assert!(rendered.contains("Local::work()"), "{rendered}");
    assert!(rendered.contains("changed()"), "{rendered}");
    assert!(!rendered.contains("Unrelated::work()"), "{rendered}");
    assert!(!rendered.contains("[partial]"), "{rendered}");
    assert!(!rendered.contains("[unresolved]"), "{rendered}");
}

#[test]
fn macro_generated_closures_are_not_misattributed_as_duplicate_roots() {
    let source = r#"
        pub fn main() {
            assert_eq!((|| || work())()(), ());
        }
        fn work() {}
    "#;
    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let main_count = analysis
        .functions
        .iter()
        .filter(|function| function.label.default == "main()")
        .count();

    assert_eq!(main_count, 1, "{:#?}", analysis.functions);
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let main = graph.resolve_entry("main").unwrap().unwrap();
    let tree = graph.build_call_tree(&main, 8).unwrap();
    assert_eq!(tree.children[0].label.default, "λ#1()");
    assert_eq!(tree.children[1].label.default, "λ#2()");
    assert_eq!(tree.children[1].children[0].label.default, "work()");
}

#[test]
fn calls_written_in_evaluated_macro_arguments_remain_in_the_tree() {
    let source = r#"
        trait Value { fn get(&self) -> i32; }
        struct Concrete;
        impl Value for Concrete { fn get(&self) -> i32 { leaf(); 1 } }
        fn leaf() {}
        pub fn run() {
            let value: &dyn Value = &Concrete;
            assert_eq!(value.get(), 1);
        }
    "#;
    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();

    assert_eq!(tree.children[0].label.default, "dyn Value::get()");
    assert_eq!(
        tree.children[0].children[0].label.default,
        "Concrete::get()"
    );
    assert_eq!(
        tree.children[0].children[0].children[0].label.default,
        "leaf()"
    );
}

#[test]
fn recursively_expanding_generic_instantiations_return_an_error_instead_of_hanging() {
    let source = r#"
        fn recur<T>(value: T) {
            recur(Some(value));
        }
        fn main() {
            recur(());
        }
    "#;

    let error = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("recursively expanding generic instantiation"),
        "{error}"
    );
}

#[test]
fn trait_upcasting_uses_the_dispatch_traits_own_vtable_layout() {
    let source = r#"
        trait Base { fn base(&self) {} }
        trait Left: Base { fn left(&self) {} }
        trait Right: Base {
            fn concrete(&self);
            fn defaulted(&self) { default_work(); }
        }
        trait Diamond: Left + Right {}
        impl Base for i32 {}
        impl Left for i32 {}
        impl Right for i32 { fn concrete(&self) { concrete_work(); } }
        impl Diamond for i32 {}
        fn concrete_work() {}
        fn default_work() {}
        pub fn run() {
            let diamond: &dyn Diamond = &1;
            let right: &dyn Right = diamond;
            right.concrete();
            right.defaulted();
        }
    "#;
    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = diffkit::render_call_tree_with_options(
        &tree,
        &RenderOptions {
            show_types: false,
            color: ColorMode::Plain,
        },
    );

    assert!(rendered.contains("i32::concrete()"), "{rendered}");
    assert!(rendered.contains("concrete_work()"), "{rendered}");
    assert!(rendered.contains("i32::defaulted()"), "{rendered}");
    assert!(rendered.contains("default_work()"), "{rendered}");
    assert!(!rendered.contains("[unresolved]"), "{rendered}");
}

#[test]
fn unrelated_observed_vtables_do_not_trigger_supertrait_instance_queries() {
    let source = r#"
        trait Mirror { type Other; }
        #[derive(Debug)]
        struct Even(usize);
        struct Odd;
        impl Mirror for Even { type Other = Odd; }
        impl Mirror for Odd { type Other = Even; }
        trait Dyn<T: Mirror>: AsRef<<T as Mirror>::Other> {}
        impl Dyn<Odd> for Even {}
        impl AsRef<Even> for Even {
            fn as_ref(&self) -> &Even { leaf(); self }
        }
        fn leaf() {}
        fn code<T: Mirror>(value: &dyn Dyn<T>) -> &T::Other { value.as_ref() }
        pub fn run() { let _ = format!("{:?}", code(&Even(22))); }
    "#;
    let after = source.replace("fn leaf() {}", "fn leaf() { changed(); } fn changed() {}");
    let report = rustdiff_sources(
        "before.rs",
        source,
        "after.rs",
        &after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 12,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);

    assert!(rendered.contains("Even::as_ref()"), "{rendered}");
    assert!(rendered.contains("changed()"), "{rendered}");
}

#[test]
fn generic_supertrait_default_method_calls_use_the_concrete_impl() {
    let before = r#"
        #[derive(Clone, Copy)] struct Value;
        trait Parent { fn parent(self); }
        trait Child: Parent + Sized { fn child(self) { invoke_parent(self); } }
        fn invoke_parent<T: Parent>(value: T) { value.parent(); }
        impl Parent for Value { fn parent(self) { leaf(); } }
        impl Child for Value {}
        fn leaf() {}
        pub fn run() { Value.child(); }
    "#;
    let after = before.replace("fn leaf() {}", "fn leaf() { changed(); } fn changed() {}");
    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        &after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 12,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);

    assert!(rendered.contains("Value::parent()"), "{rendered}");
    assert!(rendered.contains("changed()"), "{rendered}");
    assert!(!rendered.contains("T::parent()"), "{rendered}");
}

#[test]
fn primitive_generic_method_calls_render_the_concrete_receiver() {
    let before = r#"
        trait Parent { fn parent(self); }
        fn invoke<T: Parent>(value: T) { value.parent(); }
        impl Parent for isize { fn parent(self) { leaf(); } }
        fn leaf() {}
        pub fn run() { invoke(12isize); }
    "#;
    let after = before.replace("fn leaf() {}", "fn leaf() { changed(); } fn changed() {}");
    let report = rustdiff_sources(
        "before.rs",
        before,
        "after.rs",
        &after,
        &DiffOptions {
            entries: vec!["run".to_owned()],
            max_depth: 12,
        },
    )
    .unwrap();
    let rendered = render_plain(&report);

    assert!(rendered.contains("isize::parent()"), "{rendered}");
    assert!(rendered.contains("changed()"), "{rendered}");
    assert!(!rendered.contains("T::parent()"), "{rendered}");
}

#[test]
fn non_evaluating_macro_tokens_do_not_create_false_calls() {
    let source = r#"
        fn hidden() {}
        pub fn run() { let _ = stringify!(hidden()); }
    "#;
    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let run = analysis
        .functions
        .iter()
        .find(|function| function.label.default == "run()")
        .unwrap();

    assert!(run.calls.is_empty(), "{:#?}", run.calls);
}

#[test]
fn returned_closure_invocation_is_an_explicit_call_node() {
    let before = r#"
        fn make_callback() -> impl Fn() { || work() }
        fn work() {}
        pub fn run() { make_callback()(); }
    "#;
    let after = before.replace("fn work() {}", "fn work() { finish(); } fn finish() {}");
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

    assert!(rendered.contains("make_callback()"), "{rendered}");
    assert!(rendered.contains("λ#1()"), "{rendered}");
    assert!(rendered.contains("finish()"), "{rendered}");
}

#[test]
fn closure_erased_behind_dyn_fn_keeps_its_lambda_body() {
    let source = r#"
        fn leaf() {}
        pub fn run() {
            let callback: Box<dyn Fn()> = Box::new(|| leaf());
            callback();
        }
    "#;
    let analysis = diffkit::language::rust::analyze_semantic_source(source, &[]).unwrap();
    let graph = ProgramGraph::from_files([analysis]).unwrap();
    let run = graph.resolve_entry("run").unwrap().unwrap();
    let tree = graph.build_call_tree(&run, 8).unwrap();
    let rendered = diffkit::render_call_tree_with_options(
        &tree,
        &RenderOptions {
            show_types: false,
            color: ColorMode::Plain,
        },
    );

    assert!(rendered.contains("dyn Fn()::call"), "{rendered}");
    assert!(rendered.contains("λ#1"), "{rendered}");
    assert!(rendered.contains("leaf()"), "{rendered}");
    assert!(!rendered.contains("[unresolved]"), "{rendered}");
}

#[test]
fn nested_async_closures_keep_their_lexical_parent_and_body() {
    let before = r#"
        async fn work() {}
        pub async fn run() {
            let outer = async || {
                let inner = async || work().await;
                inner().await;
            };
            outer().await;
        }
    "#;
    let after = before.replace(
        "async fn work() {}",
        "async fn work() { finish(); } fn finish() {}",
    );
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

    assert!(rendered.contains("λouter()"), "{rendered}");
    assert!(rendered.contains("λinner()"), "{rendered}");
    assert!(rendered.contains("finish()"), "{rendered}");
}
