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
