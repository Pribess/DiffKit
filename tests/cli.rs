use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

static TEST_SEQUENCE: AtomicU64 = AtomicU64::new(0);
static RUST_PROJECT_FIXTURE: OnceLock<TestRepository> = OnceLock::new();

fn fixture(relative: &str) -> PathBuf {
    let repository = RUST_PROJECT_FIXTURE.get_or_init(|| {
        let repository = TestRepository::new();
        repository.write(
            "Cargo.toml",
            "[package]\nname = \"fixture-project\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[lib]\npath = \"src/lib.rs\"\n",
        );
        repository.write("src/lib.rs", "mod service;\nmod storage;\npub use service::entry;\n");
        repository.write(
            "src/service.rs",
            "use crate::storage::{Postgres, Store};\n#[derive(Clone, Copy)]\npub struct Order;\npub fn entry(order: Order) { run(&Postgres, order); }\nfn run<S: Store>(storage: &S, order: Order) { storage.save(order); }\npub fn detached<S: Store>(storage: &S, order: Order) { storage.save(order); }\n",
        );
        repository.write(
            "src/storage.rs",
            "use crate::service::Order;\npub trait Store { fn save(&self, order: Order); }\npub struct Postgres;\nimpl Store for Postgres { fn save(&self, order: Order) { write(order); } }\nfn write(_order: Order) {}\n",
        );
        repository
    });
    repository.path().join(relative)
}

#[test]
fn help_is_colored_by_default_even_when_no_color_is_set() {
    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .arg("-h")
        .env("NO_COLOR", "1")
        .output()
        .unwrap();
    assert!(output.status.success());
    assert!(output.stdout.windows(2).any(|bytes| bytes == b"\x1b["));
}

#[test]
fn plain_mode_removes_colors_from_help() {
    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args(["--color=plain", "-h"])
        .output()
        .unwrap();
    assert!(output.status.success());
    assert!(!output.stdout.windows(2).any(|bytes| bytes == b"\x1b["));
}

#[test]
fn file_command_uses_cargo_semantics_but_stops_at_the_selected_file() {
    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args([
            "file",
            fixture("src/service.rs").to_str().unwrap(),
            "--color=plain",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!stderr.contains("Analyzing Rust semantics"), "{stderr}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("entry(order)"), "{stdout}");
    assert!(
        stdout.contains("run<Postgres>(&Postgres, order)"),
        "{stdout}"
    );
    assert!(stdout.contains("Postgres::save(order)"), "{stdout}");
    assert!(!stdout.contains("write(order)"), "{stdout}");
}

#[test]
fn file_entry_must_be_declared_in_the_selected_file() {
    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args([
            "file",
            fixture("src/service.rs").to_str().unwrap(),
            "--color=plain",
            "-e",
            "write",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("entry not found"), "{stderr}");
    assert!(stderr.contains("selected file"), "{stderr}");
}

#[test]
fn project_entry_can_seed_an_unobserved_generic_instance() {
    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args([
            "file",
            fixture("src/service.rs").to_str().unwrap(),
            "--color=plain",
            "-e",
            "detached<Postgres>",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("detached<Postgres>(storage, order)"),
        "{stdout}"
    );
    assert!(stdout.contains("Postgres::save(order)"), "{stdout}");
    assert!(!stdout.contains("__diffkit_seed"), "{stdout}");
}

#[test]
fn types_mode_attaches_concrete_types_to_the_same_call_line() {
    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args([
            "file",
            fixture("src/service.rs").to_str().unwrap(),
            "--color=plain",
            "--types",
            "-e",
            "entry",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("entry(order: Order)"), "{stdout}");
    assert!(
        stdout.contains("run<Postgres>(&Postgres: &Postgres, order: Order)"),
        "{stdout}"
    );
    assert!(stdout.contains("Postgres::save(order: Order)"), "{stdout}");
}

#[test]
fn standalone_ocaml_file_comparison_matches_roots_across_file_names() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let before = manifest.join("examples/ocaml/before.ml");
    let after = manifest.join("examples/ocaml/after.ml");
    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args([
            "file",
            before.to_str().unwrap(),
            after.to_str().unwrap(),
            "--color=plain",
            "-e",
            "run",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("  run order"), "{stdout}");
    assert!(!stdout.contains("Before.run"), "{stdout}");
    assert!(!stdout.contains("After.run"), "{stdout}");
}

#[test]
fn rust_file_outside_cargo_targets_falls_back_to_standalone_semantics() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let before = manifest.join("examples/rust/before.rs");
    let after = manifest.join("examples/rust/after.rs");
    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args([
            "file",
            before.to_str().unwrap(),
            after.to_str().unwrap(),
            "--color=plain",
            "-e",
            "checkout",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("checkout(total)"), "{stdout}");
    assert!(stdout.contains("prepare(total)"), "{stdout}");
}

#[test]
fn default_git_mode_propagates_a_multifile_change_to_the_project_root() {
    let repository = TestRepository::new();
    repository.write(
        "Cargo.toml",
        "[package]\nname = \"git-fixture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    );
    repository.write(
        "src/main.rs",
        "mod service;\nfn main() { service::entry(); }\n",
    );
    repository.write(
        "src/service.rs",
        "pub fn entry() { save(); }\nfn save() {}\n",
    );
    repository.git(["init", "--quiet"]);
    repository.git(["config", "user.email", "diffkit@example.invalid"]);
    repository.git(["config", "user.name", "DiffKit Test"]);
    repository.git(["add", "."]);
    repository.git(["commit", "--quiet", "-m", "before"]);
    repository.write(
        "src/service.rs",
        "pub fn entry() { save(); audit(); }\nfn save() {}\nfn audit() {}\n",
    );

    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args(["--color=plain"])
        .current_dir(repository.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!stderr.contains("Analyzing Rust semantics"), "{stderr}");
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("main()"), "{stdout}");
    assert!(stdout.contains("entry()"), "{stdout}");
    assert!(
        stdout.contains("+    └─ audit()") || stdout.contains("+     └─ audit()"),
        "{stdout}"
    );

    let cached = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args(["--color=plain", "--verbose"])
        .current_dir(repository.path())
        .output()
        .unwrap();
    assert!(
        cached.status.success(),
        "{}",
        String::from_utf8_lossy(&cached.stderr)
    );
    let stderr = String::from_utf8_lossy(&cached.stderr);
    assert!(stderr.contains("Analyzing Rust semantics"), "{stderr}");
    assert!(stderr.contains("cache hit: git-before"), "{stderr}");
    assert!(stderr.contains("cache hit: git-after"), "{stderr}");

    repository.write(
        "src/service.rs",
        "pub fn entry() { save(); audit(); trace(); }\nfn save() {}\nfn audit() {}\nfn trace() {}\n",
    );
    let invalidated = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args(["--color=plain", "--verbose"])
        .current_dir(repository.path())
        .output()
        .unwrap();
    assert!(
        invalidated.status.success(),
        "{}",
        String::from_utf8_lossy(&invalidated.stderr)
    );
    let stderr = String::from_utf8_lossy(&invalidated.stderr);
    assert!(stderr.contains("cache hit: git-before"), "{stderr}");
    assert!(stderr.contains("cache miss: git-after"), "{stderr}");
}

#[test]
fn git_mode_treats_a_functionless_module_file_as_project_analyzed() {
    let repository = TestRepository::new();
    repository.write(
        "Cargo.toml",
        "[package]\nname = \"module-fixture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    );
    repository.write("src/lib.rs", "pub mod service;\n");
    repository.write("src/service.rs", "pub fn run() {}\n");
    repository.git(["init", "--quiet"]);
    repository.git(["config", "user.email", "diffkit@example.invalid"]);
    repository.git(["config", "user.name", "DiffKit Test"]);
    repository.git(["add", "."]);
    repository.git(["commit", "--quiet", "-m", "before"]);
    repository.write(
        "src/lib.rs",
        "// The module file itself still has no function body.\npub mod service;\n",
    );

    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args(["--color=plain"])
        .current_dir(repository.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("No call changes between HEAD and worktree."));
}

#[test]
fn git_pathspec_keeps_project_context_but_excludes_other_changes() {
    let repository = TestRepository::new();
    repository.write(
        "Cargo.toml",
        "[package]\nname = \"pathspec-fixture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    );
    repository.write(
        "src/main.rs",
        "mod selected;\nmod ignored;\nfn main() { selected::entry(); ignored::entry(); }\n",
    );
    repository.write(
        "src/selected.rs",
        "pub fn entry() { save(); }\nfn save() {}\n",
    );
    repository.write(
        "src/ignored.rs",
        "pub fn entry() { save(); }\nfn save() {}\n",
    );
    repository.git(["init", "--quiet"]);
    repository.git(["config", "user.email", "diffkit@example.invalid"]);
    repository.git(["config", "user.name", "DiffKit Test"]);
    repository.git(["add", "."]);
    repository.git(["commit", "--quiet", "-m", "before"]);
    repository.write(
        "src/selected.rs",
        "pub fn entry() { save(); audit(); }\nfn save() {}\nfn audit() {}\n",
    );
    repository.write(
        "src/ignored.rs",
        "pub fn entry() { save(); telemetry(); }\nfn save() {}\nfn telemetry() {}\n",
    );

    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args(["--color=plain", "--", "src/selected.rs"])
        .current_dir(repository.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("audit()"), "{stdout}");
    assert!(!stdout.contains("telemetry()"), "{stdout}");
}

#[test]
fn git_mode_analyzes_changed_rust_files_outside_cargo_targets() {
    let repository = TestRepository::new();
    repository.write(
        "Cargo.toml",
        "[package]\nname = \"standalone-fixture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    );
    repository.write("src/main.rs", "fn main() {}\n");
    repository.write(
        "snippets/sample.rs",
        "pub fn run() { save(); }\nfn save() {}\n",
    );
    repository.git(["init", "--quiet"]);
    repository.git(["config", "user.email", "diffkit@example.invalid"]);
    repository.git(["config", "user.name", "DiffKit Test"]);
    repository.git(["add", "."]);
    repository.git(["commit", "--quiet", "-m", "before"]);
    repository.write(
        "snippets/sample.rs",
        "pub fn run() { save(); audit(); }\nfn save() {}\nfn audit() {}\n",
    );

    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args(["--color=plain"])
        .current_dir(repository.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("run()"), "{stdout}");
    assert!(stdout.contains("audit()"), "{stdout}");
}

#[test]
fn git_mode_analyzes_standalone_ocaml_files_without_dune() {
    let repository = TestRepository::new();
    repository.write(
        "service.ml",
        "let run value = save value\nand save value = value\n",
    );
    repository.git(["init", "--quiet"]);
    repository.git(["config", "user.email", "diffkit@example.invalid"]);
    repository.git(["config", "user.name", "DiffKit Test"]);
    repository.git(["add", "."]);
    repository.git(["commit", "--quiet", "-m", "before"]);
    repository.write(
        "service.ml",
        "let run value = save value; audit value\nand save value = value\nand audit value = value\n",
    );

    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args(["--color=plain"])
        .current_dir(repository.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("run value"), "{stdout}");
    assert!(stdout.contains("audit value"), "{stdout}");
}

#[test]
fn git_mode_analyzes_code_behind_non_default_cargo_features() {
    let repository = TestRepository::new();
    repository.write(
        "Cargo.toml",
        "[package]\nname = \"feature-fixture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[features]\ndefault = []\nbalance = []\n",
    );
    repository.write(
        "src/lib.rs",
        "#[cfg(feature = \"balance\")]\npub fn run() { save(); }\n#[cfg(feature = \"balance\")]\nfn save() {}\n",
    );
    repository.git(["init", "--quiet"]);
    repository.git(["config", "user.email", "diffkit@example.invalid"]);
    repository.git(["config", "user.name", "DiffKit Test"]);
    repository.git(["add", "."]);
    repository.git(["commit", "--quiet", "-m", "before"]);
    repository.write(
        "src/lib.rs",
        "#[cfg(feature = \"balance\")]\npub fn run() { save(); audit(); }\n#[cfg(feature = \"balance\")]\nfn save() {}\n#[cfg(feature = \"balance\")]\nfn audit() {}\n",
    );

    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args(["--color=plain", "--entry", "run"])
        .current_dir(repository.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("run()"), "{stdout}");
    assert!(stdout.contains("audit()"), "{stdout}");
}

#[test]
fn project_closure_contexts_stay_stable_when_source_lines_move() {
    let repository = TestRepository::new();
    repository.write(
        "Cargo.toml",
        "[package]\nname = \"closure-lines\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    );
    repository.write(
        "src/lib.rs",
        "fn apply<F: FnOnce()>(f: F) { let invoke = || f(); invoke(); }\nfn work() {}\npub fn run() { apply(|| work()); }\n",
    );
    repository.git(["init", "--quiet"]);
    repository.git(["config", "user.email", "diffkit@example.invalid"]);
    repository.git(["config", "user.name", "DiffKit Test"]);
    repository.git(["add", "."]);
    repository.git(["commit", "--quiet", "-m", "before"]);
    repository.write(
        "src/lib.rs",
        "// Moving a closure must not create a new monomorphization identity.\n\nfn apply<F: FnOnce()>(f: F) { let invoke = || f(); invoke(); }\nfn work() {}\npub fn run() { apply(|| work()); }\n",
    );

    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args(["--color=plain"])
        .current_dir(repository.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("No call changes between HEAD and worktree."),
        "{stdout}"
    );

    let tree = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args([
            "file",
            repository.path().join("src/lib.rs").to_str().unwrap(),
            "--color=plain",
            "--entry",
            "run",
        ])
        .output()
        .unwrap();
    assert!(
        tree.status.success(),
        "{}",
        String::from_utf8_lossy(&tree.stderr)
    );
    let stdout = String::from_utf8(tree.stdout).unwrap();
    assert!(stdout.contains("λinvoke<λ#1>"), "{stdout}");
    assert!(!stdout.contains("{closure@"), "{stdout}");
}

#[test]
fn macro_expanded_closure_contexts_stay_stable_when_source_lines_move() {
    let repository = TestRepository::new();
    repository.write(
        "Cargo.toml",
        "[package]\nname = \"macro-closure-lines\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    );
    let source = r#"macro_rules! runner {
    ($name:ident) => {
        pub fn $name() { invoke(|| work()); }
    };
}

fn invoke<F: FnOnce()>(f: F) { f(); }
fn work() {}
runner!(run);
"#;
    repository.write("src/lib.rs", source);
    repository.git(["init", "--quiet"]);
    repository.git(["config", "user.email", "diffkit@example.invalid"]);
    repository.git(["config", "user.name", "DiffKit Test"]);
    repository.git(["add", "."]);
    repository.git(["commit", "--quiet", "-m", "before"]);
    repository.write(
        "src/lib.rs",
        &format!("// Shift the macro's compiler span without changing calls.\n\n{source}"),
    );

    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args(["--color=plain"])
        .current_dir(repository.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("No call changes between HEAD and worktree."),
        "{stdout}"
    );
    assert!(!stdout.contains("{closure@"), "{stdout}");

    let tree = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args([
            "file",
            repository.path().join("src/lib.rs").to_str().unwrap(),
            "--color=plain",
            "--entry",
            "invoke",
        ])
        .output()
        .unwrap();
    assert!(
        tree.status.success(),
        "{}",
        String::from_utf8_lossy(&tree.stderr)
    );
    let stdout = String::from_utf8(tree.stdout).unwrap();
    assert!(stdout.contains("invoke<λrun#1>"), "{stdout}");
    assert!(!stdout.contains("{closure@"), "{stdout}");
    assert!(!stdout.contains("{lambda-def:"), "{stdout}");
}

#[test]
fn rust_context_crosses_a_workspace_crate_generic_body() {
    let repository = TestRepository::new();
    repository.write(
        "Cargo.toml",
        "[workspace]\nmembers = [\"app\", \"store-core\"]\nresolver = \"3\"\n",
    );
    repository.write(
        "store-core/Cargo.toml",
        "[package]\nname = \"store-core\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    );
    repository.write(
        "store-core/src/lib.rs",
        "pub trait Store { fn save(&self); }\npub fn run<T: Store>(store: T) { store.save(); }\npub fn run_dyn(store: &dyn Store) { store.save(); }\n",
    );
    repository.write(
        "app/Cargo.toml",
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\nstore-core = { path = \"../store-core\" }\n",
    );
    repository.write(
        "app/src/main.rs",
        "struct Postgres;\nimpl store_core::Store for Postgres { fn save(&self) { write(); } }\nfn write() {}\nfn main() { store_core::run(Postgres); store_core::run_dyn(&Postgres); }\n",
    );

    repository.git(["init", "--quiet"]);
    repository.git(["config", "user.email", "diffkit@example.invalid"]);
    repository.git(["config", "user.name", "DiffKit Test"]);
    repository.git(["add", "."]);
    repository.git(["commit", "--quiet", "-m", "before"]);
    repository.write(
        "app/src/main.rs",
        "struct Postgres;\nimpl store_core::Store for Postgres { fn save(&self) { write(); } }\nfn write() { audit(); }\nfn audit() {}\nfn main() { store_core::run(Postgres); store_core::run_dyn(&Postgres); }\n",
    );

    let output = Command::new(env!("CARGO_BIN_EXE_diffkit"))
        .args(["--color=plain", "-e", "main"])
        .current_dir(repository.path())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("main()"), "{stdout}");
    assert!(stdout.contains("run<Postgres>(Postgres)"), "{stdout}");
    assert!(stdout.contains("run_dyn(&Postgres)"), "{stdout}");
    assert!(stdout.contains("dyn Store::save()"), "{stdout}");
    assert!(stdout.contains("Postgres::save()"), "{stdout}");
    assert!(stdout.contains("audit()"), "{stdout}");
}

struct TestRepository {
    path: PathBuf,
}

impl TestRepository {
    fn new() -> Self {
        let sequence = TEST_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "diffkit-cli-test-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn write(&self, relative: &str, contents: &str) {
        let destination = self.path.join(relative);
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(destination, contents).unwrap();
    }

    fn git<const N: usize>(&self, arguments: [&str; N]) {
        let status = Command::new("git")
            .args(arguments)
            .current_dir(&self.path)
            .status()
            .unwrap();
        assert!(status.success());
    }
}

impl Drop for TestRepository {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
