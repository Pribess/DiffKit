use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static TEST_SEQUENCE: AtomicU64 = AtomicU64::new(0);

fn fixture(relative: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/rust_project")
        .join(relative)
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
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("main()"), "{stdout}");
    assert!(stdout.contains("entry()"), "{stdout}");
    assert!(
        stdout.contains("+    └─ audit()") || stdout.contains("+     └─ audit()"),
        "{stdout}"
    );
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
