use std::env;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-env-changed=RUSTC");

    if !cfg!(any(target_os = "macos", target_os = "linux")) {
        return;
    }
    let rustc = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let Ok(output) = Command::new(rustc).args(["--print", "sysroot"]).output() else {
        return;
    };
    if !output.status.success() {
        return;
    }
    let Ok(sysroot) = String::from_utf8(output.stdout) else {
        return;
    };
    let compiler_library_directory = format!("{}/lib", sysroot.trim());
    println!("cargo:rustc-link-arg=-Wl,-rpath,{compiler_library_directory}");
}
