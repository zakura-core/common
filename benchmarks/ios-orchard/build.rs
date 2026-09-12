use std::{env, process::Command};

fn command_output(program: &str, args: &[&str]) -> Option<String> {
    let output = Command::new(program).args(args).output().ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn main() {
    println!("cargo:rerun-if-changed=../../.git/HEAD");
    println!("cargo:rerun-if-env-changed=ORCHARD_BENCH_OPT_FLAGS");
    println!("cargo:rerun-if-env-changed=ORCHARD_BENCH_XCODE_VERSION");

    let git_commit =
        command_output("git", &["rev-parse", "HEAD"]).unwrap_or_else(|| "unknown".to_owned());
    let git_status =
        command_output("git", &["status", "--porcelain"]).unwrap_or_else(|| "unknown".to_owned());
    let rustc = env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    let rust_version = command_output(&rustc, &["-Vv"])
        .unwrap_or_else(|| "unknown".to_owned())
        .replace('\n', "; ");
    let target = env::var("TARGET").unwrap_or_else(|_| "unknown".to_owned());
    let opt_flags =
        env::var("ORCHARD_BENCH_OPT_FLAGS").unwrap_or_else(|_| "Cargo release defaults".to_owned());
    let xcode_version =
        env::var("ORCHARD_BENCH_XCODE_VERSION").unwrap_or_else(|_| "not supplied".to_owned());

    println!("cargo:rustc-env=ORCHARD_BENCH_GIT_COMMIT={git_commit}");
    println!(
        "cargo:rustc-env=ORCHARD_BENCH_GIT_DIRTY={}",
        !git_status.is_empty()
    );
    println!("cargo:rustc-env=ORCHARD_BENCH_RUST_VERSION={rust_version}");
    println!("cargo:rustc-env=ORCHARD_BENCH_TARGET={target}");
    println!("cargo:rustc-env=ORCHARD_BENCH_OPT_FLAGS={opt_flags}");
    println!("cargo:rustc-env=ORCHARD_BENCH_XCODE_VERSION={xcode_version}");
}
