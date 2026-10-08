//! Isolated Cargo consumers for Udon's compiler and artifact tests.

use std::{fs, path::Path, path::PathBuf, process::Command};

pub struct Consumer {
    // Retain ownership until all synchronous Cargo invocations and artifact
    // inspections finish, including when the test unwinds.
    directory: tempfile::TempDir,
    pub target: PathBuf,
}

impl Consumer {
    /// Copies a fixture, relative to this crate's `tests/`, into its own workspace.
    ///
    /// A single source file becomes `src/main.rs`; directories preserve their
    /// complete fixture layout.
    ///
    /// Artifact fixtures with a build script receive Bento and Udon in both
    /// dependency roles. Other fixtures depend only on the requested Udon alias.
    pub fn new(package: &str, fixture: &str, alias: &str, extra_features: &[&str]) -> Self {
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let workspace = manifest.join("../..").canonicalize().unwrap();
        let source = manifest.join("tests").join(fixture);
        let directory = tempfile::Builder::new()
            .prefix(&format!("udon-{package}-"))
            .tempdir()
            .unwrap();
        let root = directory.path();
        if source.is_dir() {
            copy_fixture(&source, root);
        } else {
            fs::create_dir(root.join("src")).unwrap();
            fs::copy(&source, root.join("src/main.rs")).unwrap();
        }
        let udon = workspace.join("crates/udon");
        let mut dependencies = format!(
            "{alias} = {{ package = \"zakura-udon\", path = {udon:?}, default-features = false }}\n"
        );
        let mut build_dependencies = String::new();
        if root.join("build.rs").is_file() {
            let bento = workspace.join("crates/bento");
            dependencies.push_str(&format!(
                "bento = {{ package = \"zakura-bento\", path = {bento:?} }}\n"
            ));
            build_dependencies = format!("[build-dependencies]\n{dependencies}");
        }
        let extra_features: String = extra_features
            .iter()
            .map(|name| format!("{name} = []\n"))
            .collect();
        fs::write(
            root.join("Cargo.toml"),
            format!(
                r#"[package]
name = "{package}"
version = "0.0.0"
edition = "2024"
publish = false

[workspace]

[features]
sqrt-table-large = ["{alias}/sqrt-table-large"]
aarch64-asm = ["{alias}/aarch64-asm"]
x86_64-asm = ["{alias}/x86_64-asm"]
portable = ["{alias}/portable"]
traits = ["{alias}/traits"]
poseidon = ["{alias}/poseidon"]
{extra_features}
[dependencies]
{dependencies}
{build_dependencies}
"#
            ),
        )
        .unwrap();
        // Offline resolution may adapt the seed to the consumer's graph.
        fs::copy(workspace.join("Cargo.lock"), root.join("Cargo.lock")).unwrap();
        let target = root.join("target");
        Self { directory, target }
    }

    /// Runs a full build or executable and checks the expected outcome.
    ///
    /// Rejections must include the diagnostic and one of the supplied source
    /// paths, so a generator failure cannot stand in for consumer validation.
    pub fn check(
        &self,
        command: &str,
        features: &str,
        environment: &[(&str, &str)],
        diagnostic: Option<&str>,
        sources: &[&str],
    ) {
        let output = Command::new(env!("CARGO"))
            .current_dir(self.directory.path())
            .args([
                command,
                "--release",
                "--quiet",
                "--offline",
                "--features",
                features,
            ])
            .envs(environment.iter().copied())
            .env("CARGO_TARGET_DIR", &self.target)
            .env("CARGO_TERM_COLOR", "never")
            .output()
            .expect("execute the nested Cargo consumer");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let context = format!("cargo {command}, features {features:?}, env {environment:?}");
        if let Some(diagnostic) = diagnostic {
            assert!(
                !output.status.success(),
                "{context} unexpectedly succeeded:\n{stdout}{stderr}"
            );
            assert!(
                stderr.contains(diagnostic),
                "wrong rejection for {context}:\n{stdout}{stderr}"
            );
            assert!(
                sources.iter().any(|source| stderr.contains(source)),
                "rejection must come from {sources:?} for {context}:\n{stdout}{stderr}"
            );
        } else {
            assert!(
                output.status.success(),
                "{context} failed:\n{stdout}{stderr}"
            );
        }
    }
}

fn copy_fixture(source: &Path, destination: &Path) {
    fs::create_dir_all(destination).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        let target = destination.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_fixture(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), target).unwrap();
        }
    }
}

/// Feature sets that must not change stored representations: each arithmetic
/// backend, with and without the large square-root tables.
///
/// `x86_64-asm` forces the BMI2/ADX backend on x86-64 targets, so it is
/// exercised only where the host can execute it; elsewhere the feature is
/// inert, as `aarch64-asm` is on x86-64.
#[allow(dead_code)] // The API consumers never run generators.
pub fn arithmetic_feature_sets() -> Vec<&'static str> {
    let mut sets = vec![
        "",
        "sqrt-table-large",
        "aarch64-asm",
        "aarch64-asm,sqrt-table-large",
    ];
    if x86_64_asm_runs_on_host() {
        sets.extend(["x86_64-asm", "x86_64-asm,sqrt-table-large"]);
    }
    sets
}

#[allow(dead_code)]
fn x86_64_asm_runs_on_host() -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        std::arch::is_x86_feature_detected!("adx") && std::arch::is_x86_feature_detected!("bmi2")
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        true
    }
}
