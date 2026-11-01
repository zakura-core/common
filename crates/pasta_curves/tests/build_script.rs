use std::{
    env, fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    time::{SystemTime, UNIX_EPOCH},
};

const ASM_DIRECTIVE: &str = "cargo:rustc-cfg=pasta_curves_x86_64_asm";
const BASELINE: [bool; 4] = [false, true, false, false];
const TARGET_ASM: [bool; 4] = [true, true, false, false];
const NEVER_ASM: [bool; 4] = [false; 4];

struct Case<'a> {
    name: &'a str,
    environment: &'a [(&'a str, Option<&'a str>)],
    selected: [bool; 4],
}

struct BuildScript {
    executable: PathBuf,
}

impl BuildScript {
    fn compile(mode: &str, features: &[&str]) -> Self {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
        let directory = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!(
            "pasta-build-script-{}-{mode}-{}",
            std::process::id(),
            nonce.as_nanos(),
        ));
        fs::create_dir_all(&directory).unwrap();
        let script = Self {
            executable: directory.join(format!("build-script{}", env::consts::EXE_SUFFIX)),
        };
        let rustc = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
        let mut command = Command::new(rustc);
        command
            .current_dir(env!("CARGO_MANIFEST_DIR"))
            .args(["--edition=2024", "--crate-name", "pasta_build_script"])
            .arg("build.rs")
            .arg("-o")
            .arg(&script.executable);
        // Compile only the selection logic, regardless of Cargo's features.
        // In particular, `aarch64-asm` must not introduce a `cc` dependency.
        for feature in features {
            command.arg("--cfg").arg(format!("feature={feature:?}"));
        }
        let output = command.output().expect("failed to invoke rustc");
        assert!(
            output.status.success(),
            "{mode} build-script compilation failed: {}",
            String::from_utf8_lossy(&output.stderr),
        );
        script
    }

    fn run(&self, case: &Case<'_>) -> Output {
        let mut command = Command::new(&self.executable);
        command.env_clear().envs([
            ("CARGO_CFG_TARGET_ARCH", "x86_64"),
            ("CARGO_CFG_TARGET_POINTER_WIDTH", "64"),
            ("CARGO_CFG_TARGET_FEATURE", "fxsr,sse,sse2"),
            ("HOST", "x86_64-unknown-linux-gnu"),
            ("TARGET", "x86_64-unknown-linux-gnu"),
            ("CARGO_ENCODED_RUSTFLAGS", ""),
        ]);
        for &(name, value) in case.environment {
            if let Some(value) = value {
                command.env(name, value);
            } else {
                command.env_remove(name);
            }
        }
        command.output().expect("failed to run build script")
    }
}

impl Drop for BuildScript {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.executable);
        let _ = fs::remove_dir(self.executable.parent().unwrap());
    }
}

#[test]
fn x86_64_assembly_respects_target_features_and_overrides() {
    // Expected selections follow this mode order. `portable` always wins.
    let modes: &[(&str, &[&str])] = &[
        ("default", &[]),
        ("forced", &["x86_64-asm"]),
        ("portable", &["portable"]),
        ("forced-portable", &["x86_64-asm", "portable"]),
    ];
    let cases = [
        Case {
            name: "same-triple baseline",
            environment: &[],
            selected: BASELINE,
        },
        Case {
            name: "missing target features",
            environment: &[("CARGO_CFG_TARGET_FEATURE", None)],
            selected: BASELINE,
        },
        Case {
            name: "empty target features",
            environment: &[("CARGO_CFG_TARGET_FEATURE", Some(""))],
            selected: BASELINE,
        },
        Case {
            name: "ADX alone",
            environment: &[("CARGO_CFG_TARGET_FEATURE", Some("sse2,adx"))],
            selected: BASELINE,
        },
        Case {
            name: "BMI2 alone",
            environment: &[("CARGO_CFG_TARGET_FEATURE", Some("bmi2,sse2"))],
            selected: BASELINE,
        },
        Case {
            name: "both required features",
            environment: &[("CARGO_CFG_TARGET_FEATURE", Some("adx,bmi2"))],
            selected: TARGET_ASM,
        },
        Case {
            name: "required features among other features",
            environment: &[("CARGO_CFG_TARGET_FEATURE", Some("bmi2,sse2,adx"))],
            selected: TARGET_ASM,
        },
        Case {
            name: "ADX token must match exactly",
            environment: &[("CARGO_CFG_TARGET_FEATURE", Some("adx2,bmi2"))],
            selected: BASELINE,
        },
        Case {
            name: "BMI2 token must match exactly",
            environment: &[("CARGO_CFG_TARGET_FEATURE", Some("adx,bmi20"))],
            selected: BASELINE,
        },
        Case {
            name: "native rustflags do not replace resolved features",
            environment: &[("CARGO_ENCODED_RUSTFLAGS", Some("-C\x1ftarget-cpu=native"))],
            selected: BASELINE,
        },
        Case {
            name: "feature rustflags do not replace resolved features",
            environment: &[(
                "CARGO_ENCODED_RUSTFLAGS",
                Some("-C\x1ftarget-feature=+adx,+bmi2"),
            )],
            selected: BASELINE,
        },
        Case {
            name: "resolved target features are authoritative",
            environment: &[
                ("CARGO_CFG_TARGET_FEATURE", Some("adx,bmi2")),
                ("CARGO_ENCODED_RUSTFLAGS", Some("-C\x1ftarget-feature=-adx")),
            ],
            selected: TARGET_ASM,
        },
        Case {
            name: "cross-compilation baseline",
            environment: &[("HOST", Some("aarch64-unknown-linux-gnu"))],
            selected: BASELINE,
        },
        Case {
            name: "cross-compilation uses target features",
            environment: &[
                ("HOST", Some("aarch64-unknown-linux-gnu")),
                ("CARGO_CFG_TARGET_FEATURE", Some("adx,bmi2")),
            ],
            selected: TARGET_ASM,
        },
        Case {
            name: "other architectures reject forced assembly",
            environment: &[
                ("CARGO_CFG_TARGET_ARCH", Some("aarch64")),
                ("CARGO_CFG_TARGET_FEATURE", Some("adx,bmi2")),
            ],
            selected: NEVER_ASM,
        },
        Case {
            name: "32-bit targets reject forced assembly",
            environment: &[
                ("CARGO_CFG_TARGET_POINTER_WIDTH", Some("32")),
                ("CARGO_CFG_TARGET_FEATURE", Some("adx,bmi2")),
            ],
            selected: NEVER_ASM,
        },
    ];

    for (index, &(mode, features)) in modes.iter().enumerate() {
        let script = BuildScript::compile(mode, features);
        for case in &cases {
            let output = script.run(case);
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                output.status.success(),
                "{mode}: {} failed: {stderr}",
                case.name,
            );
            assert_eq!(
                stdout.lines().any(|line| line == ASM_DIRECTIVE),
                case.selected[index],
                "{mode}: {}; stdout: {stdout}; stderr: {stderr}",
                case.name,
            );
        }
    }
}
