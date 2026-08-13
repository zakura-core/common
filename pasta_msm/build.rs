use std::{env, path::PathBuf};

include!("build_selection.rs");

fn main() {
    println!("cargo:rerun-if-changed=native");
    println!("cargo:rerun-if-changed=build_selection.rs");
    println!("cargo:rerun-if-env-changed=CARGO_CFG_TARGET_FEATURE");
    println!("cargo:rerun-if-env-changed=CXX");
    println!("cargo:rerun-if-env-changed=CXXFLAGS");

    let target_arch =
        env::var("CARGO_CFG_TARGET_ARCH").expect("Cargo must provide CARGO_CFG_TARGET_ARCH");
    let target_env =
        env::var("CARGO_CFG_TARGET_ENV").expect("Cargo must provide CARGO_CFG_TARGET_ENV");
    if !matches!(target_arch.as_str(), "aarch64" | "x86_64") {
        panic!("pasta-msm supports only aarch64 and x86_64 targets");
    }
    let target_features = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_default();
    let use_adx = target_uses_adx(&target_arch, &target_features);

    let semolina = PathBuf::from("native/semolina");
    let mut field = cc::Build::new();
    field.include(&semolina).file(semolina.join("pasta.c"));
    if use_adx {
        field.define("__ADX__", None);
    }

    if target_env == "msvc" {
        let suffix = if target_arch == "x86_64" {
            "x86_64"
        } else {
            "armv8"
        };
        let win64 = semolina.join("win64");
        field
            .file(win64.join(format!("ct_inverse_mod_256-{suffix}.asm")))
            .file(win64.join(format!("pasta_add-{suffix}.asm")))
            .file(semolina.join(msvc_multiplication_assembly(&target_arch, use_adx)));
    } else {
        field.file(semolina.join("assembly.S"));
    }

    field
        .flag_if_supported("-mno-avx")
        .flag_if_supported("-fno-builtin")
        .flag_if_supported("-Wno-unused-function")
        .flag_if_supported("-Wno-unused-command-line-argument")
        .compile("zakura_pasta_msm_field");

    let mut bridge = cc::Build::new();
    bridge
        .cpp(true)
        .include("native")
        .include(&semolina)
        .file("native/msm.cpp")
        .flag_if_supported("-mno-avx")
        .flag_if_supported("-fno-builtin")
        .flag_if_supported("-std=c++11")
        .flag_if_supported("-Wno-unused-function")
        .flag_if_supported("-Wno-unused-command-line-argument");
    if use_adx {
        bridge.define("__ADX__", None);
    }
    bridge.compile("zakura_pasta_msm_bridge");
}
