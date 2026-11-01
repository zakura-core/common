use std::env;

const X86_64_ASM_CFG: &str = "pasta_curves_x86_64_asm";

fn main() {
    println!("cargo:rustc-check-cfg=cfg({X86_64_ASM_CFG})");
    println!("cargo:rerun-if-changed=src/asm/pasta_mul-armv8.S");
    println!("cargo:rustc-check-cfg=cfg(miri)");

    if use_x86_64_asm() {
        println!("cargo:rustc-cfg={X86_64_ASM_CFG}");
    }

    #[cfg(feature = "aarch64-asm")]
    build_aarch64_asm();
}

fn use_x86_64_asm() -> bool {
    if env::var("CARGO_CFG_TARGET_ARCH").as_deref() != Ok("x86_64")
        || env::var("CARGO_CFG_TARGET_POINTER_WIDTH").as_deref() != Ok("64")
    {
        return false;
    }

    // `portable` is a safety override, including under `--all-features`.
    if cfg!(feature = "portable") {
        return false;
    }

    // Include the backend for baseline and cross-compiled x86-64 builds.
    // Runtime CPU detection decides whether its instructions may execute.
    true
}

#[cfg(feature = "aarch64-asm")]
fn build_aarch64_asm() {
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let target_endian = env::var("CARGO_CFG_TARGET_ENDIAN").unwrap();
    let target_family = env::var("CARGO_CFG_TARGET_FAMILY").ok();
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap();
    let target_pointer_width = env::var("CARGO_CFG_TARGET_POINTER_WIDTH").unwrap();
    let target_is_unix = target_family
        .as_deref()
        .is_some_and(|families| families.split(',').any(|family| family == "unix"));

    if target_arch == "aarch64"
        && target_endian == "little"
        && (target_is_unix || target_os == "none")
        && target_pointer_width == "64"
    {
        cc::Build::new()
            .file("src/asm/pasta_mul-armv8.S")
            .compile("pasta_curves_aarch64");
    }
}
