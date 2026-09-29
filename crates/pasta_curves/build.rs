use std::env;

const X86_64_ASM_CFG: &str = "pasta_curves_x86_64_asm";
const REQUIRED_X86_64_FEATURES: [&str; 2] = ["adx", "bmi2"];

fn main() {
    println!("cargo:rustc-check-cfg=cfg({X86_64_ASM_CFG})");
    println!("cargo:rerun-if-changed=src/asm/pasta_mul-armv8.S");

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

    if cfg!(feature = "x86_64-asm") {
        return true;
    }

    // Use the compiler's resolved target features, not the build CPU. Equal
    // HOST and TARGET triples do not imply an implicit native target.
    let target_features = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_default();
    has_required_x86_64_features(&target_features)
}

fn has_required_x86_64_features(target_features: &str) -> bool {
    REQUIRED_X86_64_FEATURES.iter().all(|required| {
        target_features
            .split(',')
            .any(|feature| feature == *required)
    })
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
