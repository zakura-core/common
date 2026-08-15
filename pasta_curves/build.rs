#[cfg(any(feature = "aarch64-asm", feature = "x86_64-asm"))]
use std::env;

fn main() {
    println!("cargo:rerun-if-changed=src/asm/pasta_mul-armv8.S");
    println!("cargo:rerun-if-changed=src/asm/pasta_mulx-x86_64-coff.s");
    println!("cargo:rerun-if-changed=src/asm/pasta_mulx-x86_64-elf.s");
    println!("cargo:rerun-if-changed=src/asm/pasta_mulx-x86_64-macosx.s");
    println!("cargo:rerun-if-changed=src/asm/pasta_mulx-x86_64-win64.asm");

    #[cfg(feature = "aarch64-asm")]
    build_aarch64_asm();

    #[cfg(feature = "x86_64-asm")]
    build_x86_64_asm();
}

#[cfg(feature = "x86_64-asm")]
fn build_x86_64_asm() {
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    if target_arch != "x86_64" {
        return;
    }

    let target_env = env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();
    let target_family = env::var("CARGO_CFG_TARGET_FAMILY").unwrap_or_default();
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let target_vendor = env::var("CARGO_CFG_TARGET_VENDOR").unwrap_or_default();
    let source = if target_vendor == "apple" {
        "src/asm/pasta_mulx-x86_64-macosx.s"
    } else if target_os == "windows" && target_env == "msvc" {
        "src/asm/pasta_mulx-x86_64-win64.asm"
    } else if target_os == "windows" {
        "src/asm/pasta_mulx-x86_64-coff.s"
    } else if target_family.split(',').any(|family| family == "unix") {
        "src/asm/pasta_mulx-x86_64-elf.s"
    } else {
        return;
    };

    cc::Build::new().file(source).compile("pasta_curves_x86_64");
}

#[cfg(feature = "aarch64-asm")]
fn build_aarch64_asm() {
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let target_vendor = env::var("CARGO_CFG_TARGET_VENDOR").unwrap();

    if target_arch == "aarch64" && target_vendor == "apple" {
        cc::Build::new()
            .file("src/asm/pasta_mul-armv8.S")
            .compile("pasta_curves_aarch64");
    }
}
