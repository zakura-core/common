#[cfg(feature = "aarch64-asm")]
use std::env;

fn main() {
    println!("cargo:rerun-if-changed=src/asm/pasta_mul-armv8.S");

    #[cfg(feature = "aarch64-asm")]
    build_aarch64_asm();
}

#[cfg(feature = "aarch64-asm")]
fn build_aarch64_asm() {
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").ok();
    let target_endian = env::var("CARGO_CFG_TARGET_ENDIAN").ok();
    let target_family = env::var("CARGO_CFG_TARGET_FAMILY").ok();
    let target_os = env::var("CARGO_CFG_TARGET_OS").ok();
    let target_pointer_width = env::var("CARGO_CFG_TARGET_POINTER_WIDTH").ok();

    if target_arch.as_deref() == Some("aarch64")
        && target_endian.as_deref() == Some("little")
        && (target_family.as_deref() == Some("unix") || target_os.as_deref() == Some("none"))
        && target_pointer_width.as_deref() == Some("64")
    {
        cc::Build::new()
            .file("src/asm/pasta_mul-armv8.S")
            .compile("pasta_curves_aarch64");
    }
}
