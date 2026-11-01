use std::env;

fn main() {
    println!("cargo:rustc-check-cfg=cfg(udon_aarch64_asm)");
    println!("cargo:rustc-check-cfg=cfg(udon_x86_64_asm)");
    println!("cargo:rustc-check-cfg=cfg(udon_asm)");
    println!("cargo:rerun-if-changed=src/asm/pasta_mul-armv8.S");

    let x86_64 = use_x86_64_asm();
    let aarch64 = build_aarch64_asm();
    if x86_64 {
        println!("cargo:rustc-cfg=udon_x86_64_asm");
    }
    // The umbrella cfg lets field kernels dispatch to whichever backend was
    // selected without naming the architecture.
    if x86_64 || aarch64 {
        println!("cargo:rustc-cfg=udon_asm");
    }
}

// Whether the x86-64 inline-assembly backend is selected for this build.
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

#[cfg(not(feature = "aarch64-asm"))]
fn build_aarch64_asm() -> bool {
    false
}

// Assembles the AArch64 routines and reports whether that backend is selected.
#[cfg(feature = "aarch64-asm")]
fn build_aarch64_asm() -> bool {
    let arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let endian = env::var("CARGO_CFG_TARGET_ENDIAN").unwrap();
    let family = env::var("CARGO_CFG_TARGET_FAMILY").unwrap_or_default();
    let os = env::var("CARGO_CFG_TARGET_OS").unwrap();
    let width = env::var("CARGO_CFG_TARGET_POINTER_WIDTH").unwrap();
    if arch == "aarch64"
        && endian == "little"
        && width == "64"
        && (family.split(',').any(|family| family == "unix") || os == "none")
    {
        cc::Build::new()
            .file("src/asm/pasta_mul-armv8.S")
            .compile("zakura_udon_aarch64");
        println!("cargo:rustc-cfg=udon_aarch64_asm");
        return true;
    }
    false
}
