fn target_uses_adx(target_arch: &str, target_features: &str) -> bool {
    target_arch == "x86_64"
        && target_features
            .split(',')
            .any(|feature| feature == "adx")
}

fn msvc_multiplication_assembly(target_arch: &str, use_adx: bool) -> &'static str {
    match (target_arch, use_adx) {
        ("x86_64", true) => "win64/pasta_mulx-x86_64.asm",
        ("x86_64", false) => "win64/pasta_mulq-x86_64.asm",
        ("aarch64", _) => "win64/pasta_mul-armv8.asm",
        _ => unreachable!("unsupported pasta-msm target architecture"),
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::{msvc_multiplication_assembly, target_uses_adx};

    fn assert_checked_in(source: &str) {
        let source = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("native/semolina")
            .join(source);

        assert!(source.is_file(), "missing {}", source.display());
    }

    #[test]
    fn msvc_x86_64_baseline_selects_mulq() {
        let use_adx = target_uses_adx("x86_64", "sse,sse2");

        assert!(!use_adx);
        assert_eq!(
            msvc_multiplication_assembly("x86_64", use_adx),
            "win64/pasta_mulq-x86_64.asm"
        );
        assert_checked_in(msvc_multiplication_assembly("x86_64", use_adx));
    }

    #[test]
    fn msvc_x86_64_adx_selects_mulx() {
        let use_adx = target_uses_adx("x86_64", "adx,sse,sse2");

        assert!(use_adx);
        assert_eq!(
            msvc_multiplication_assembly("x86_64", use_adx),
            "win64/pasta_mulx-x86_64.asm"
        );
        assert_checked_in(msvc_multiplication_assembly("x86_64", use_adx));
    }
}
