//! CPU selection shared by the two Pasta field backends.

#[cfg(not(pasta_curves_x86_64_asm_static))]
use core::sync::atomic::{AtomicU8, Ordering};

#[cfg(not(pasta_curves_x86_64_asm_static))]
const UNKNOWN: u8 = 0;
#[cfg(not(pasta_curves_x86_64_asm_static))]
const UNAVAILABLE: u8 = 1;
#[cfg(not(pasta_curves_x86_64_asm_static))]
const AVAILABLE: u8 = 2;
#[cfg(not(pasta_curves_x86_64_asm_static))]
static STATE: AtomicU8 = AtomicU8::new(UNKNOWN);

#[cfg(all(test, not(pasta_curves_x86_64_asm_static)))]
std::thread_local! {
    static FORCE_PORTABLE: core::cell::Cell<bool> = const {
        core::cell::Cell::new(false)
    };
}

/// Whether the caller may execute the BMI2+ADX field backend.
#[inline(always)]
pub(super) fn asm_available() -> bool {
    #[cfg(pasta_curves_x86_64_asm_static)]
    {
        true
    }
    #[cfg(not(pasta_curves_x86_64_asm_static))]
    {
        #[cfg(test)]
        if FORCE_PORTABLE.get() {
            return false;
        }

        match STATE.load(Ordering::Relaxed) {
            AVAILABLE => true,
            UNAVAILABLE => false,
            _ => detect_and_cache(),
        }
    }
}

#[cfg(not(pasta_curves_x86_64_asm_static))]
#[cold]
#[inline(never)]
fn detect_and_cache() -> bool {
    use core::arch::x86_64::{__cpuid, __cpuid_count};

    const STRUCTURED_FEATURES_LEAF: u32 = 7;
    const BMI2_AND_ADX: u32 = (1 << 8) | (1 << 19);

    // CPUID is available on x86-64. Check the maximum basic leaf before
    // querying structured features. BMI2 and ADX use general-purpose
    // registers, so no operating-system extended-state support is needed.
    let available = if cfg!(target_env = "sgx") {
        // CPUID cannot be executed inside an SGX enclave.
        false
    } else {
        __cpuid(0).eax >= STRUCTURED_FEATURES_LEAF
            && __cpuid_count(STRUCTURED_FEATURES_LEAF, 0).ebx & BMI2_AND_ADX == BMI2_AND_ADX
    };
    // The cache publishes only a CPU capability, not any associated data.
    // Concurrent initial detections may repeat CPUID and store the same value.
    STATE.store(
        if available { AVAILABLE } else { UNAVAILABLE },
        Ordering::Relaxed,
    );
    available
}

/// Forces fallback only on this test thread, restoring it even after a panic.
#[cfg(all(test, not(pasta_curves_x86_64_asm_static)))]
pub(super) fn with_portable_backend(f: impl FnOnce()) {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            FORCE_PORTABLE.set(self.0);
        }
    }

    let _restore = Restore(FORCE_PORTABLE.replace(true));
    f();
}

#[cfg(test)]
#[test]
fn selected_backend_matches_cpu_features() {
    #[cfg(pasta_curves_x86_64_asm_static)]
    assert!(asm_available());

    #[cfg(not(pasta_curves_x86_64_asm_static))]
    {
        let expected =
            std::is_x86_feature_detected!("bmi2") && std::is_x86_feature_detected!("adx");
        // Both the first access and the cached access must agree with std.
        assert_eq!(asm_available(), expected);
        assert_eq!(asm_available(), expected);
    }
}

#[cfg(all(test, not(pasta_curves_x86_64_asm_static)))]
#[test]
fn forced_fallback_is_scoped_and_thread_local() {
    let expected = asm_available();
    with_portable_backend(|| {
        assert!(!asm_available());
        with_portable_backend(|| assert!(!asm_available()));
        assert!(!asm_available());
        assert_eq!(std::thread::spawn(asm_available).join().unwrap(), expected);
    });
    assert_eq!(asm_available(), expected);

    let _ = std::panic::catch_unwind(|| {
        with_portable_backend(|| panic!("test restoration"));
    });
    assert_eq!(asm_available(), expected);
}
