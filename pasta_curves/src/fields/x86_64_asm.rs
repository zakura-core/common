//! Private bindings to the x86_64 Pasta field backend.

#[cfg(not(all(target_feature = "adx", target_feature = "bmi2")))]
use core::sync::atomic::{AtomicU8, Ordering};

#[cfg(not(all(target_feature = "adx", target_feature = "bmi2")))]
use core::arch::x86_64::{__cpuid, __cpuid_count};

type Limbs = [u64; 4];

#[cfg(not(all(target_feature = "adx", target_feature = "bmi2")))]
const FEATURE_UNKNOWN: u8 = 0;
#[cfg(not(all(target_feature = "adx", target_feature = "bmi2")))]
const FEATURE_UNAVAILABLE: u8 = 1;
#[cfg(not(all(target_feature = "adx", target_feature = "bmi2")))]
const FEATURE_AVAILABLE: u8 = 2;
#[cfg(not(all(target_feature = "adx", target_feature = "bmi2")))]
const CPUID_BMI2: u32 = 1 << 8;
#[cfg(not(all(target_feature = "adx", target_feature = "bmi2")))]
const CPUID_ADX: u32 = 1 << 19;

#[cfg(not(all(target_feature = "adx", target_feature = "bmi2")))]
static ADX_AVAILABLE: AtomicU8 = AtomicU8::new(FEATURE_UNKNOWN);

extern "C" {
    fn pasta_curves_mulx_mont(
        out: *mut Limbs,
        lhs: *const Limbs,
        rhs: *const Limbs,
        modulus: *const Limbs,
        inv: u64,
    );
    fn pasta_curves_sqrx_mont(
        out: *mut Limbs,
        value: *const Limbs,
        modulus: *const Limbs,
        inv: u64,
    );
    #[cfg(target_os = "linux")]
    fn pasta_curves_sqr_n_mulx_mont(
        out: *mut Limbs,
        value: *const Limbs,
        n: usize,
        rhs: *const Limbs,
        modulus: *const Limbs,
        inv: u64,
    );
}

#[cfg(all(target_feature = "adx", target_feature = "bmi2"))]
#[inline(always)]
fn adx_available() -> bool {
    true
}

#[cfg(not(all(target_feature = "adx", target_feature = "bmi2")))]
#[inline]
fn adx_available() -> bool {
    match ADX_AVAILABLE.load(Ordering::Relaxed) {
        FEATURE_UNAVAILABLE => false,
        FEATURE_AVAILABLE => true,
        _ => {
            // SAFETY: CPUID is available on every x86_64 CPU. The maximum
            // supported leaf is checked before querying structured features.
            let available = unsafe {
                __cpuid(0).eax >= 7 && {
                    let features = __cpuid_count(7, 0).ebx;
                    features & (CPUID_BMI2 | CPUID_ADX) == (CPUID_BMI2 | CPUID_ADX)
                }
            };
            ADX_AVAILABLE.store(
                if available {
                    FEATURE_AVAILABLE
                } else {
                    FEATURE_UNAVAILABLE
                },
                Ordering::Relaxed,
            );
            available
        }
    }
}

/// Multiplies two canonical Montgomery residues when BMI2 and ADX are
/// available, or returns `None` to select the portable implementation.
///
/// Both moduli must have limb 2 equal to zero and limb 3 equal to $2^{62}$,
/// and `inv` must equal the modulus's Montgomery inverse.
#[inline]
pub(super) fn mul(lhs: &Limbs, rhs: &Limbs, modulus: &Limbs, inv: u64) -> Option<Limbs> {
    if !adx_available() {
        return None;
    }

    let mut out = Limbs::default();
    // SAFETY: Feature detection above establishes the BMI2 and ADX
    // preconditions. All pointers refer to four initialized `u64` limbs for
    // the duration of the call, and the backend writes four limbs to `out`.
    unsafe {
        pasta_curves_mulx_mont(&mut out, lhs, rhs, modulus, inv);
    }
    Some(out)
}

/// Squares a canonical Montgomery residue when BMI2 and ADX are available,
/// or returns `None` to select the portable implementation.
///
/// The modulus must have limb 2 equal to zero and limb 3 equal to $2^{62}$,
/// and `inv` must equal its Montgomery inverse.
#[inline]
pub(super) fn square(value: &Limbs, modulus: &Limbs, inv: u64) -> Option<Limbs> {
    if !adx_available() {
        return None;
    }

    let mut out = Limbs::default();
    // SAFETY: Feature detection above establishes the BMI2 and ADX
    // preconditions. All pointers refer to four initialized `u64` limbs for
    // the duration of the call, and the backend writes four limbs to `out`.
    unsafe {
        pasta_curves_sqrx_mont(&mut out, value, modulus, inv);
    }
    Some(out)
}

/// Squares a canonical Montgomery residue `n` times, then multiplies by
/// `rhs`, when the fused BMI2/ADX backend is available.
///
/// Both moduli must have limb 2 equal to zero and limb 3 equal to $2^{62}$,
/// and `inv` must equal the modulus's Montgomery inverse.
pub(super) fn sqr_n_mul(
    value: &Limbs,
    n: usize,
    rhs: &Limbs,
    modulus: &Limbs,
    inv: u64,
) -> Option<Limbs> {
    debug_assert!(n >= 1);

    #[cfg(target_os = "linux")]
    {
        if !adx_available() {
            return None;
        }

        let mut out = Limbs::default();
        // SAFETY: Feature detection above establishes the BMI2 and ADX
        // preconditions. All pointers refer to four initialized `u64` limbs
        // for the duration of the call, and the backend writes four limbs.
        unsafe {
            pasta_curves_sqr_n_mulx_mont(&mut out, value, n, rhs, modulus, inv);
        }
        Some(out)
    }

    #[cfg(not(target_os = "linux"))]
    {
        let _ = (value, n, rhs, modulus, inv);
        None
    }
}

#[cfg(test)]
pub(super) fn is_available() -> bool {
    adx_available()
}
