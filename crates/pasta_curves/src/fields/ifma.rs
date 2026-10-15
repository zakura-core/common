//! Batched field multiplication using AVX-512 IFMA (`vpmadd52{lo,hi}uq`).
//!
//! Field elements are transposed into a limb-sliced radix-52 representation
//! (five 52-bit limbs per element, eight elements per vector register) and
//! multiplied with a radix-52 Montgomery reduction using `R = 2^260`. The
//! right-hand operand is pre-scaled by `2^4` so a single reduction maps the
//! product back into the canonical `R = 2^256` Montgomery domain used by the
//! scalar representation.

use core::arch::x86_64::*;

#[cfg(any(
    test,
    feature = "multicore",
    feature = "orbits",
    feature = "sqrt-table"
))]
mod packed;

const LIMBS: usize = 5;
const RADIX: u32 = 52;
const MASK52: u64 = (1u64 << RADIX) - 1;
/// Bits by which `R = 2^260` exceeds the scalar Montgomery radix `2^256`.
const RADIX_GAP: u32 = 4;
/// Carry from a radix-52 limb shifted left by the Montgomery radix gap.
const CARRY_SHIFT: u32 = RADIX - RADIX_GAP;
/// Bit position of Pasta's leading modulus term in the top radix-52 limb.
const TOP_MODULUS_LIMB_SHIFT: u32 = 254 - (LIMBS as u32 - 1) * RADIX;
const XSAVE_OSXSAVE_AVX: u32 = (1 << 26) | (1 << 27) | (1 << 28);
const REQUIRED_XCR0: u64 = (1 << 1) | (1 << 2) | (1 << 5) | (1 << 6) | (1 << 7);
const AVX512_F_IFMA_VL: u32 = (1 << 16) | (1 << 21) | (1 << 31);

fn supports_ifma(leaf1_ecx: u32, leaf7_ebx: u32, xcr0: u64) -> bool {
    leaf1_ecx & XSAVE_OSXSAVE_AVX == XSAVE_OSXSAVE_AVX
        && leaf7_ebx & AVX512_F_IFMA_VL == AVX512_F_IFMA_VL
        && xcr0 & REQUIRED_XCR0 == REQUIRED_XCR0
}

/// Modulus and Montgomery constant for one field, in radix-52 form.
struct Radix52Modulus {
    /// The modulus in five 52-bit limbs, little-endian.
    p52: [u64; LIMBS],
    /// `-p^{-1} mod 2^52`.
    nprime: u64,
}

/// Returns whether the CPU and operating system support the IFMA path.
///
/// Unlike the standard-library detector, this also works in a `no_std` build.
fn ifma_available() -> bool {
    use core::sync::atomic::{AtomicU8, Ordering};

    static AVAILABLE: AtomicU8 = AtomicU8::new(0);
    let cached = AVAILABLE.load(Ordering::Relaxed);
    if cached != 0 {
        return cached == 2;
    }

    // SAFETY: CPUID is always available on x86-64. XGETBV is executed only
    // after CPUID confirms that the OS has enabled XSAVE support.
    let available = unsafe {
        let max_leaf = __cpuid(0).eax;
        let leaf1 = __cpuid(1);
        if max_leaf < 7 || leaf1.ecx & XSAVE_OSXSAVE_AVX != XSAVE_OSXSAVE_AVX {
            false
        } else {
            let leaf7 = __cpuid_count(7, 0);
            supports_ifma(leaf1.ecx, leaf7.ebx, _xgetbv(0))
        }
    };
    AVAILABLE.store(if available { 2 } else { 1 }, Ordering::Relaxed);
    available
}

/// Transposes 8 contiguous 4x64 elements into 4 limb-sliced vectors.
#[target_feature(enable = "avx512f")]
unsafe fn load_transpose8x4(ptr: *const u64) -> [__m512i; 4] {
    unsafe {
        let r0 = _mm512_loadu_si512(ptr as *const _);
        let r1 = _mm512_loadu_si512(ptr.add(8) as *const _);
        let r2 = _mm512_loadu_si512(ptr.add(16) as *const _);
        let r3 = _mm512_loadu_si512(ptr.add(24) as *const _);
        let merge = _mm512_set_epi64(11, 10, 9, 8, 3, 2, 1, 0);
        core::array::from_fn(|j| {
            let j = j as i64;
            let idx = _mm512_set_epi64(0, 0, 0, 0, j + 12, j + 8, j + 4, j);
            let lo = _mm512_permutex2var_epi64(r0, idx, r1);
            let hi = _mm512_permutex2var_epi64(r2, idx, r3);
            _mm512_permutex2var_epi64(lo, merge, hi)
        })
    }
}

/// Inverse of [`load_transpose8x4`].
#[target_feature(enable = "avx512f")]
unsafe fn store_transpose4x8(limbs: &[__m512i; 4], ptr: *mut u64) {
    unsafe {
        let mut lanes = [[0u64; 8]; 4];
        for (j, lane) in lanes.iter_mut().enumerate() {
            _mm512_storeu_si512(lane.as_mut_ptr() as *mut _, limbs[j]);
        }
        for e in 0..8 {
            for (j, lane) in lanes.iter().enumerate() {
                *ptr.add(e * 4 + j) = lane[e];
            }
        }
    }
}

/// 4x64 -> 5x52 radix conversion.
#[target_feature(enable = "avx512f")]
fn to_radix52(x: &[__m512i; 4]) -> [__m512i; LIMBS] {
    let mask = _mm512_set1_epi64(MASK52 as i64);
    [
        _mm512_and_si512(x[0], mask),
        _mm512_and_si512(
            _mm512_or_si512(_mm512_srli_epi64(x[0], 52), _mm512_slli_epi64(x[1], 12)),
            mask,
        ),
        _mm512_and_si512(
            _mm512_or_si512(_mm512_srli_epi64(x[1], 40), _mm512_slli_epi64(x[2], 24)),
            mask,
        ),
        _mm512_and_si512(
            _mm512_or_si512(_mm512_srli_epi64(x[2], 28), _mm512_slli_epi64(x[3], 36)),
            mask,
        ),
        _mm512_srli_epi64(x[3], 16),
    ]
}

/// 5x52 -> 4x64 radix conversion.
#[target_feature(enable = "avx512f")]
fn from_radix52(x: &[__m512i; LIMBS]) -> [__m512i; 4] {
    [
        _mm512_or_si512(x[0], _mm512_slli_epi64(x[1], 52)),
        _mm512_or_si512(_mm512_srli_epi64(x[1], 12), _mm512_slli_epi64(x[2], 40)),
        _mm512_or_si512(_mm512_srli_epi64(x[2], 24), _mm512_slli_epi64(x[3], 28)),
        _mm512_or_si512(_mm512_srli_epi64(x[3], 36), _mm512_slli_epi64(x[4], 16)),
    ]
}

/// Multiplies by `2^RADIX_GAP` in radix-52 (exact: inputs are < p < 2^255).
#[target_feature(enable = "avx512f")]
fn shl_radix_gap(x: &[__m512i; LIMBS]) -> [__m512i; LIMBS] {
    let mask = _mm512_set1_epi64(MASK52 as i64);
    core::array::from_fn(|j| {
        let hi = _mm512_slli_epi64(x[j], RADIX_GAP);
        if j == 0 {
            _mm512_and_si512(hi, mask)
        } else {
            _mm512_and_si512(
                _mm512_or_si512(hi, _mm512_srli_epi64(x[j - 1], CARRY_SHIFT)),
                mask,
            )
        }
    })
}

/// Canonicalizes a radix-52 value in `[0, 2p)` by conditionally subtracting p.
#[target_feature(enable = "avx512f")]
fn cond_sub_p(x: &[__m512i; LIMBS], modulus: &Radix52Modulus) -> [__m512i; LIMBS] {
    let mask = _mm512_set1_epi64(MASK52 as i64);
    let mut d = [_mm512_setzero_si512(); LIMBS];
    let mut borrow = _mm512_setzero_si512();
    for j in 0..LIMBS {
        let pj = _mm512_set1_epi64(modulus.p52[j] as i64);
        let t = _mm512_sub_epi64(_mm512_sub_epi64(x[j], pj), borrow);
        d[j] = _mm512_and_si512(t, mask);
        borrow = _mm512_srli_epi64(t, 63);
    }
    // A final borrow means x < p: keep x; otherwise use the difference.
    let keep = _mm512_test_epi64_mask(borrow, borrow);
    core::array::from_fn(|j| _mm512_mask_blend_epi64(keep, d[j], x[j]))
}

/// 8-way radix-52 Montgomery multiplication with `R = 2^260`.
///
/// Inputs have normalized 52-bit limbs and either `a < p, b < 16p`
/// (scalar-domain adapters) or `a < 2p, b < 2p` (private native scratch).
/// Since `p < 2^255`, the respective output bounds are `3p/2` and `9p/8`.
/// The result has normalized 52-bit limbs; one conditional subtraction
/// produces a canonical residue when the caller requires one.
///
/// Each round adds at most four 52-bit low/high contributions to any
/// accumulator. Across five rounds, including lowest-limb carries, a
/// conservative bound is `20 * 2^52 + 65 < 2^57`, below the 64-bit wrap.
/// Both supported Pasta moduli have `p52[3] = 0` and a power-of-two top
/// limb. This fixed-shape kernel accepts only those moduli.
#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
fn mont_mul8(
    a: &[__m512i; LIMBS],
    b: &[__m512i; LIMBS],
    modulus: &Radix52Modulus,
) -> [__m512i; LIMBS] {
    debug_assert_eq!(modulus.p52[3], 0);
    debug_assert_eq!(modulus.p52[4], 1 << TOP_MODULUS_LIMB_SHIFT);
    let zero = _mm512_setzero_si512();
    let mask52 = _mm512_set1_epi64(MASK52 as i64);
    let nprime = _mm512_set1_epi64(modulus.nprime as i64);
    let p: [__m512i; LIMBS] = core::array::from_fn(|j| _mm512_set1_epi64(modulus.p52[j] as i64));

    // Keep each accumulator explicit to avoid indexed-window stack spills.
    let (mut acc0, mut acc1, mut acc2, mut acc3, mut acc4, mut acc5) =
        (zero, zero, zero, zero, zero, zero);
    macro_rules! accumulate {
        ($lhs:expr, $rhs:expr, $lo:ident, $hi:ident) => {
            $lo = _mm512_madd52lo_epu64($lo, $lhs, $rhs);
            $hi = _mm512_madd52hi_epu64($hi, $lhs, $rhs);
        };
    }
    for ai in *a {
        accumulate!(ai, b[0], acc0, acc1);
        accumulate!(ai, b[1], acc1, acc2);
        accumulate!(ai, b[2], acc2, acc3);
        accumulate!(ai, b[3], acc3, acc4);
        accumulate!(ai, b[4], acc4, acc5);
        let m = _mm512_and_si512(_mm512_madd52lo_epu64(zero, acc0, nprime), mask52);
        accumulate!(m, p[0], acc0, acc1);
        accumulate!(m, p[1], acc1, acc2);
        accumulate!(m, p[2], acc2, acc3);
        // The fourth modulus limb is zero. The top limb is a power of two:
        // shifting its product splits exactly at the radix-52 boundary.
        let low = _mm512_and_si512(_mm512_slli_epi64(m, TOP_MODULUS_LIMB_SHIFT), mask52);
        let high = _mm512_srli_epi64(m, RADIX - TOP_MODULUS_LIMB_SHIFT);
        acc4 = _mm512_add_epi64(acc4, low);
        acc5 = _mm512_add_epi64(acc5, high);
        // The lowest limb is divisible by 2^52; carry it up and shift.
        acc0 = _mm512_add_epi64(acc1, _mm512_srli_epi64(acc0, RADIX));
        acc1 = acc2;
        acc2 = acc3;
        acc3 = acc4;
        acc4 = acc5;
        acc5 = zero;
    }
    let t1 = _mm512_add_epi64(acc1, _mm512_srli_epi64(acc0, RADIX));
    let t2 = _mm512_add_epi64(acc2, _mm512_srli_epi64(t1, RADIX));
    let t3 = _mm512_add_epi64(acc3, _mm512_srli_epi64(t2, RADIX));
    let t4 = _mm512_add_epi64(acc4, _mm512_srli_epi64(t3, RADIX));
    [acc0, t1, t2, t3, t4].map(|limb| _mm512_and_si512(limb, mask52))
}

/// Elementwise `lhs[i] *= rhs[i]` over canonical 4x64 Montgomery elements.
///
/// # Safety
///
/// Requires AVX-512F/IFMA/VL. `lhs` and `rhs` must be slices of
/// `#[repr(transparent)]` wrappers around `[u64; 4]` canonical Montgomery
/// residues, with `rhs.len() >= lhs.len()`.
#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
unsafe fn mul_slice_raw(
    lhs: *mut u64,
    rhs: *const u64,
    len: usize,
    modulus: &Radix52Modulus,
) -> usize {
    unsafe {
        let n8 = len / 8;
        for i in 0..n8 {
            let a = to_radix52(&load_transpose8x4(lhs.add(i * 32)));
            let b = shl_radix_gap(&to_radix52(&load_transpose8x4(rhs.add(i * 32))));
            let c = mont_mul8(&a, &b, modulus);
            let c = cond_sub_p(&c, modulus);
            store_transpose4x8(&from_radix52(&c), lhs.add(i * 32));
        }
        n8 * 8
    }
}

/// Elementwise `x[i] = x[i]^2` over canonical 4x64 Montgomery elements.
///
/// # Safety
///
/// Same requirements as [`mul_slice_raw`].
#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
unsafe fn sqr_slice_raw(x: *mut u64, len: usize, modulus: &Radix52Modulus) -> usize {
    unsafe {
        let n8 = len / 8;
        for i in 0..n8 {
            let a = to_radix52(&load_transpose8x4(x.add(i * 32)));
            let b = shl_radix_gap(&a);
            let c = mont_mul8(&a, &b, modulus);
            let c = cond_sub_p(&c, modulus);
            store_transpose4x8(&from_radix52(&c), x.add(i * 32));
        }
        n8 * 8
    }
}

/// Selects a modulus only for the two concrete transparent Pasta field types.
fn modulus<F: ff::Field>() -> Option<&'static Radix52Modulus> {
    use core::any::TypeId;

    const FP: Radix52Modulus = Radix52Modulus {
        p52: [
            0xd30ed00000001,
            0xfc094cf91b992,
            0x224698,
            0,
            0x400000000000,
        ],
        nprime: 0xd30ecffffffff,
    };
    const FQ: Radix52Modulus = Radix52Modulus {
        p52: [
            0x6eb2100000001,
            0xfc0994a8dd8c4,
            0x224698,
            0,
            0x400000000000,
        ],
        nprime: 0x6eb20ffffffff,
    };

    if TypeId::of::<F>() == TypeId::of::<super::Fp>() {
        Some(&FP)
    } else if TypeId::of::<F>() == TypeId::of::<super::Fq>() {
        Some(&FQ)
    } else {
        None
    }
}

/// Whether IFMA is available for this concrete field type.
pub(super) fn available_for<F: ff::Field>() -> bool {
    modulus::<F>().is_some() && ifma_available()
}

/// Multiplies eight field elements after checked concrete-type dispatch.
pub(super) fn mul8<F: ff::Field>(lhs: &mut [F; 8], rhs: &[F; 8]) {
    let modulus = modulus::<F>().expect("IFMA requires a concrete Pasta field");
    assert!(ifma_available());
    // SAFETY: the TypeId check above proves that F is Fp or Fq. Both are
    // transparent [u64; 4] wrappers, and safe field operations preserve
    // canonical Montgomery residues. All eight elements are in bounds and
    // the required CPU and OS features were checked.
    unsafe {
        mul_slice_raw(
            lhs.as_mut_ptr().cast(),
            rhs.as_ptr().cast(),
            lhs.len(),
            modulus,
        );
    }
}

/// Squares eight field elements after checked concrete-type dispatch.
pub(super) fn square8<F: ff::Field>(values: &mut [F; 8]) {
    let modulus = modulus::<F>().expect("IFMA requires a concrete Pasta field");
    assert!(ifma_available());
    // SAFETY: the same concrete-type, representation, and CPU checks as mul8.
    unsafe {
        sqr_slice_raw(values.as_mut_ptr().cast(), values.len(), modulus);
    }
}

/// Computes the square-root exponent in private native-radix scratch.
#[cfg(feature = "sqrt-table")]
pub(super) fn pow_t8<F: ff::Field>(values: &[F; 8]) -> [F; 8] {
    let modulus = modulus::<F>().expect("IFMA requires a concrete Pasta field");
    assert!(ifma_available());
    // SAFETY: the concrete field dispatch and CPU/OS gate establish the
    // backend's representation, modulus, and instruction requirements.
    unsafe { packed::pow_t8(values, modulus) }
}

/// Reduces buckets after exact-field and CPU dispatch, in private scratch.
#[cfg(any(test, feature = "multicore", feature = "orbits"))]
pub(super) fn reduce_affine_buckets<F: ff::Field>(
    point_count: usize,
    offsets: &[usize],
    point_at: impl Fn(usize) -> (F, F),
) -> Option<alloc::vec::Vec<Option<(F, F)>>> {
    let modulus = modulus::<F>()?;
    if !ifma_available()
        || offsets.first() != Some(&0)
        || offsets.last() != Some(&point_count)
        || offsets.windows(2).any(|range| range[0] > range[1])
    {
        return None;
    }
    // SAFETY: exact TypeId dispatch proves the transparent Pasta field
    // representation, and the CPU gate covers all enabled target features.
    // The validated offsets partition the closure's point indices.
    unsafe { packed::reduce(point_count, offsets, point_at, modulus) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn modulus_words(modulus: &Radix52Modulus) -> [u64; 4] {
        let p = modulus.p52;
        [
            p[0] | (p[1] << 52),
            (p[1] >> 12) | (p[2] << 40),
            (p[2] >> 24) | (p[3] << 28),
            (p[3] >> 36) | (p[4] << 16),
        ]
    }

    fn check_modulus<F: ff::PrimeField>() {
        let modulus = modulus::<F>().unwrap();
        let p = modulus.p52;
        let reconstructed = modulus_words(modulus);
        let minus_one = (-F::ONE).to_repr();
        let bytes = minus_one.as_ref();
        assert_eq!(bytes.len(), core::mem::size_of_val(&reconstructed));
        let mut expected = core::array::from_fn::<_, 4, _>(|limb| {
            u64::from_le_bytes(bytes[limb * 8..(limb + 1) * 8].try_into().unwrap())
        });
        for limb in &mut expected {
            let (value, carry) = limb.overflowing_add(1);
            *limb = value;
            if !carry {
                break;
            }
        }
        assert_eq!(reconstructed, expected);
        assert!(p.iter().all(|limb| *limb <= MASK52));
        assert_eq!(p[3], 0, "the fixed-shape kernel omits this reduction term");
        assert_eq!(p[4], 1 << TOP_MODULUS_LIMB_SHIFT);
        assert_eq!(p[0].wrapping_mul(modulus.nprime) & MASK52, MASK52);
    }

    #[test]
    fn ifma_radix52_constants_match_scalar_moduli() {
        check_modulus::<super::super::Fp>();
        check_modulus::<super::super::Fq>();
    }

    fn raw_boundary_words<F: ff::Field>() -> [[u64; 4]; 8] {
        let mut minus_one = modulus_words(modulus::<F>().unwrap());
        minus_one[0] -= 1;
        let mut minus_two = minus_one;
        for limb in &mut minus_two {
            let (value, borrow) = limb.overflowing_sub(1);
            *limb = value;
            if !borrow {
                break;
            }
        }
        [
            [0, 0, 0, 0],
            [1, 0, 0, 0],
            [u64::MAX, 0, 0, 0],
            [u64::MAX, u64::MAX, 0, 0],
            [u64::MAX, u64::MAX, u64::MAX, 0],
            [0, 0, 0, 1 << 62],
            minus_one,
            minus_two,
        ]
    }

    fn check_raw_boundaries<F: ff::Field>(values: [F; 8]) {
        if !available_for::<F>() {
            return;
        }
        for shift in 0..values.len() {
            let rhs = core::array::from_fn(|lane| values[(lane + shift) % values.len()]);
            let expected = core::array::from_fn(|lane| values[lane] * rhs[lane]);
            let mut actual = values;
            mul8(&mut actual, &rhs);
            assert_eq!(actual, expected);
        }
        let expected = values.map(|value| value.square());
        let mut actual = values;
        square8(&mut actual);
        assert_eq!(actual, expected);
    }

    #[test]
    fn ifma_raw_montgomery_boundaries_match_scalar() {
        // These are canonical internal residues, not ordinary integer inputs.
        // In particular p - 1 exercises the final conditional subtraction.
        check_raw_boundaries(raw_boundary_words::<super::super::Fp>().map(super::super::Fp));
        check_raw_boundaries(raw_boundary_words::<super::super::Fq>().map(super::super::Fq));
    }

    #[test]
    fn ifma_detection_requires_every_cpu_and_os_feature() {
        assert!(supports_ifma(
            XSAVE_OSXSAVE_AVX,
            AVX512_F_IFMA_VL,
            REQUIRED_XCR0,
        ));
        for bit in [26, 27, 28] {
            assert!(!supports_ifma(
                XSAVE_OSXSAVE_AVX & !(1 << bit),
                AVX512_F_IFMA_VL,
                REQUIRED_XCR0,
            ));
        }
        for bit in [16, 21, 31] {
            assert!(!supports_ifma(
                XSAVE_OSXSAVE_AVX,
                AVX512_F_IFMA_VL & !(1 << bit),
                REQUIRED_XCR0,
            ));
        }
        for bit in [1, 2, 5, 6, 7] {
            assert!(!supports_ifma(
                XSAVE_OSXSAVE_AVX,
                AVX512_F_IFMA_VL,
                REQUIRED_XCR0 & !(1 << bit),
            ));
        }
    }

    #[test]
    fn ifma_detection_matches_standard_library() {
        std::println!("IFMA engaged={}", ifma_available());
        assert_eq!(
            ifma_available(),
            std::arch::is_x86_feature_detected!("avx512f")
                && std::arch::is_x86_feature_detected!("avx512ifma")
                && std::arch::is_x86_feature_detected!("avx512vl"),
        );
    }
}
