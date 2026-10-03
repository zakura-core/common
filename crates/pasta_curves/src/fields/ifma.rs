//! Batched field multiplication using AVX-512 IFMA (`vpmadd52{lo,hi}uq`).
//!
//! Field elements are transposed into a limb-sliced radix-52 representation
//! (five 52-bit limbs per element, eight elements per vector register) and
//! multiplied with a radix-52 Montgomery reduction using `R = 2^260`. The
//! right-hand operand is pre-scaled by `2^4` so a single reduction maps the
//! product back into the canonical `R = 2^256` Montgomery domain used by the
//! scalar representation.

use core::arch::x86_64::*;

const LIMBS: usize = 5;
const RADIX: u32 = 52;
const MASK52: u64 = (1u64 << RADIX) - 1;
/// Bits by which `R = 2^260` exceeds the scalar Montgomery radix `2^256`.
const RADIX_GAP: u32 = 4;
/// Bits of each 64-bit limb consumed by the next radix-52 limb.
const CARRY_SHIFT: u32 = 64 - RADIX_GAP * 4;

/// Modulus and Montgomery constant for one field, in radix-52 form.
pub(crate) struct Radix52Modulus {
    /// The modulus in five 52-bit limbs, little-endian.
    pub p52: [u64; LIMBS],
    /// `-p^{-1} mod 2^52`.
    pub nprime: u64,
}

/// Returns whether the batched IFMA path is usable on this CPU.
#[inline]
pub(crate) fn ifma_available() -> bool {
    std::arch::is_x86_feature_detected!("avx512ifma")
        && std::arch::is_x86_feature_detected!("avx512vl")
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
/// Inputs must have 52-bit limbs with combined values below `p * 2^RADIX_GAP`;
/// the output is below `2p` with 52-bit limbs.
#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
fn mont_mul8(
    a: &[__m512i; LIMBS],
    b: &[__m512i; LIMBS],
    modulus: &Radix52Modulus,
) -> [__m512i; LIMBS] {
    let zero = _mm512_setzero_si512();
    let mask52 = _mm512_set1_epi64(MASK52 as i64);
    let nprime = _mm512_set1_epi64(modulus.nprime as i64);
    let p: [__m512i; LIMBS] = core::array::from_fn(|j| _mm512_set1_epi64(modulus.p52[j] as i64));

    let mut acc = [zero; LIMBS + 1];
    for ai in *a {
        for j in 0..LIMBS {
            acc[j] = _mm512_madd52lo_epu64(acc[j], ai, b[j]);
            acc[j + 1] = _mm512_madd52hi_epu64(acc[j + 1], ai, b[j]);
        }
        let m = _mm512_and_si512(_mm512_madd52lo_epu64(zero, acc[0], nprime), mask52);
        for j in 0..LIMBS {
            acc[j] = _mm512_madd52lo_epu64(acc[j], m, p[j]);
            acc[j + 1] = _mm512_madd52hi_epu64(acc[j + 1], m, p[j]);
        }
        // acc[0] is now divisible by 2^52; carry it up and shift the window.
        let carry = _mm512_srli_epi64(acc[0], RADIX);
        acc[1] = _mm512_add_epi64(acc[1], carry);
        for j in 0..LIMBS {
            acc[j] = acc[j + 1];
        }
        acc[LIMBS] = zero;
    }

    let mut out = [zero; LIMBS];
    let mut carry = zero;
    for j in 0..LIMBS {
        let t = _mm512_add_epi64(acc[j], carry);
        out[j] = _mm512_and_si512(t, mask52);
        carry = _mm512_srli_epi64(t, RADIX);
    }
    out
}

/// Elementwise `lhs[i] *= rhs[i]` over canonical 4x64 Montgomery elements.
///
/// # Safety
///
/// Requires AVX-512F/IFMA/VL. `lhs` and `rhs` must be slices of
/// `#[repr(transparent)]` wrappers around `[u64; 4]` canonical Montgomery
/// residues, with `rhs.len() >= lhs.len()`.
#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
pub(crate) unsafe fn mul_slice_raw(
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

/// Broadcasts one canonical 4x64 element into radix-52 limb vectors.
#[target_feature(enable = "avx512f")]
fn radix52_broadcast(k: &[u64; 4]) -> [__m512i; LIMBS] {
    let l = [
        k[0] & MASK52,
        ((k[0] >> 52) | (k[1] << 12)) & MASK52,
        ((k[1] >> 40) | (k[2] << 24)) & MASK52,
        ((k[2] >> 28) | (k[3] << 36)) & MASK52,
        k[3] >> 16,
    ];
    core::array::from_fn(|j| _mm512_set1_epi64(l[j] as i64))
}

/// Elementwise `x[i] *= k` over canonical 4x64 Montgomery elements.
///
/// # Safety
///
/// Same requirements as [`mul_slice_raw`], with `k` a canonical Montgomery
/// residue.
#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
pub(crate) unsafe fn scale_slice_raw(
    x: *mut u64,
    len: usize,
    k: &[u64; 4],
    modulus: &Radix52Modulus,
) -> usize {
    unsafe {
        let b = shl_radix_gap(&radix52_broadcast(k));
        let n8 = len / 8;
        for i in 0..n8 {
            let a = to_radix52(&load_transpose8x4(x.add(i * 32)));
            let c = mont_mul8(&a, &b, modulus);
            let c = cond_sub_p(&c, modulus);
            store_transpose4x8(&from_radix52(&c), x.add(i * 32));
        }
        n8 * 8
    }
}

/// Accumulator limbs for the unreduced dot-product kernel: ten radix-52
/// product positions plus one limb for normalization carries.
#[cfg(feature = "deferred")]
const DOT_LIMBS: usize = 2 * LIMBS + 1;

/// Batches between carry normalizations. Each batch adds at most ten 52-bit
/// terms per accumulator limb, so `256 * 10 * 2^52 + 2^52 < 2^64` holds and
/// no lane can overflow within a block.
#[cfg(feature = "deferred")]
const DOT_NORM_INTERVAL: usize = 256;

/// Propagates each accumulator lane's bits above 52 into the next limb.
#[cfg(feature = "deferred")]
#[target_feature(enable = "avx512f")]
fn dot_normalize(acc: &mut [__m512i; DOT_LIMBS]) {
    let mask = _mm512_set1_epi64(MASK52 as i64);
    let mut carry = _mm512_setzero_si512();
    for limb in acc.iter_mut().take(DOT_LIMBS - 1) {
        let t = _mm512_add_epi64(*limb, carry);
        *limb = _mm512_and_si512(t, mask);
        carry = _mm512_srli_epi64(t, RADIX);
    }
    // The top limb only ever holds normalization carries; keep it unmasked.
    acc[DOT_LIMBS - 1] = _mm512_add_epi64(acc[DOT_LIMBS - 1], carry);
}

/// Accumulates `sum_i a[i] * b[i]` over canonical 4x64 elements as one
/// unreduced 576-bit integer, added into `sum` (nine base-2^64 limbs).
///
/// The integer value matches the scalar deferred accumulator exactly, so the
/// caller can finish with the existing partial/Montgomery reduction.
///
/// # Safety
///
/// Requires AVX-512F/IFMA/VL. `a` and `b` must each point to `len` contiguous
/// `[u64; 4]` values. `len` must not exceed `2^38` (so the folded carries fit
/// the top limb).
#[cfg(feature = "deferred")]
#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
pub(crate) unsafe fn dot_slice_raw(
    a: *const u64,
    b: *const u64,
    len: usize,
    sum: &mut [u64; 9],
) -> usize {
    let zero = _mm512_setzero_si512();
    let mut acc = [zero; DOT_LIMBS];
    let n8 = len / 8;
    let mut since_norm = 0;
    for i in 0..n8 {
        // SAFETY: `i * 32 + 32 <= len * 4` u64s are in bounds per the
        // contract above.
        let (av, bv) = unsafe {
            (
                to_radix52(&load_transpose8x4(a.add(i * 32))),
                to_radix52(&load_transpose8x4(b.add(i * 32))),
            )
        };
        for (j, aj) in av.iter().enumerate() {
            for (k, bk) in bv.iter().enumerate() {
                acc[j + k] = _mm512_madd52lo_epu64(acc[j + k], *aj, *bk);
                acc[j + k + 1] = _mm512_madd52hi_epu64(acc[j + k + 1], *aj, *bk);
            }
        }
        since_norm += 1;
        if since_norm == DOT_NORM_INTERVAL {
            dot_normalize(&mut acc);
            since_norm = 0;
        }
    }
    dot_normalize(&mut acc);

    // Horizontal sum: eight lanes per radix-52 limb, then base-52 to base-64.
    for (k, limb) in acc.iter().enumerate() {
        let mut lanes = [0u64; 8];
        // SAFETY: `lanes` is a valid 64-byte store target.
        unsafe {
            _mm512_storeu_si512(lanes.as_mut_ptr() as *mut _, *limb);
        }
        // Normalized lanes are below 2^52 (top limb: below 2^56), so the
        // eight-lane total stays below 2^59.
        let total: u64 = lanes.iter().sum();
        let bit = RADIX as usize * k;
        let (word, offset) = (bit / 64, bit % 64);
        let wide = (total as u128) << offset;
        let (lo, hi) = (wide as u64, (wide >> 64) as u64);
        let (s, overflow) = sum[word].overflowing_add(lo);
        sum[word] = s;
        let mut carry = hi as u128 + overflow as u128;
        let mut next = word + 1;
        while carry != 0 {
            let (s, overflow) = sum[next].overflowing_add(carry as u64);
            sum[next] = s;
            carry = (carry >> 64) + overflow as u128;
            next += 1;
        }
    }
    n8 * 8
}

/// Elementwise `x[i] = x[i]^2` over canonical 4x64 Montgomery elements.
///
/// # Safety
///
/// Same requirements as [`mul_slice_raw`].
#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
pub(crate) unsafe fn sqr_slice_raw(x: *mut u64, len: usize, modulus: &Radix52Modulus) -> usize {
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
