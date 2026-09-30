//! Private lazy radix-52 scratch for affine reduction and batch decoding.
//!
//! Coordinates and numerator prefixes remain in the `R = 2^260` Montgomery
//! domain across every level. Only input coordinates, inversion endpoints,
//! and final bucket sums cross the scalar `R = 2^256` boundary. Hot scratch
//! residues are in `[0, 2p)`; canonical entry, inversion, and exit bridges
//! never expose lazy residues as scalar field values.

#[cfg(any(test, feature = "multicore", feature = "orbits"))]
use alloc::vec::Vec;

use super::*;

const LANES: usize = 8;
type Packed = [__m512i; LIMBS];

/// Coordinates are limb-major so contiguous output groups store directly.
/// Both arrays are padded to a full SIMD group.
#[cfg(any(test, feature = "multicore", feature = "orbits"))]
struct Coordinates {
    x: [Vec<u64>; LIMBS],
    y: [Vec<u64>; LIMBS],
}

#[cfg(any(test, feature = "multicore", feature = "orbits"))]
impl Coordinates {
    fn new(capacity: usize) -> Self {
        Self {
            x: core::array::from_fn(|_| Vec::with_capacity(capacity)),
            y: core::array::from_fn(|_| Vec::with_capacity(capacity)),
        }
    }

    fn resize(&mut self, len: usize) {
        let padded = len.div_ceil(LANES) * LANES;
        for coordinate in [&mut self.x, &mut self.y] {
            for limb in coordinate {
                limb.resize(padded, 0);
            }
        }
    }
}

#[cfg(any(test, feature = "multicore", feature = "orbits"))]
struct PairGroup {
    left: [usize; LANES],
    right: [usize; LANES],
    /// A zero bit is an odd carry or padding, not an affine chord.
    pairs: u8,
}

#[cfg(any(test, feature = "multicore", feature = "orbits"))]
struct Pending {
    numerator: Packed,
    denominator: Packed,
    x_sum: Packed,
    pairs: u8,
}

/// Correction modulus for private lazy additions, not a Montgomery modulus.
#[cfg(any(test, feature = "multicore", feature = "orbits"))]
struct LazyCorrection {
    twice_p: [u64; LIMBS],
}

#[cfg(any(test, feature = "multicore", feature = "orbits"))]
impl LazyCorrection {
    fn new(modulus: &Radix52Modulus) -> Self {
        let mut carry = 0;
        let twice_p = core::array::from_fn(|limb| {
            let value = modulus.p52[limb] * 2 + carry;
            carry = value >> RADIX;
            value & MASK52
        });
        debug_assert_eq!(carry, 0);
        Self { twice_p }
    }
}

#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
fn lazy_mul(lhs: &Packed, rhs: &Packed, modulus: &Radix52Modulus) -> Packed {
    // The true modulus is p. Inputs below 2p give a normalized result
    // below p + 4p^2/R260 < 9p/8, closing the private [0, 2p) invariant.
    mont_mul8(lhs, rhs, modulus)
}

#[target_feature(enable = "avx512f")]
#[cfg(any(test, feature = "multicore", feature = "orbits"))]
fn lazy_add(lhs: &Packed, rhs: &Packed, correction: &LazyCorrection) -> Packed {
    let mask = _mm512_set1_epi64(MASK52 as i64);
    let mut carry = _mm512_setzero_si512();
    let sum: Packed = core::array::from_fn(|limb| {
        let value = _mm512_add_epi64(_mm512_add_epi64(lhs[limb], rhs[limb]), carry);
        carry = _mm512_srli_epi64(value, RADIX);
        _mm512_and_si512(value, mask)
    });
    // x+y < 4p < 2^257, so no final carry is lost at the radix boundary.
    let mut borrow = _mm512_setzero_si512();
    let difference = core::array::from_fn::<_, LIMBS, _>(|limb| {
        let p = _mm512_set1_epi64(correction.twice_p[limb] as i64);
        let value = _mm512_sub_epi64(_mm512_sub_epi64(sum[limb], p), borrow);
        borrow = _mm512_srli_epi64(value, 63);
        _mm512_and_si512(value, mask)
    });
    let keep = _mm512_test_epi64_mask(borrow, borrow);
    core::array::from_fn(|limb| _mm512_mask_blend_epi64(keep, difference[limb], sum[limb]))
}

#[target_feature(enable = "avx512f")]
#[cfg(any(test, feature = "multicore", feature = "orbits"))]
fn lazy_sub(lhs: &Packed, rhs: &Packed, correction: &LazyCorrection) -> Packed {
    let zero = _mm512_setzero_si512();
    let mask = _mm512_set1_epi64(MASK52 as i64);
    let mut borrow = zero;
    let mut difference = core::array::from_fn::<_, LIMBS, _>(|limb| {
        let value = _mm512_sub_epi64(_mm512_sub_epi64(lhs[limb], rhs[limb]), borrow);
        borrow = _mm512_srli_epi64(value, 63);
        _mm512_and_si512(value, mask)
    });
    let add_modulus = _mm512_sub_epi64(zero, borrow);
    let mut carry = zero;
    for limb in 0..LIMBS {
        let p = _mm512_set1_epi64(correction.twice_p[limb] as i64);
        let value = _mm512_add_epi64(
            _mm512_add_epi64(difference[limb], _mm512_and_si512(p, add_modulus)),
            carry,
        );
        difference[limb] = _mm512_and_si512(value, mask);
        carry = _mm512_srli_epi64(value, RADIX);
    }
    difference
}

#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
fn mul(lhs: &Packed, rhs: &Packed, modulus: &Radix52Modulus) -> Packed {
    // Canonical bridges accept private inputs below 2p. Their result is
    // below 9p/8, so one subtraction produces canonical bits.
    cond_sub_p(&mont_mul8(lhs, rhs, modulus), modulus)
}

#[cfg(test)]
#[target_feature(enable = "avx512f")]
fn add(lhs: &Packed, rhs: &Packed, modulus: &Radix52Modulus) -> Packed {
    let mask = _mm512_set1_epi64(MASK52 as i64);
    let mut carry = _mm512_setzero_si512();
    let sum = core::array::from_fn(|limb| {
        let value = _mm512_add_epi64(_mm512_add_epi64(lhs[limb], rhs[limb]), carry);
        carry = _mm512_srli_epi64(value, RADIX);
        _mm512_and_si512(value, mask)
    });
    // x+y < 2p < 2^256, so no carry is lost at the 260-bit boundary.
    cond_sub_p(&sum, modulus)
}

#[target_feature(enable = "avx512f")]
fn sub(lhs: &Packed, rhs: &Packed, modulus: &Radix52Modulus) -> Packed {
    let zero = _mm512_setzero_si512();
    let mask = _mm512_set1_epi64(MASK52 as i64);
    let mut borrow = zero;
    let mut difference = core::array::from_fn(|limb| {
        let value = _mm512_sub_epi64(_mm512_sub_epi64(lhs[limb], rhs[limb]), borrow);
        borrow = _mm512_srli_epi64(value, 63);
        _mm512_and_si512(value, mask)
    });
    let add_modulus = _mm512_sub_epi64(zero, borrow);
    let mut carry = zero;
    for limb in 0..LIMBS {
        let p = _mm512_set1_epi64(modulus.p52[limb] as i64);
        let value = _mm512_add_epi64(
            _mm512_add_epi64(difference[limb], _mm512_and_si512(p, add_modulus)),
            carry,
        );
        difference[limb] = _mm512_and_si512(value, mask);
        carry = _mm512_srli_epi64(value, RADIX);
    }
    difference
}

/// Maps xR256 to xR260 using the Pasta modulus shape p = 2^254 + c.
///
/// For canonical raw bits N < p, q = N >> 250 is at most sixteen. Writing
/// 16N = q*2^254 + r gives 16N - q*p = r - q*c in [-16c, 2^254).
/// Both Pasta moduli have 0 < c < 2^128, so this lies in (-p, p): one
/// borrow-selected addition of p produces canonical 16N, without four
/// complete modular doublings. q*p is normalized before subtraction.
///
/// # Safety
///
/// `F` is exactly [`super::super::Fp`] or [`super::super::Fq`], and the CPU
/// supports the enabled target features.
#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
unsafe fn into_native<F: ff::Field>(values: &[F; LANES], modulus: &Radix52Modulus) -> Packed {
    debug_assert_eq!(modulus.p52[LIMBS - 1], 1 << TOP_MODULUS_LIMB_SHIFT);
    debug_assert_eq!(modulus.p52[LIMBS - 2], 0);
    debug_assert!(modulus.p52[2] < 1 << (128 - 2 * RADIX));
    debug_assert!(modulus.p52[..3].iter().any(|limb| *limb != 0));
    let value = unsafe { to_radix52(&load_transpose8x4(values.as_ptr().cast())) };
    const QUOTIENT_SHIFT: u32 = TOP_MODULUS_LIMB_SHIFT - RADIX_GAP;
    let quotient = _mm512_srli_epi64(value[LIMBS - 1], QUOTIENT_SHIFT);
    let mask = _mm512_set1_epi64(MASK52 as i64);
    let mut carry = _mm512_setzero_si512();
    let quotient_p = core::array::from_fn(|limb| {
        let p = _mm512_set1_epi64(modulus.p52[limb] as i64);
        let low = _mm512_madd52lo_epu64(carry, quotient, p);
        carry = _mm512_madd52hi_epu64(_mm512_srli_epi64(low, RADIX), quotient, p);
        _mm512_and_si512(low, mask)
    });
    // The operands can exceed p, but their difference is in (-p, p).
    // The radix subtraction's single borrow correction therefore suffices.
    sub(&shl_radix_gap(&value), &quotient_p, modulus)
}

/// Maps xR260 to xR256 using (xR260)*R256/R260.
///
/// `scalar_one` is the ordinary scalar field representation of one, R256.
/// It is deliberately not a native-R260 multiplicative identity.
/// `values` may be lazy: multiplying a value below 2p by scalar one below
/// p gives a result below `17p/16`, normalized once before the scalar store.
///
/// # Safety
///
/// Same exact-field and CPU requirements as [`into_native`].
#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
unsafe fn from_native<F: ff::Field>(
    values: &Packed,
    scalar_one: &Packed,
    modulus: &Radix52Modulus,
) -> [F; LANES] {
    let scalar = mul(values, scalar_one, modulus);
    let mut result = [F::ZERO; LANES];
    unsafe { store_transpose4x8(&from_radix52(&scalar), result.as_mut_ptr().cast()) };
    result
}

/// Evaluates the existing Pasta square-root exponent chains in native R260.
///
/// # Safety
///
/// `F` must be the exact Pasta field selected by `modulus`, and all enabled
/// target features must be supported. Inputs are canonical scalar values;
/// lazy scratch remains private and the exit bridge canonicalizes once.
#[cfg(feature = "sqrt-table")]
#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
pub(super) unsafe fn pow_t8<F: ff::Field>(
    values: &[F; LANES],
    modulus: &Radix52Modulus,
) -> [F; LANES] {
    use core::any::TypeId;

    let base = unsafe { into_native(values, modulus) };
    macro_rules! sqr_n {
        ($value:expr, $count:expr) => {{
            let mut value = $value;
            for _ in 0..$count {
                value = lazy_mul(&value, &value, modulus);
            }
            value
        }};
    }
    macro_rules! sqr_n_mul {
        ($value:expr, $count:expr, $by:expr) => {{ lazy_mul(&sqr_n!($value, $count), &$by, modulus) }};
    }
    let power = if TypeId::of::<F>() == TypeId::of::<super::super::Fp>() {
        let r10 = lazy_mul(&base, &base, modulus);
        let r11 = lazy_mul(&r10, &base, modulus);
        let r110 = lazy_mul(&r11, &r11, modulus);
        let r111 = lazy_mul(&r110, &base, modulus);
        let r1001 = lazy_mul(&r111, &r10, modulus);
        let r1101 = lazy_mul(&r111, &r110, modulus);
        let ra = sqr_n_mul!(base, 129, base);
        let rb = sqr_n_mul!(ra, 7, r1001);
        let rc = sqr_n_mul!(rb, 7, r1101);
        let rd = sqr_n_mul!(rc, 4, r11);
        let re = sqr_n_mul!(rd, 6, r111);
        let rf = sqr_n_mul!(re, 3, r111);
        let rg = sqr_n_mul!(rf, 10, r1001);
        let rh = sqr_n_mul!(rg, 5, r1001);
        let ri = sqr_n_mul!(rh, 4, r1001);
        let rj = sqr_n_mul!(ri, 3, r111);
        let rk = sqr_n_mul!(rj, 4, r1001);
        let rl = sqr_n_mul!(rk, 5, r11);
        let rm = sqr_n_mul!(rl, 4, r111);
        let rn = sqr_n_mul!(rm, 4, r11);
        let ro = sqr_n_mul!(rn, 6, r1001);
        let rp = sqr_n_mul!(ro, 5, r1101);
        let rq = sqr_n_mul!(rp, 4, r11);
        let rr = sqr_n_mul!(rq, 7, r111);
        let rs = sqr_n_mul!(rr, 3, r11);
        sqr_n!(rs, 1)
    } else {
        debug_assert_eq!(TypeId::of::<F>(), TypeId::of::<super::super::Fq>());
        let s10 = lazy_mul(&base, &base, modulus);
        let s11 = lazy_mul(&s10, &base, modulus);
        let s111 = sqr_n_mul!(s11, 1, base);
        let s1001 = lazy_mul(&s111, &s10, modulus);
        let s1011 = lazy_mul(&s1001, &s10, modulus);
        let s1101 = lazy_mul(&s1011, &s10, modulus);
        let sa = sqr_n_mul!(base, 129, base);
        let sb = sqr_n_mul!(sa, 7, s1001);
        let sc = sqr_n_mul!(sb, 7, s1101);
        let sd = sqr_n_mul!(sc, 4, s11);
        let se = sqr_n_mul!(sd, 6, s111);
        let sf = sqr_n_mul!(se, 3, s111);
        let sg = sqr_n_mul!(sf, 10, s1001);
        let sh = sqr_n_mul!(sg, 4, s1001);
        let si = sqr_n_mul!(sh, 5, s1001);
        let sj = sqr_n_mul!(si, 5, s1001);
        let sk = sqr_n_mul!(sj, 3, s1001);
        let sl = sqr_n_mul!(sk, 4, s1011);
        let sm = sqr_n_mul!(sl, 4, s1011);
        let sn = sqr_n_mul!(sm, 5, s11);
        let so = sqr_n_mul!(sn, 4, base);
        let sp = sqr_n_mul!(so, 5, s11);
        let sq = sqr_n_mul!(sp, 4, s111);
        let sr = sqr_n_mul!(sq, 5, s1011);
        let ss = sqr_n_mul!(sr, 3, base);
        sqr_n!(ss, 4)
    };
    let ones = [F::ONE; LANES];
    let scalar_one = unsafe { to_radix52(&load_transpose8x4(ones.as_ptr().cast())) };
    unsafe { from_native(&power, &scalar_one, modulus) }
}

/// Gathers real or padded indices from allocated, normalized limb arrays.
///
/// # Safety
///
/// Every index is in bounds in all limb arrays. The CPU supports AVX-512F.
#[target_feature(enable = "avx512f")]
#[cfg(any(test, feature = "multicore", feature = "orbits"))]
unsafe fn gather(values: &[Vec<u64>; LIMBS], indices: &[usize; LANES]) -> Packed {
    // Most groups are eight consecutive pairs within one bucket. Two
    // contiguous loads and a permutation beat a gather in that common case.
    let start = indices[0];
    if indices.windows(2).all(|pair| pair[1] == pair[0] + 2) && start + 2 * LANES <= values[0].len()
    {
        let even = _mm512_set_epi64(14, 12, 10, 8, 6, 4, 2, 0);
        return core::array::from_fn(|limb| unsafe {
            let lo = _mm512_loadu_si512(values[limb].as_ptr().add(start).cast());
            let hi = _mm512_loadu_si512(values[limb].as_ptr().add(start + LANES).cast());
            _mm512_permutex2var_epi64(lo, even, hi)
        });
    }
    let indices = unsafe { _mm512_loadu_si512(indices.as_ptr().cast()) };
    core::array::from_fn(|limb| unsafe {
        _mm512_i64gather_epi64::<8>(indices, values[limb].as_ptr().cast())
    })
}

#[target_feature(enable = "avx512f")]
#[cfg(any(test, feature = "multicore", feature = "orbits"))]
unsafe fn load_group(values: &[Vec<u64>; LIMBS], group: usize) -> Packed {
    core::array::from_fn(|limb| unsafe {
        _mm512_loadu_si512(values[limb].as_ptr().add(group * LANES).cast())
    })
}

#[target_feature(enable = "avx512f")]
#[cfg(any(test, feature = "multicore", feature = "orbits"))]
unsafe fn store_group(values: &mut [Vec<u64>; LIMBS], group: usize, packed: &Packed) {
    for limb in 0..LIMBS {
        unsafe {
            _mm512_storeu_si512(
                values[limb].as_mut_ptr().add(group * LANES).cast(),
                packed[limb],
            )
        };
    }
}

#[cfg(any(test, feature = "multicore", feature = "orbits"))]
fn plan(offsets: &[usize], groups: &mut Vec<PairGroup>, next_offsets: &mut Vec<usize>) -> usize {
    groups.clear();
    next_offsets.clear();
    next_offsets.push(0);
    let mut group = PairGroup {
        left: [0; LANES],
        right: [0; LANES],
        pairs: 0,
    };
    let mut outputs = 0;
    for range in offsets.windows(2) {
        let mut input = range[0];
        while input < range[1] {
            let lane = outputs % LANES;
            group.left[lane] = input;
            let paired = input + 1 < range[1];
            group.right[lane] = input + usize::from(paired);
            if paired {
                group.pairs |= 1 << lane;
            }
            input += 1 + usize::from(paired);
            outputs += 1;
            if outputs % LANES == 0 {
                groups.push(group);
                group = PairGroup {
                    left: [0; LANES],
                    right: [0; LANES],
                    pairs: 0,
                };
            }
        }
        next_offsets.push(outputs);
    }
    if outputs % LANES != 0 {
        groups.push(group);
    }
    outputs
}

/// Reduces valid nonidentity affine inputs with incomplete chord formulas.
/// The source closure is read-only; a failed guard discards all scratch.
///
/// # Safety
///
/// `F` is exactly the Pasta field selected by `modulus`. All enabled CPU
/// features are available. Non-decreasing offsets start at zero and end at
/// `point_count`, partitioning the closure's valid indices.
#[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
#[cfg(any(test, feature = "multicore", feature = "orbits"))]
pub(super) unsafe fn reduce<F: ff::Field>(
    point_count: usize,
    offsets: &[usize],
    point_at: impl Fn(usize) -> (F, F),
    modulus: &Radix52Modulus,
) -> Option<Vec<Option<(F, F)>>> {
    // The entry point is safe for arbitrary lengths. Check rounding before
    // allocating scratch or forming SIMD addresses, including synthetic
    // callers whose coordinate reader does not borrow a real input vector.
    let padded = point_count.checked_add(LANES - 1)? / LANES * LANES;
    if padded > isize::MAX as usize / core::mem::size_of::<u64>() {
        return None;
    }
    let bucket_count = offsets.len() - 1;
    if point_count == 0 {
        return Some(alloc::vec![None; bucket_count]);
    }
    let ones = [F::ONE; LANES];
    let scalar_one = unsafe { to_radix52(&load_transpose8x4(ones.as_ptr().cast())) };
    let native_one = unsafe { into_native(&ones, modulus) };
    let correction = LazyCorrection::new(modulus);
    let zero = [_mm512_setzero_si512(); LIMBS];
    let mut points = Coordinates::new(padded);
    points.resize(point_count);
    for group in 0..point_count.div_ceil(LANES) {
        let coords: [(F, F); LANES] = core::array::from_fn(|lane| {
            let index = group * LANES + lane;
            if index < point_count {
                point_at(index)
            } else {
                (F::ZERO, F::ZERO)
            }
        });
        let x = coords.map(|point| point.0);
        let y = coords.map(|point| point.1);
        unsafe {
            store_group(&mut points.x, group, &into_native(&x, modulus));
            store_group(&mut points.y, group, &into_native(&y, modulus));
        }
    }
    let mut offsets = offsets.to_vec();
    let mut next_offsets = Vec::with_capacity(offsets.len());
    // Odd buckets carry one operand, so ceil(total/2) can under-reserve
    // scratch and make all ten limb vectors grow on the first level.
    let first_outputs: usize = offsets
        .windows(2)
        .map(|range| (range[1] - range[0]).div_ceil(2))
        .sum();
    let mut next = Coordinates::new(first_outputs.div_ceil(LANES) * LANES);
    let mut groups = Vec::with_capacity(first_outputs.div_ceil(LANES));
    let mut pending = Vec::with_capacity(groups.capacity());

    while offsets.windows(2).any(|range| range[1] - range[0] > 1) {
        let outputs = plan(&offsets, &mut groups, &mut next_offsets);
        next.resize(outputs);
        pending.clear();
        for (group_index, group) in groups.iter().enumerate() {
            // Every real index comes from a validated input range; padding
            // uses index zero, available because point_count is nonzero.
            let left_x = unsafe { gather(&points.x, &group.left) };
            let left_y = unsafe { gather(&points.y, &group.left) };
            let right_x = unsafe { gather(&points.x, &group.right) };
            let right_y = unsafe { gather(&points.y, &group.right) };
            let numerator = lazy_sub(&right_y, &left_y, &correction);
            let denominator = lazy_sub(&right_x, &left_x, &correction);
            let numerator = core::array::from_fn(|limb| {
                _mm512_mask_blend_epi64(group.pairs, zero[limb], numerator[limb])
            });
            let denominator = core::array::from_fn(|limb| {
                _mm512_mask_blend_epi64(group.pairs, native_one[limb], denominator[limb])
            });
            pending.push(Pending {
                numerator,
                denominator,
                x_sum: lazy_add(&left_x, &right_x, &correction),
                pairs: group.pairs,
            });
            unsafe {
                store_group(&mut next.x, group_index, &left_x);
                store_group(&mut next.y, group_index, &left_y);
            }
        }

        let mut lane_products = pending[0].denominator;
        for addition in pending.iter_mut().skip(1) {
            addition.numerator = lazy_mul(&addition.numerator, &lane_products, modulus);
            lane_products = lazy_mul(&lane_products, &addition.denominator, modulus);
        }
        // Map the eight products to ordinary field values, perform one
        // shared scalar inversion, and map recovered inverses back to R260.
        // Canonicalization catches both lazy representations of field zero,
        // raw 0 and raw p, before the inversion guard or any chord writes.
        let products = unsafe { from_native::<F>(&lane_products, &scalar_one, modulus) };
        let mut prefixes = [F::ONE; LANES];
        let mut product = products[0];
        for lane in 1..LANES {
            prefixes[lane] = product;
            product *= products[lane];
        }
        let mut inverse = Option::<F>::from(product.invert())?;
        let mut inverses = [F::ZERO; LANES];
        for lane in (1..LANES).rev() {
            inverses[lane] = prefixes[lane] * inverse;
            inverse *= products[lane];
        }
        inverses[0] = inverse;
        let mut inverses = unsafe { into_native(&inverses, modulus) };

        // No chord result is written until every denominator in this
        // level passed the product guard. Scratch from earlier levels is
        // private too, so a late failure leaves the original source intact.
        for (group, addition) in pending.iter().enumerate().rev() {
            let slopes = lazy_mul(&addition.numerator, &inverses, modulus);
            if group != 0 {
                inverses = lazy_mul(&inverses, &addition.denominator, modulus);
            }
            let left_x = unsafe { load_group(&next.x, group) };
            let left_y = unsafe { load_group(&next.y, group) };
            let x = lazy_sub(
                &lazy_mul(&slopes, &slopes, modulus),
                &addition.x_sum,
                &correction,
            );
            let y = lazy_sub(
                &lazy_mul(&slopes, &lazy_sub(&left_x, &x, &correction), modulus),
                &left_y,
                &correction,
            );
            let x = core::array::from_fn(|limb| {
                _mm512_mask_blend_epi64(addition.pairs, left_x[limb], x[limb])
            });
            let y = core::array::from_fn(|limb| {
                _mm512_mask_blend_epi64(addition.pairs, left_y[limb], y[limb])
            });
            unsafe {
                store_group(&mut next.x, group, &x);
                store_group(&mut next.y, group, &y);
            }
        }
        core::mem::swap(&mut points, &mut next);
        core::mem::swap(&mut offsets, &mut next_offsets);
    }

    let mut buckets = Vec::with_capacity(bucket_count);
    for group in (0..bucket_count).step_by(LANES) {
        let indices = core::array::from_fn(|lane| {
            let bucket = group + lane;
            if bucket < bucket_count && offsets[bucket] != offsets[bucket + 1] {
                offsets[bucket]
            } else {
                0
            }
        });
        let x = unsafe { from_native::<F>(&gather(&points.x, &indices), &scalar_one, modulus) };
        let y = unsafe { from_native::<F>(&gather(&points.y, &indices), &scalar_one, modulus) };
        for lane in 0..LANES.min(bucket_count - group) {
            let bucket = group + lane;
            if offsets[bucket] != offsets[bucket + 1] {
                debug_assert_eq!(offsets[bucket + 1] - offsets[bucket], 1);
                buckets.push(Some((x[lane], y[lane])));
            } else {
                buckets.push(None);
            }
        }
    }
    Some(buckets)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    fn modulus_words<F: ff::Field>() -> [u64; 4] {
        let mut words = [0u64; 4];
        for (limb, value) in modulus::<F>().unwrap().p52.iter().enumerate() {
            let bit = limb * RADIX as usize;
            let word = bit / u64::BITS as usize;
            let shift = bit % u64::BITS as usize;
            words[word] |= value << shift;
            if shift != 0 && word + 1 < words.len() {
                words[word + 1] |= value >> (u64::BITS as usize - shift);
            }
        }
        words
    }

    fn add_words(lhs: [u64; 4], rhs: [u64; 4]) -> [u64; 4] {
        let mut carry = 0u128;
        let sum = core::array::from_fn(|word| {
            let value = u128::from(lhs[word]) + u128::from(rhs[word]) + carry;
            carry = value >> u64::BITS;
            value as u64
        });
        assert_eq!(carry, 0);
        sum
    }

    #[cfg(feature = "sqrt-table")]
    #[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
    unsafe fn check_sqrt_exponent<F: ff::PrimeField>() {
        fn decrement(words: &mut [u64; 4]) {
            for word in words {
                let (value, borrow) = word.overflowing_sub(1);
                *word = value;
                if !borrow {
                    return;
                }
            }
            panic!("positive exponent expected");
        }
        fn halve(words: &mut [u64; 4]) {
            let mut high_bit = 0;
            for word in words.iter_mut().rev() {
                let next = *word << (u64::BITS - 1);
                *word = (*word >> 1) | high_bit;
                high_bit = next;
            }
        }
        // Derive (T-1)/2 independently from p-1 = T*2^S; this reference
        // does not reuse either field-specific addition chain.
        let mut exponent = modulus_words::<F>();
        decrement(&mut exponent);
        for _ in 0..F::S {
            halve(&mut exponent);
        }
        decrement(&mut exponent);
        halve(&mut exponent);
        let mut rng = XorShiftRng::from_seed([0x8C; 16]);
        let boundaries = [F::ZERO, F::ONE, -F::ONE, F::from(2), -F::from(2)];
        for iteration in 0..128 {
            let values = core::array::from_fn(|lane| {
                if iteration < boundaries.len() {
                    boundaries[(iteration + lane) % boundaries.len()]
                } else {
                    F::random(&mut rng)
                }
            });
            let expected = values.map(|value| value.pow_vartime(exponent));
            assert_eq!(
                unsafe { pow_t8(&values, modulus::<F>().unwrap()) },
                expected,
                "native sqrt exponent iteration {iteration}",
            );
        }
    }

    #[cfg(feature = "sqrt-table")]
    #[test]
    fn packed_sqrt_exponents_match_independent_model() {
        if available_for::<super::super::super::Fp>() {
            // SAFETY: concrete fields and runtime CPU/OS checks establish
            // all representation and instruction requirements.
            unsafe {
                check_sqrt_exponent::<super::super::super::Fp>();
                check_sqrt_exponent::<super::super::super::Fq>();
            }
        }
    }

    fn sub_words(lhs: [u64; 4], rhs: [u64; 4]) -> [u64; 4] {
        let mut borrow = false;
        let difference = core::array::from_fn(|word| {
            let (value, first) = lhs[word].overflowing_sub(rhs[word]);
            let (value, second) = value.overflowing_sub(u64::from(borrow));
            borrow = first || second;
            value
        });
        assert!(!borrow);
        difference
    }

    /// Checks every limb before reconstructing words, so an unnormalized
    /// limb cannot disappear through the scalar bridge's bit packing.
    #[target_feature(enable = "avx512f")]
    unsafe fn checked_lazy_words(value: &Packed, twice_p: [u64; 4]) -> [[u64; 4]; LANES] {
        let mut words = [[0u64; 4]; LANES];
        for (limb, vector) in value.iter().enumerate() {
            let mut lanes = [0u64; LANES];
            unsafe { _mm512_storeu_si512(lanes.as_mut_ptr().cast(), *vector) };
            let bit = limb * RADIX as usize;
            let word = bit / u64::BITS as usize;
            let shift = bit % u64::BITS as usize;
            for (lane, value) in lanes.into_iter().enumerate() {
                assert!(value <= MASK52, "limb {limb}, lane {lane}");
                words[lane][word] |= value << shift;
                if shift != 0 {
                    let high = value >> (u64::BITS as usize - shift);
                    if word + 1 < words[lane].len() {
                        words[lane][word + 1] |= high;
                    } else {
                        assert_eq!(high, 0, "lazy residue exceeds 256 bits");
                    }
                }
            }
        }
        for value in &words {
            assert!(value.iter().rev().cmp(twice_p.iter().rev()).is_lt());
        }
        words
    }

    #[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
    unsafe fn check_lazy_arithmetic<F: ff::Field>(from_words: impl Fn([u64; 4]) -> F) {
        let modulus = modulus::<F>().unwrap();
        let correction = LazyCorrection::new(modulus);
        let p = modulus_words::<F>();
        let twice_p = add_words(p, p);
        let one = [1, 0, 0, 0];
        let boundaries = [
            [0; 4],
            one,
            sub_words(p, one),
            p,
            add_words(p, one),
            sub_words(twice_p, one),
            [0, 0, 0, 1 << 62],
            sub_words([0, 0, 0, 1 << 62], one),
        ];
        let ones = [F::ONE; LANES];
        let scalar_one = unsafe { to_radix52(&load_transpose8x4(ones.as_ptr().cast())) };
        let mut radix_factor = F::ONE;
        for _ in 0..RADIX_GAP {
            radix_factor = radix_factor.double();
        }
        let inverse_factor = Option::<F>::from(radix_factor.invert()).unwrap();
        let reference = |words: [u64; 4]| {
            // Never construct a scalar field with raw p or another lazy
            // alias: normalize the integer words before the constructor.
            let canonical = if words.iter().rev().cmp(p.iter().rev()).is_lt() {
                words
            } else {
                sub_words(words, p)
            };
            from_words(canonical) * inverse_factor
        };
        let mut rng = XorShiftRng::from_seed([0xC7; 16]);
        for iteration in 0..1024 + LANES {
            let (left_words, right_words, lhs, rhs) = if iteration < LANES {
                let right = core::array::from_fn(|lane| boundaries[(lane + iteration) % LANES]);
                (
                    boundaries,
                    right,
                    boundaries.map(&reference),
                    right.map(&reference),
                )
            } else {
                let lhs = core::array::from_fn(|_| F::random(&mut rng));
                let rhs = core::array::from_fn(|_| F::random(&mut rng));
                let left = unsafe { into_native(&lhs, modulus) };
                let right = unsafe { into_native(&rhs, modulus) };
                let mut left_words = unsafe { checked_lazy_words(&left, twice_p) };
                let mut right_words = unsafe { checked_lazy_words(&right, twice_p) };
                for lane in 0..LANES {
                    if (iteration + lane) & 1 != 0 {
                        left_words[lane] = add_words(left_words[lane], p);
                    }
                    if (iteration / 2 + lane) & 1 != 0 {
                        right_words[lane] = add_words(right_words[lane], p);
                    }
                }
                (left_words, right_words, lhs, rhs)
            };
            let left = unsafe { to_radix52(&load_transpose8x4(left_words.as_ptr().cast())) };
            let right = unsafe { to_radix52(&load_transpose8x4(right_words.as_ptr().cast())) };
            let actual = [
                lazy_mul(&left, &right, modulus),
                lazy_add(&left, &right, &correction),
                lazy_sub(&left, &right, &correction),
                lazy_mul(&left, &left, modulus),
            ];
            let expected = [
                core::array::from_fn::<_, LANES, _>(|lane| lhs[lane] * rhs[lane]),
                core::array::from_fn(|lane| lhs[lane] + rhs[lane]),
                core::array::from_fn(|lane| lhs[lane] - rhs[lane]),
                lhs.map(|value| value.square()),
            ];
            for (actual, expected) in actual.iter().zip(expected) {
                unsafe { checked_lazy_words(actual, twice_p) };
                assert_eq!(
                    unsafe { from_native::<F>(actual, &scalar_one, modulus) },
                    expected,
                    "lazy arithmetic iteration {iteration}",
                );
            }
            // Outputs of one lazy operation are legal inputs to the next,
            // including a subtraction that chooses the p alias of zero.
            let restored = lazy_sub(&actual[1], &left, &correction);
            let chained = lazy_mul(&restored, &right, modulus);
            unsafe { checked_lazy_words(&restored, twice_p) };
            unsafe { checked_lazy_words(&chained, twice_p) };
            assert_eq!(
                unsafe { from_native::<F>(&chained, &scalar_one, modulus) },
                rhs.map(|value| value.square()),
            );
        }
    }

    #[test]
    fn packed_lazy_arithmetic_edges_and_aliases() {
        if available_for::<super::super::super::Fp>() {
            // SAFETY: exact fields and runtime CPU checks meet the helpers'
            // contracts; raw lazy aliases stay outside scalar constructors.
            unsafe {
                check_lazy_arithmetic(super::super::super::Fp);
                check_lazy_arithmetic(super::super::super::Fq);
            }
        }
    }

    #[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
    unsafe fn check_lazy_zero_aliases<F: ff::Field>() {
        let modulus = modulus::<F>().unwrap();
        let correction = LazyCorrection::new(modulus);
        let p = modulus_words::<F>();
        let twice_p = add_words(p, p);
        let raw_zero = [p; LANES];
        let zero = unsafe { to_radix52(&load_transpose8x4(raw_zero.as_ptr().cast())) };
        let ones = [F::ONE; LANES];
        let scalar_one = unsafe { to_radix52(&load_transpose8x4(ones.as_ptr().cast())) };
        let native_one = unsafe { into_native(&ones, modulus) };
        let one_words = unsafe { checked_lazy_words(&native_one, twice_p) };
        let alias_words = one_words.map(|words| add_words(words, p));
        let alias = unsafe { to_radix52(&load_transpose8x4(alias_words.as_ptr().cast())) };
        let alias_difference = lazy_sub(&native_one, &alias, &correction);
        assert_eq!(
            unsafe { checked_lazy_words(&alias_difference, twice_p) },
            raw_zero
        );
        for value in [
            zero,
            alias_difference,
            lazy_mul(&zero, &native_one, modulus),
            lazy_add(&zero, &zero, &correction),
        ] {
            unsafe { checked_lazy_words(&value, twice_p) };
            let products = unsafe { from_native::<F>(&value, &scalar_one, modulus) };
            assert_eq!(products, [F::ZERO; LANES]);
            // The reducer's guard must test canonical field zero, not raw
            // bits: p is a lazy zero even though its limbs are nonzero.
            assert!(Option::<F>::from(products.into_iter().product::<F>().invert()).is_none());
        }
    }

    #[test]
    fn packed_lazy_zero_aliases_guard_inversion() {
        if available_for::<super::super::super::Fp>() {
            // SAFETY: exact fields and runtime CPU detection meet the
            // representation and instruction requirements of the helpers.
            unsafe {
                check_lazy_zero_aliases::<super::super::super::Fp>();
                check_lazy_zero_aliases::<super::super::super::Fq>();
            }
        }
    }

    fn add_neighbors(cases: &mut Vec<[u64; 4]>, center: [u64; 4], modulus: [u64; 4]) {
        for delta in [-1, 0, 1] {
            let mut words = center;
            let mut overflow = false;
            if delta != 0 {
                let mut carry = true;
                for word in &mut words {
                    if !carry {
                        break;
                    }
                    let (value, next) = if delta < 0 {
                        word.overflowing_sub(1)
                    } else {
                        word.overflowing_add(1)
                    };
                    *word = value;
                    carry = next;
                }
                overflow = carry;
            }
            if !overflow && words.iter().rev().cmp(modulus.iter().rev()).is_lt() {
                cases.push(words);
            }
        }
    }

    #[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
    unsafe fn check_entry_quotient_boundaries<F: ff::Field>(from_words: impl Fn([u64; 4]) -> F) {
        let modulus = modulus::<F>().unwrap();
        let p = modulus.p52;
        assert_eq!(p[4], 1 << 46);
        assert_eq!(p[3], 0);
        assert!(p[2] < 1 << 24 && p[..3].iter().any(|limb| *limb != 0));
        let p = [
            p[0] | (p[1] << 52),
            (p[1] >> 12) | (p[2] << 40),
            (p[2] >> 24) | (p[3] << 28),
            (p[3] >> 36) | (p[4] << 16),
        ];
        let mut cases = Vec::new();
        let mut minus_one = p;
        minus_one[0] -= 1;
        add_neighbors(&mut cases, minus_one, p);
        for quotient in 0..=16u64 {
            // Quotient changes at q*2^250, including the q=16 interval
            // between 2^254 and p that a strict 254-bit bound would omit.
            add_neighbors(&mut cases, [0, 0, 0, quotient << 58], p);

            // The borrow flips at ceil(q*p/16). Use independent 64-bit
            // integer arithmetic to find that boundary, not SIMD or fields.
            let mut product = [0u64; 5];
            let mut carry = 0u128;
            for limb in 0..4 {
                let value = u128::from(p[limb]) * u128::from(quotient) + carry;
                product[limb] = value as u64;
                carry = value >> 64;
            }
            product[4] = carry as u64;
            let mut threshold = core::array::from_fn::<_, 4, _>(|limb| {
                (product[limb] >> RADIX_GAP) | (product[limb + 1] << (64 - RADIX_GAP))
            });
            if product[0] & ((1 << RADIX_GAP) - 1) != 0 {
                for word in &mut threshold {
                    let (value, carry) = word.overflowing_add(1);
                    *word = value;
                    if !carry {
                        break;
                    }
                }
            }
            add_neighbors(&mut cases, threshold, p);
        }

        for chunk in cases.chunks(LANES) {
            let values: [F; LANES] =
                core::array::from_fn(|lane| from_words(chunk.get(lane).copied().unwrap_or([0; 4])));
            let actual = unsafe { into_native(&values, modulus) };
            // Comparing raw output words with four scalar field doublings
            // checks canonical 16N mod p independently of the native bridge.
            let expected = values.map(|mut value| {
                for _ in 0..RADIX_GAP {
                    value = value.double();
                }
                value
            });
            let mut actual_words = [F::ZERO; LANES];
            unsafe {
                store_transpose4x8(&from_radix52(&actual), actual_words.as_mut_ptr().cast());
            }
            assert_eq!(actual_words, expected);
        }
    }

    #[test]
    fn packed_entry_quotient_boundaries() {
        if available_for::<super::super::super::Fp>() {
            // SAFETY: exact fields and runtime CPU detection meet the helper
            // requirements; the constructors receive canonical raw words.
            unsafe {
                check_entry_quotient_boundaries(super::super::super::Fp);
                check_entry_quotient_boundaries(super::super::super::Fq);
            }
        }
    }

    fn raw_native_boundaries<F: ff::Field>() -> [[u64; 4]; LANES] {
        let words = modulus_words::<F>();
        let subtract_one = |mut words: [u64; 4]| {
            for word in &mut words {
                let (value, borrow) = word.overflowing_sub(1);
                *word = value;
                if !borrow {
                    break;
                }
            }
            words
        };
        let minus_one = subtract_one(words);
        let minus_two = subtract_one(minus_one);
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

    #[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
    unsafe fn check_raw_native_boundaries<F: ff::Field>(raw: [F; LANES]) {
        let modulus = modulus::<F>().unwrap();
        let ones = [F::ONE; LANES];
        let scalar_one = unsafe { to_radix52(&load_transpose8x4(ones.as_ptr().cast())) };
        let native_one = unsafe { into_native(&ones, modulus) };
        let mut radix_factor = F::ONE;
        for _ in 0..RADIX_GAP {
            radix_factor = radix_factor.double();
        }
        let inverse_factor = Option::<F>::from(radix_factor.invert()).unwrap();

        // Interpret the canonical raw words directly in R260, not through
        // into_native: p - 1 and p - 2 must reach the native arithmetic intact.
        // As scalar-R256 fields, those same words represent sixteen times
        // their native-domain values, so divide by the radix factor here.
        let expected = raw.map(|value| value * inverse_factor);
        let left = unsafe { to_radix52(&load_transpose8x4(raw.as_ptr().cast())) };
        assert_eq!(
            unsafe { from_native::<F>(&left, &scalar_one, modulus) },
            expected,
        );
        let round_trip = unsafe { into_native(&expected, modulus) };
        for limb in 0..LIMBS {
            assert_eq!(
                _mm512_cmpeq_epi64_mask(round_trip[limb], left[limb]),
                u8::MAX,
            );
        }

        for shift in 0..LANES {
            let right_raw: [F; LANES] = core::array::from_fn(|lane| raw[(lane + shift) % LANES]);
            let right_values: [F; LANES] =
                core::array::from_fn(|lane| expected[(lane + shift) % LANES]);
            let right = unsafe { to_radix52(&load_transpose8x4(right_raw.as_ptr().cast())) };
            for (actual, reference) in [
                (
                    mul(&left, &right, modulus),
                    core::array::from_fn(|lane| expected[lane] * right_values[lane]),
                ),
                (
                    add(&left, &right, modulus),
                    core::array::from_fn(|lane| expected[lane] + right_values[lane]),
                ),
                (
                    sub(&left, &right, modulus),
                    core::array::from_fn(|lane| expected[lane] - right_values[lane]),
                ),
            ] {
                assert_eq!(
                    unsafe { from_native::<F>(&actual, &scalar_one, modulus) },
                    reference,
                );
            }
        }

        let nonzero = expected.map(|value| {
            if value.is_zero_vartime() {
                F::ONE
            } else {
                value
            }
        });
        let inverses = nonzero.map(|value| Option::<F>::from(value.invert()).unwrap());
        let nonzero = unsafe { into_native(&nonzero, modulus) };
        let inverses = unsafe { into_native(&inverses, modulus) };
        let product = mul(&nonzero, &inverses, modulus);
        for limb in 0..LIMBS {
            assert_eq!(
                _mm512_cmpeq_epi64_mask(product[limb], native_one[limb]),
                u8::MAX,
            );
        }
    }

    #[test]
    fn packed_raw_native_boundaries_match_scalar() {
        if available_for::<super::super::super::Fp>() {
            // SAFETY: runtime CPU detection and exact concrete fields meet
            // the representation and instruction requirements of the helper.
            unsafe {
                check_raw_native_boundaries(
                    raw_native_boundaries::<super::super::super::Fp>().map(super::super::super::Fp),
                );
                check_raw_native_boundaries(
                    raw_native_boundaries::<super::super::super::Fq>().map(super::super::super::Fq),
                );
            }
        }
    }

    #[test]
    fn packed_oversized_inputs_do_not_call_source() {
        fn check<F: ff::Field>() {
            for point_count in [
                usize::MAX,
                usize::MAX - (LANES - 1),
                isize::MAX as usize / core::mem::size_of::<u64>() + 1,
            ] {
                assert!(
                    super::super::reduce_affine_buckets::<F>(
                        point_count,
                        &[0, point_count],
                        |_| panic!("oversized inputs must not call the source"),
                    )
                    .is_none(),
                );
            }
        }
        check::<super::super::super::Fp>();
        check::<super::super::super::Fq>();
    }

    #[target_feature(enable = "avx512f,avx512ifma,avx512vl")]
    unsafe fn check_native_domain<F: ff::Field>() {
        let modulus = modulus::<F>().unwrap();
        let ones = [F::ONE; LANES];
        let scalar_one = unsafe { to_radix52(&load_transpose8x4(ones.as_ptr().cast())) };
        let native_one = unsafe { into_native(&ones, modulus) };
        let two = F::ONE.double();
        let boundaries = [F::ZERO, F::ONE, -F::ONE, two, -two];
        let mut rng = XorShiftRng::from_seed([0x6B; 16]);
        for iteration in 0..1024 {
            let lhs = core::array::from_fn(|lane| {
                if iteration < boundaries.len() {
                    boundaries[(iteration + lane) % boundaries.len()]
                } else {
                    F::random(&mut rng)
                }
            });
            let rhs = core::array::from_fn(|lane| {
                if iteration < boundaries.len() {
                    boundaries[(iteration * 2 + lane) % boundaries.len()]
                } else {
                    F::random(&mut rng)
                }
            });
            let left = unsafe { into_native(&lhs, modulus) };
            let right = unsafe { into_native(&rhs, modulus) };
            assert_eq!(
                unsafe { from_native::<F>(&left, &scalar_one, modulus) },
                lhs
            );
            for (actual, expected) in [
                (
                    mul(&left, &right, modulus),
                    core::array::from_fn(|i| lhs[i] * rhs[i]),
                ),
                (
                    add(&left, &right, modulus),
                    core::array::from_fn(|i| lhs[i] + rhs[i]),
                ),
                (
                    sub(&left, &right, modulus),
                    core::array::from_fn(|i| lhs[i] - rhs[i]),
                ),
            ] {
                assert_eq!(
                    unsafe { from_native::<F>(&actual, &scalar_one, modulus) },
                    expected
                );
            }
            if lhs.iter().all(|value| !value.is_zero_vartime()) {
                let inverses = lhs.map(|value| Option::<F>::from(value.invert()).unwrap());
                let inverses = unsafe { into_native(&inverses, modulus) };
                let product = mul(&left, &inverses, modulus);
                assert_eq!(
                    unsafe { from_native::<F>(&product, &scalar_one, modulus) },
                    ones
                );
                for limb in 0..LIMBS {
                    assert_eq!(
                        _mm512_cmpeq_epi64_mask(product[limb], native_one[limb]),
                        u8::MAX,
                    );
                }
            }
        }
    }

    #[test]
    fn packed_native_domain_and_inversion_bridge() {
        if available_for::<super::super::super::Fp>() {
            // SAFETY: exact fields and runtime CPU checks match the helpers.
            unsafe {
                check_native_domain::<super::super::super::Fp>();
                check_native_domain::<super::super::super::Fq>();
            }
        }
    }
}
