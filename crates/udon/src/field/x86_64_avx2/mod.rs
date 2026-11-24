//! Four-lane AVX2 arithmetic for both Pasta fields, in radix 2^29.
//!
//! A serial chain of field squarings already saturates the x86-64 integer
//! multiplier, so interleaving scalar chains gains little there. This module
//! instead holds four field elements in one set of AVX2 registers, one element
//! per 64-bit lane, and squares or multiplies all four with `vpmuludq`. It
//! serves the exponentiation behind square roots (and so point decoding);
//! [`PowerVectors`] is its only interface, and no radix-2^29 value leaves the
//! module.
//!
//! # Availability
//!
//! The build script compiles this module (`udon_avx2`) on 64-bit x86-64 when
//! the target enables AVX2, or when the `x86_64-asm` feature forces the
//! x86-64 backend; `portable` disables it. Running AVX2 code on a CPU without
//! AVX2 is undefined behavior, so both conditions must guarantee it:
//!
//! - A target that enables AVX2 promises a CPU that has it.
//! - The forced backend's documented requirement is a CPU with BMI2, ADX, and
//!   AVX2. Every Intel and AMD CPU with BMI2 and ADX has AVX2 (on Intel, BMI2
//!   and AVX2 arrived with Haswell and ADX with Broadwell, and the Pentium,
//!   Celeron, and Atom parts without AVX2 lack BMI2 too; on AMD all three are
//!   present from Zen on), but a virtual machine that exposes BMI2 and ADX
//!   while hiding AVX does not meet the requirement.
//!
//! Automatic backend selection from ADX and BMI2 target features does not
//! enable this module by itself: such a target may omit or disable AVX2.
//! Every `unsafe` call of an AVX2 function below relies on this contract and
//! on nothing else.
//!
//! # Arithmetic
//!
//! A lane holds a residue in nine limbs of 29 bits, in Montgomery form with
//! `R' = 2^261`. Both Pasta moduli are `1 mod 2^32`, so each reduction
//! round's Montgomery factor is a negation, and in radix 2^29 both have limb
//! 0 equal to 1, limbs 5 to 7 zero, and limb 8 equal to 2^22
//! ([`modulus_limbs`] checks this for every modulus the kernels are
//! instantiated with). The kernels are transcriptions of the ones in
//! zakura-pasta-curves and keep their bounds:
//!
//! - Inputs below `2p` give a product below `4p^2`, and the Montgomery result
//!   `(t + Q p) / R'` is below `4p^2 / R' + p < 1.04 p`. Values therefore stay
//!   below `2p`, the bound of the scalar kernels' loose form, with no
//!   conditional subtraction.
//! - Output limbs 0 to 7 are below 2^29 and limb 8 is below 2^23; an input
//!   below `2p` has limb 8 at most 2^23. Every limb, and every doubled limb in
//!   `sqr`, fits the 32-bit operands of `vpmuludq`.
//! - A column accumulates at most nine products below 2^60 (doubled cross
//!   products), five reduction terms below 2^58, and a carry below 2^35, so
//!   it stays below 2^64.
//!
//! A lane's value is the same integer modulo `p` as the scalar Montgomery
//! arithmetic computes, after the domain change at entry and exit.

#![allow(unsafe_code)]

use core::arch::x86_64::*;
use core::marker::PhantomData;

use super::pasta::PrimeModulus;

type Limbs = [u64; 4];

/// Field elements per vector.
pub(crate) const LANES: usize = 4;
/// Radix-2^29 limbs per field element.
const LIMBS: usize = 9;
/// Bits per limb.
const BITS: i32 = 29;
const MASK: u64 = (1 << BITS) - 1;
/// Both moduli's top limb is `2^TOP_LIMB_SHIFT`.
const TOP_LIMB_SHIFT: i32 = 22;
/// `log2` of this module's Montgomery radix `R'`.
const RADIX_BITS: usize = LIMBS * BITS as usize;
/// `log2` of the scalar kernels' Montgomery radix `R`.
const SCALAR_RADIX_BITS: usize = 256;

/// Four field elements, limb-major.
#[derive(Clone, Copy)]
struct Vector([__m256i; LIMBS]);

/// Converts a little-endian 256-bit integer to radix 2^29.
const fn to_radix29(x: &Limbs) -> [u64; LIMBS] {
    let mut out = [0u64; LIMBS];
    let mut i = 0;
    while i < LIMBS {
        let bit = i * BITS as usize;
        let (w, s) = (bit / 64, bit % 64);
        let mut v = x[w] >> s;
        if s + BITS as usize > 64 && w + 1 < 4 {
            v |= x[w + 1] << (64 - s);
        }
        out[i] = v & MASK;
        i += 1;
    }
    out
}

/// A modulus in radix 2^29, checked for the sparse shape that `mul` and `sqr`
/// assume.
const fn modulus_limbs<M: PrimeModulus>() -> [u64; LIMBS] {
    let l = to_radix29(&M::MODULUS);
    assert!(l[0] == 1 && l[5] == 0 && l[6] == 0 && l[7] == 0 && l[8] == 1 << TOP_LIMB_SHIFT);
    l
}

/// `2 * x mod p` for `x < p`.
const fn double_mod(x: &Limbs, p: &Limbs) -> Limbs {
    // p is below 2^255, so the doubled value fits four limbs.
    let mut doubled = [0u64; 4];
    let mut difference = [0u64; 4];
    let (mut carry, mut borrow) = (0, false);
    let mut i = 0;
    while i < 4 {
        doubled[i] = (x[i] << 1) | carry;
        carry = x[i] >> 63;
        let (low, first) = doubled[i].overflowing_sub(p[i]);
        let (low, second) = low.overflowing_sub(borrow as u64);
        difference[i] = low;
        borrow = first || second;
        i += 1;
    }
    assert!(carry == 0);
    if borrow { doubled } else { difference }
}

/// The integer that moves a scalar Montgomery residue `a * R` into this
/// module's domain: `mul` by `R'^2 / R mod p` gives `a * R'`.
const fn entry_factor<M: PrimeModulus>() -> Limbs {
    // R'^2 / R = R * 2^(2 * 261 - 2 * 256), and `M::R` is `R mod p`.
    let mut factor = M::R;
    let mut doublings = 2 * RADIX_BITS - 2 * SCALAR_RADIX_BITS;
    while doublings > 0 {
        factor = double_mod(&factor, &M::MODULUS);
        doublings -= 1;
    }
    factor
}

/// Lane-wise Montgomery product.
#[target_feature(enable = "avx2")]
#[inline]
fn mul<M: PrimeModulus>(a: &Vector, b: &Vector) -> Vector {
    let p = const { modulus_limbs::<M>() };
    let mask = _mm256_set1_epi64x(MASK as i64);
    let zero = _mm256_setzero_si256();
    let p1 = _mm256_set1_epi64x(p[1] as i64);
    let p2 = _mm256_set1_epi64x(p[2] as i64);
    let p3 = _mm256_set1_epi64x(p[3] as i64);
    let p4 = _mm256_set1_epi64x(p[4] as i64);
    let a = &a.0;
    let b = &b.0;
    let mut q = [zero; LIMBS];
    let mut out = [zero; LIMBS];
    let mut carry = zero;
    let col = _mm256_add_epi64(_mm256_mul_epu32(a[0], b[0]), carry);
    q[0] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[0]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(_mm256_mul_epu32(a[0], b[1]), _mm256_mul_epu32(a[1], b[0])),
        _mm256_add_epi64(_mm256_mul_epu32(q[0], p1), carry),
    );
    q[1] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[1]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(a[0], b[2]), _mm256_mul_epu32(a[1], b[1])),
            _mm256_add_epi64(_mm256_mul_epu32(a[2], b[0]), _mm256_mul_epu32(q[0], p2)),
        ),
        _mm256_add_epi64(_mm256_mul_epu32(q[1], p1), carry),
    );
    q[2] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[2]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(a[0], b[3]), _mm256_mul_epu32(a[1], b[2])),
            _mm256_add_epi64(_mm256_mul_epu32(a[2], b[1]), _mm256_mul_epu32(a[3], b[0])),
        ),
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(q[0], p3), _mm256_mul_epu32(q[1], p2)),
            _mm256_add_epi64(_mm256_mul_epu32(q[2], p1), carry),
        ),
    );
    q[3] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[3]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[0], b[4]), _mm256_mul_epu32(a[1], b[3])),
                _mm256_add_epi64(_mm256_mul_epu32(a[2], b[2]), _mm256_mul_epu32(a[3], b[1])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[4], b[0]), _mm256_mul_epu32(q[0], p4)),
                _mm256_add_epi64(_mm256_mul_epu32(q[1], p3), _mm256_mul_epu32(q[2], p2)),
            ),
        ),
        _mm256_add_epi64(_mm256_mul_epu32(q[3], p1), carry),
    );
    q[4] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[4]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[0], b[5]), _mm256_mul_epu32(a[1], b[4])),
                _mm256_add_epi64(_mm256_mul_epu32(a[2], b[3]), _mm256_mul_epu32(a[3], b[2])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[4], b[1]), _mm256_mul_epu32(a[5], b[0])),
                _mm256_add_epi64(_mm256_mul_epu32(q[1], p4), _mm256_mul_epu32(q[2], p3)),
            ),
        ),
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(q[3], p2), _mm256_mul_epu32(q[4], p1)),
            carry,
        ),
    );
    q[5] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[5]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[0], b[6]), _mm256_mul_epu32(a[1], b[5])),
                _mm256_add_epi64(_mm256_mul_epu32(a[2], b[4]), _mm256_mul_epu32(a[3], b[3])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[4], b[2]), _mm256_mul_epu32(a[5], b[1])),
                _mm256_add_epi64(_mm256_mul_epu32(a[6], b[0]), _mm256_mul_epu32(q[2], p4)),
            ),
        ),
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(q[3], p3), _mm256_mul_epu32(q[4], p2)),
            _mm256_add_epi64(_mm256_mul_epu32(q[5], p1), carry),
        ),
    );
    q[6] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[6]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[0], b[7]), _mm256_mul_epu32(a[1], b[6])),
                _mm256_add_epi64(_mm256_mul_epu32(a[2], b[5]), _mm256_mul_epu32(a[3], b[4])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[4], b[3]), _mm256_mul_epu32(a[5], b[2])),
                _mm256_add_epi64(_mm256_mul_epu32(a[6], b[1]), _mm256_mul_epu32(a[7], b[0])),
            ),
        ),
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(q[3], p4), _mm256_mul_epu32(q[4], p3)),
                _mm256_add_epi64(_mm256_mul_epu32(q[5], p2), _mm256_mul_epu32(q[6], p1)),
            ),
            carry,
        ),
    );
    q[7] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[7]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[0], b[8]), _mm256_mul_epu32(a[1], b[7])),
                _mm256_add_epi64(_mm256_mul_epu32(a[2], b[6]), _mm256_mul_epu32(a[3], b[5])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[4], b[4]), _mm256_mul_epu32(a[5], b[3])),
                _mm256_add_epi64(_mm256_mul_epu32(a[6], b[2]), _mm256_mul_epu32(a[7], b[1])),
            ),
        ),
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(
                    _mm256_mul_epu32(a[8], b[0]),
                    _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[0]),
                ),
                _mm256_add_epi64(_mm256_mul_epu32(q[4], p4), _mm256_mul_epu32(q[5], p3)),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(q[6], p2), _mm256_mul_epu32(q[7], p1)),
                carry,
            ),
        ),
    );
    q[8] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[8]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[1], b[8]), _mm256_mul_epu32(a[2], b[7])),
                _mm256_add_epi64(_mm256_mul_epu32(a[3], b[6]), _mm256_mul_epu32(a[4], b[5])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[5], b[4]), _mm256_mul_epu32(a[6], b[3])),
                _mm256_add_epi64(_mm256_mul_epu32(a[7], b[2]), _mm256_mul_epu32(a[8], b[1])),
            ),
        ),
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(
                    _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[1]),
                    _mm256_mul_epu32(q[5], p4),
                ),
                _mm256_add_epi64(_mm256_mul_epu32(q[6], p3), _mm256_mul_epu32(q[7], p2)),
            ),
            _mm256_add_epi64(_mm256_mul_epu32(q[8], p1), carry),
        ),
    );
    out[0] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[2], b[8]), _mm256_mul_epu32(a[3], b[7])),
                _mm256_add_epi64(_mm256_mul_epu32(a[4], b[6]), _mm256_mul_epu32(a[5], b[5])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[6], b[4]), _mm256_mul_epu32(a[7], b[3])),
                _mm256_add_epi64(
                    _mm256_mul_epu32(a[8], b[2]),
                    _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[2]),
                ),
            ),
        ),
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(q[6], p4), _mm256_mul_epu32(q[7], p3)),
            _mm256_add_epi64(_mm256_mul_epu32(q[8], p2), carry),
        ),
    );
    out[1] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[3], b[8]), _mm256_mul_epu32(a[4], b[7])),
                _mm256_add_epi64(_mm256_mul_epu32(a[5], b[6]), _mm256_mul_epu32(a[6], b[5])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[7], b[4]), _mm256_mul_epu32(a[8], b[3])),
                _mm256_add_epi64(
                    _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[3]),
                    _mm256_mul_epu32(q[7], p4),
                ),
            ),
        ),
        _mm256_add_epi64(_mm256_mul_epu32(q[8], p3), carry),
    );
    out[2] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(a[4], b[8]), _mm256_mul_epu32(a[5], b[7])),
            _mm256_add_epi64(_mm256_mul_epu32(a[6], b[6]), _mm256_mul_epu32(a[7], b[5])),
        ),
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_mul_epu32(a[8], b[4]),
                _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[4]),
            ),
            _mm256_add_epi64(_mm256_mul_epu32(q[8], p4), carry),
        ),
    );
    out[3] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(a[5], b[8]), _mm256_mul_epu32(a[6], b[7])),
            _mm256_add_epi64(_mm256_mul_epu32(a[7], b[6]), _mm256_mul_epu32(a[8], b[5])),
        ),
        _mm256_add_epi64(_mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[5]), carry),
    );
    out[4] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(a[6], b[8]), _mm256_mul_epu32(a[7], b[7])),
            _mm256_add_epi64(
                _mm256_mul_epu32(a[8], b[6]),
                _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[6]),
            ),
        ),
        carry,
    );
    out[5] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(_mm256_mul_epu32(a[7], b[8]), _mm256_mul_epu32(a[8], b[7])),
        _mm256_add_epi64(_mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[7]), carry),
    );
    out[6] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_mul_epu32(a[8], b[8]),
            _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[8]),
        ),
        carry,
    );
    out[7] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    out[8] = carry;
    Vector(out)
}

/// Lane-wise Montgomery square.
#[target_feature(enable = "avx2")]
#[inline]
fn sqr<M: PrimeModulus>(a: &Vector) -> Vector {
    let p = const { modulus_limbs::<M>() };
    let mask = _mm256_set1_epi64x(MASK as i64);
    let zero = _mm256_setzero_si256();
    let p1 = _mm256_set1_epi64x(p[1] as i64);
    let p2 = _mm256_set1_epi64x(p[2] as i64);
    let p3 = _mm256_set1_epi64x(p[3] as i64);
    let p4 = _mm256_set1_epi64x(p[4] as i64);
    let a = &a.0;
    let d: [__m256i; LIMBS] = core::array::from_fn(|i| _mm256_add_epi64(a[i], a[i]));
    let mut q = [zero; LIMBS];
    let mut out = [zero; LIMBS];
    let mut carry = zero;
    let col = _mm256_add_epi64(_mm256_mul_epu32(a[0], a[0]), carry);
    q[0] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[0]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(_mm256_mul_epu32(a[0], d[1]), _mm256_mul_epu32(q[0], p1)),
        carry,
    );
    q[1] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[1]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(a[0], d[2]), _mm256_mul_epu32(a[1], a[1])),
            _mm256_add_epi64(_mm256_mul_epu32(q[0], p2), _mm256_mul_epu32(q[1], p1)),
        ),
        carry,
    );
    q[2] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[2]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(a[0], d[3]), _mm256_mul_epu32(a[1], d[2])),
            _mm256_add_epi64(_mm256_mul_epu32(q[0], p3), _mm256_mul_epu32(q[1], p2)),
        ),
        _mm256_add_epi64(_mm256_mul_epu32(q[2], p1), carry),
    );
    q[3] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[3]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(a[0], d[4]), _mm256_mul_epu32(a[1], d[3])),
            _mm256_add_epi64(_mm256_mul_epu32(a[2], a[2]), _mm256_mul_epu32(q[0], p4)),
        ),
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(q[1], p3), _mm256_mul_epu32(q[2], p2)),
            _mm256_add_epi64(_mm256_mul_epu32(q[3], p1), carry),
        ),
    );
    q[4] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[4]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(a[0], d[5]), _mm256_mul_epu32(a[1], d[4])),
            _mm256_add_epi64(_mm256_mul_epu32(a[2], d[3]), _mm256_mul_epu32(q[1], p4)),
        ),
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(q[2], p3), _mm256_mul_epu32(q[3], p2)),
            _mm256_add_epi64(_mm256_mul_epu32(q[4], p1), carry),
        ),
    );
    q[5] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[5]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[0], d[6]), _mm256_mul_epu32(a[1], d[5])),
                _mm256_add_epi64(_mm256_mul_epu32(a[2], d[4]), _mm256_mul_epu32(a[3], a[3])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(q[2], p4), _mm256_mul_epu32(q[3], p3)),
                _mm256_add_epi64(_mm256_mul_epu32(q[4], p2), _mm256_mul_epu32(q[5], p1)),
            ),
        ),
        carry,
    );
    q[6] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[6]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[0], d[7]), _mm256_mul_epu32(a[1], d[6])),
                _mm256_add_epi64(_mm256_mul_epu32(a[2], d[5]), _mm256_mul_epu32(a[3], d[4])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(q[3], p4), _mm256_mul_epu32(q[4], p3)),
                _mm256_add_epi64(_mm256_mul_epu32(q[5], p2), _mm256_mul_epu32(q[6], p1)),
            ),
        ),
        carry,
    );
    q[7] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[7]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[0], d[8]), _mm256_mul_epu32(a[1], d[7])),
                _mm256_add_epi64(_mm256_mul_epu32(a[2], d[6]), _mm256_mul_epu32(a[3], d[5])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(
                    _mm256_mul_epu32(a[4], a[4]),
                    _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[0]),
                ),
                _mm256_add_epi64(_mm256_mul_epu32(q[4], p4), _mm256_mul_epu32(q[5], p3)),
            ),
        ),
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(q[6], p2), _mm256_mul_epu32(q[7], p1)),
            carry,
        ),
    );
    q[8] = _mm256_and_si256(_mm256_sub_epi64(zero, col), mask);
    carry = _mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[8]));
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[1], d[8]), _mm256_mul_epu32(a[2], d[7])),
                _mm256_add_epi64(_mm256_mul_epu32(a[3], d[6]), _mm256_mul_epu32(a[4], d[5])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(
                    _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[1]),
                    _mm256_mul_epu32(q[5], p4),
                ),
                _mm256_add_epi64(_mm256_mul_epu32(q[6], p3), _mm256_mul_epu32(q[7], p2)),
            ),
        ),
        _mm256_add_epi64(_mm256_mul_epu32(q[8], p1), carry),
    );
    out[0] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(
                _mm256_add_epi64(_mm256_mul_epu32(a[2], d[8]), _mm256_mul_epu32(a[3], d[7])),
                _mm256_add_epi64(_mm256_mul_epu32(a[4], d[6]), _mm256_mul_epu32(a[5], a[5])),
            ),
            _mm256_add_epi64(
                _mm256_add_epi64(
                    _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[2]),
                    _mm256_mul_epu32(q[6], p4),
                ),
                _mm256_add_epi64(_mm256_mul_epu32(q[7], p3), _mm256_mul_epu32(q[8], p2)),
            ),
        ),
        carry,
    );
    out[1] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(a[3], d[8]), _mm256_mul_epu32(a[4], d[7])),
            _mm256_add_epi64(
                _mm256_mul_epu32(a[5], d[6]),
                _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[3]),
            ),
        ),
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(q[7], p4), _mm256_mul_epu32(q[8], p3)),
            carry,
        ),
    );
    out[2] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(a[4], d[8]), _mm256_mul_epu32(a[5], d[7])),
            _mm256_add_epi64(
                _mm256_mul_epu32(a[6], a[6]),
                _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[4]),
            ),
        ),
        _mm256_add_epi64(_mm256_mul_epu32(q[8], p4), carry),
    );
    out[3] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(_mm256_mul_epu32(a[5], d[8]), _mm256_mul_epu32(a[6], d[7])),
        _mm256_add_epi64(_mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[5]), carry),
    );
    out[4] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(_mm256_mul_epu32(a[6], d[8]), _mm256_mul_epu32(a[7], a[7])),
        _mm256_add_epi64(_mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[6]), carry),
    );
    out[5] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_mul_epu32(a[7], d[8]),
            _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[7]),
        ),
        carry,
    );
    out[6] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    let col = _mm256_add_epi64(
        _mm256_add_epi64(
            _mm256_mul_epu32(a[8], a[8]),
            _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q[8]),
        ),
        carry,
    );
    out[7] = _mm256_and_si256(col, mask);
    carry = _mm256_srli_epi64::<BITS>(col);
    out[8] = carry;
    Vector(out)
}

/// Packs four little-endian 256-bit integers.
#[target_feature(enable = "avx2")]
#[inline]
fn pack(x: &[Limbs; LANES]) -> Vector {
    let l = [
        to_radix29(&x[0]),
        to_radix29(&x[1]),
        to_radix29(&x[2]),
        to_radix29(&x[3]),
    ];
    let mut v = [_mm256_setzero_si256(); LIMBS];
    for (i, limb) in v.iter_mut().enumerate() {
        *limb = _mm256_set_epi64x(
            l[3][i] as i64,
            l[2][i] as i64,
            l[1][i] as i64,
            l[0][i] as i64,
        );
    }
    Vector(v)
}

/// Unpacks four integers; limbs 0 to 7 must be below 2^29 (as `mul` and `sqr`
/// leave them).
#[target_feature(enable = "avx2")]
#[inline]
fn unpack(v: &Vector) -> [Limbs; LANES] {
    let mut limbs = [[0u64; LANES]; LIMBS];
    for (dst, src) in limbs.iter_mut().zip(&v.0) {
        // SAFETY: stores exactly the 32 bytes of the `[u64; 4]` behind `dst`.
        unsafe { _mm256_storeu_si256(dst.as_mut_ptr().cast(), *src) };
    }
    let mut out = [[0u64; 4]; LANES];
    for (lane, out) in out.iter_mut().enumerate() {
        for (i, limb) in limbs.iter().enumerate() {
            let bit = i * BITS as usize;
            let (w, s) = (bit / 64, bit % 64);
            let x = limb[lane];
            out[w] |= x << s;
            if s + BITS as usize > 64 && w + 1 < 4 {
                out[w + 1] |= x >> (64 - s);
            }
        }
    }
    out
}

/// Squares every lane of every vector `count` times.
///
/// The vectors advance together, so their independent dependency chains
/// overlap as the scalar lane kernels' do.
#[target_feature(enable = "avx2")]
fn square_run<M: PrimeModulus, const G: usize>(vectors: &mut [Vector; G], count: usize) {
    for _ in 0..count {
        for vector in vectors.iter_mut() {
            *vector = sqr::<M>(vector);
        }
    }
}

/// Multiplies every lane of `vectors` by the matching lane of `factors`.
#[target_feature(enable = "avx2")]
fn multiply<M: PrimeModulus, const G: usize>(vectors: &mut [Vector; G], factors: &[Vector; G]) {
    for (vector, factor) in vectors.iter_mut().zip(factors) {
        *vector = mul::<M>(vector, factor);
    }
}

/// Moves scalar Montgomery limbs below `2p` into this module's domain.
#[target_feature(enable = "avx2")]
fn enter<M: PrimeModulus, const G: usize>(values: &[[Limbs; LANES]; G]) -> [Vector; G] {
    let factor = pack(&[const { entry_factor::<M>() }; LANES]);
    let mut vectors = [factor; G];
    for (vector, lanes) in vectors.iter_mut().zip(values) {
        *vector = mul::<M>(&pack(lanes), &factor);
    }
    vectors
}

/// Returns scalar Montgomery limbs below `2p`.
#[target_feature(enable = "avx2")]
fn leave<M: PrimeModulus, const G: usize>(vectors: &[Vector; G]) -> [[Limbs; LANES]; G] {
    // `mul` by `R mod p` divides out `R'` and leaves the scalar radix.
    let factor = pack(&[M::R; LANES]);
    let mut values = [[[0u64; 4]; LANES]; G];
    for (lanes, vector) in values.iter_mut().zip(vectors) {
        *lanes = unpack(&mul::<M>(vector, &factor));
    }
    values
}

/// The multiplicative interpretation of an addition chain on `4 * G` lanes:
/// doubling squares every lane, and addition multiplies lane by lane.
///
/// [`Self::enter`] and [`Self::leave`] change between the scalar kernels'
/// Montgomery limbs and this module's representation, so a caller runs a
/// chain without seeing the latter.
pub(crate) struct PowerVectors<M: PrimeModulus, const G: usize> {
    vectors: [Vector; G],
    marker: PhantomData<M>,
}

impl<M: PrimeModulus, const G: usize> Clone for PowerVectors<M, G> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            vectors: self.vectors,
            marker: PhantomData,
        }
    }
}

impl<M: PrimeModulus, const G: usize> PowerVectors<M, G> {
    /// Loads `G` groups of four scalar Montgomery residues, each below `2p`.
    #[inline]
    pub(crate) fn enter(values: &[[Limbs; LANES]; G]) -> Self {
        Self {
            // SAFETY: this module is compiled only for CPUs with AVX2.
            vectors: unsafe { enter::<M, G>(values) },
            marker: PhantomData,
        }
    }

    /// Returns every lane as scalar Montgomery limbs below `2p`.
    #[inline]
    pub(crate) fn leave(&self) -> [[Limbs; LANES]; G] {
        // SAFETY: this module is compiled only for CPUs with AVX2.
        unsafe { leave::<M, G>(&self.vectors) }
    }
}

// Each step is one call into an AVX2 function that keeps its whole loop
// there: a caller compiled without AVX2 cannot inline the kernels, so finer
// steps would move every vector through memory once per squaring.
impl<M: PrimeModulus, const G: usize> bento::addchain::AdditionChain for PowerVectors<M, G> {
    #[inline]
    fn double(&self) -> Self {
        self.double_n(1)
    }

    #[inline]
    fn add(&self, rhs: &Self) -> Self {
        let mut product = self.clone();
        // SAFETY: this module is compiled only for CPUs with AVX2.
        unsafe { multiply::<M, G>(&mut product.vectors, &rhs.vectors) };
        product
    }

    #[inline]
    fn double_n(&self, count: usize) -> Self {
        let mut power = self.clone();
        // SAFETY: this module is compiled only for CPUs with AVX2.
        unsafe { square_run::<M, G>(&mut power.vectors, count) };
        power
    }

    #[inline]
    fn double_n_add(&self, count: usize, rhs: &Self) -> Self {
        let mut power = self.clone();
        // SAFETY: this module is compiled only for CPUs with AVX2.
        unsafe {
            square_run::<M, G>(&mut power.vectors, count);
            multiply::<M, G>(&mut power.vectors, &rhs.vectors);
        }
        power
    }
}
