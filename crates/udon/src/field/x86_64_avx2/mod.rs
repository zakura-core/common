//! Four-lane AVX2 arithmetic for both Pasta fields, in radix 2^29.
//!
//! A serial chain of field squarings already saturates the x86-64 integer
//! multiplier, so interleaving scalar chains gains little there. This module
//! instead holds four field elements in one set of AVX2 registers, one element
//! per 64-bit lane, and squares or multiplies all four with `vpmuludq`. It
//! serves the exponentiation behind square roots (and so point decoding)
//! through [`PowerVectors`], and the affine additions of one level of a
//! bucket's pair tree through [`chord_level`]. Those two are its interfaces,
//! and no radix-2^29 value leaves the module.
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

// Affine chord additions.
//
// The values of this section stay in the scalar kernels' Montgomery domain.
// `mul` computes `a * b / 2^261` where the scalar product divides by `2^256`,
// so scaling one operand of each product by `2^5` (`shl5`) makes `mul` the
// scalar Montgomery product, and no value is converted on the way in or out.
//
// `mul` is exact whenever limbs 0 to 7 of both inputs are below 2^29 and both
// values are below 2^261; its result is below `a * b / 2^261 + p`. Both moduli
// are `2^254 + d` with `d < 2^126`, so `p / 2^261` exceeds `1 / 128` by a
// factor below `1 + 2^-128`, which the bounds stated below absorb. Subtraction
// adds a multiple of `p` whose limbs dominate the subtrahend's
// (`dominating_multiple`), so no limb goes negative, and every value stored or
// returned is first reduced to `[0, p)` (`canonical`).

/// Chord additions in flight: two vectors of four lanes, whose independent
/// multiplication chains overlap.
const CHORD_VECTORS: usize = 2;
/// Additions per chunk of [`chord_level`].
pub(crate) const CHORD_LANES: usize = LANES * CHORD_VECTORS;
/// `2^SCALE_SHIFT` is the scale that makes `mul` the scalar Montgomery
/// product: this module's radix over the scalar kernels'.
const SCALE_SHIFT: i32 = (RADIX_BITS - SCALAR_RADIX_BITS) as i32;

/// `c * p` in radix 2^29, with limbs 0 to 7 raised to at least `2^30 - 2` by
/// borrowing from the next limb, so it dominates limb by limb any normalized
/// subtrahend whose limb 8 is at most `c * 2^22 - 2`.
///
/// Each limb is computed in one expression, adding the `2^30` it receives
/// before subtracting the `2` it lends: limbs 5 to 7 of both moduli are zero,
/// so borrowing first would underflow.
const fn dominating_multiple<M: PrimeModulus>(c: u64) -> [u64; LIMBS] {
    let p = modulus_limbs::<M>();
    let mut k = [0u64; LIMBS];
    let mut i = 0;
    while i < LIMBS {
        let received = if i < LIMBS - 1 { 1 << (BITS + 1) } else { 0 };
        let lent = if i > 0 { 2 } else { 0 };
        k[i] = c * p[i] + received - lent;
        i += 1;
    }
    k
}

/// The scalar Montgomery limbs of `2^SCALE_SHIFT`.
const fn montgomery_scale<M: PrimeModulus>() -> Limbs {
    let mut value = M::R;
    let mut doublings = SCALE_SHIFT;
    while doublings > 0 {
        value = double_mod(&value, &M::MODULUS);
        doublings -= 1;
    }
    value
}

/// Propagates carries so limbs 0 to 7 are below 2^29.
#[target_feature(enable = "avx2")]
#[inline]
fn normalize(mut v: [__m256i; LIMBS]) -> Vector {
    let mask = _mm256_set1_epi64x(MASK as i64);
    for i in 0..LIMBS - 1 {
        let carry = _mm256_srli_epi64::<BITS>(v[i]);
        v[i] = _mm256_and_si256(v[i], mask);
        v[i + 1] = _mm256_add_epi64(v[i + 1], carry);
    }
    Vector(v)
}

/// `2^SCALE_SHIFT * a`.
#[target_feature(enable = "avx2")]
#[inline]
fn shl5(a: &Vector) -> Vector {
    normalize(core::array::from_fn(|i| {
        _mm256_slli_epi64::<SCALE_SHIFT>(a.0[i])
    }))
}

/// `a + b`, for normalized `a` and `b`.
#[target_feature(enable = "avx2")]
#[inline]
fn add(a: &Vector, b: &Vector) -> Vector {
    normalize(core::array::from_fn(|i| _mm256_add_epi64(a.0[i], b.0[i])))
}

/// `a + k - b`, for `k` from [`dominating_multiple`] dominating `b`.
#[target_feature(enable = "avx2")]
#[inline]
fn sub(a: &Vector, b: &Vector, k: &[u64; LIMBS]) -> Vector {
    normalize(core::array::from_fn(|i| {
        _mm256_sub_epi64(
            _mm256_add_epi64(a.0[i], _mm256_set1_epi64x(k[i] as i64)),
            b.0[i],
        )
    }))
}

/// Reduces a normalized value below `8p` (limb 8 at most `2^25`: `8p` exceeds
/// `2^257`) to `[0, p)`.
///
/// `q = floor(v / 2^254)` is `limb 8 >> 22`; `v - q * p` lies in `[-p, p)`
/// because `2^254 < p < 2^254 + 2^128`, so at most one `p` is added back.
/// Limbs 0 to 7 get `2^32` added (borrowed as 8 from the next limb), so they
/// stay non-negative for the logical carry shifts; only limb 8 carries the
/// sign.
#[target_feature(enable = "avx2")]
#[inline]
fn canonical<M: PrimeModulus>(v: &Vector) -> Vector {
    let p = const { modulus_limbs::<M>() };
    let q = _mm256_srli_epi64::<TOP_LIMB_SHIFT>(v.0[LIMBS - 1]);
    let mut t: [__m256i; LIMBS] = core::array::from_fn(|i| {
        let qp = match i {
            0 => q,
            8 => _mm256_slli_epi64::<TOP_LIMB_SHIFT>(q),
            _ => _mm256_mul_epu32(q, _mm256_set1_epi64x(p[i] as i64)),
        };
        let offset: i64 = match i {
            0 => 1 << 32,
            8 => -8,
            _ => (1 << 32) - 8,
        };
        _mm256_sub_epi64(_mm256_add_epi64(v.0[i], _mm256_set1_epi64x(offset)), qp)
    });
    t = normalize(t).0;
    let negative = _mm256_cmpgt_epi64(_mm256_setzero_si256(), t[LIMBS - 1]);
    for (i, t) in t.iter_mut().enumerate() {
        *t = _mm256_add_epi64(
            *t,
            _mm256_and_si256(negative, _mm256_set1_epi64x(p[i] as i64)),
        );
    }
    normalize(t)
}

/// Exchanges rows and columns of four 256-bit values: output `k` holds word
/// `k` of each input, and the map is its own inverse.
#[target_feature(enable = "avx2")]
#[inline]
fn transpose(v: [__m256i; 4]) -> [__m256i; 4] {
    let low01 = _mm256_unpacklo_epi64(v[0], v[1]);
    let high01 = _mm256_unpackhi_epi64(v[0], v[1]);
    let low23 = _mm256_unpacklo_epi64(v[2], v[3]);
    let high23 = _mm256_unpackhi_epi64(v[2], v[3]);
    [
        _mm256_permute2x128_si256::<0x20>(low01, low23),
        _mm256_permute2x128_si256::<0x20>(high01, high23),
        _mm256_permute2x128_si256::<0x31>(low01, low23),
        _mm256_permute2x128_si256::<0x31>(high01, high23),
    ]
}

/// Loads four little-endian 256-bit integers, one per lane.
///
/// A radix-2^29 limb is a bit slice of the integer, so the words are
/// transposed into lanes and split with shifts; nothing is stored in radix
/// 2^29.
#[target_feature(enable = "avx2")]
#[inline]
fn load4(values: [&Limbs; LANES]) -> Vector {
    // SAFETY: each load reads exactly the 32 bytes of one `[u64; 4]`.
    let words = transpose(values.map(|value| unsafe { _mm256_loadu_si256(value.as_ptr().cast()) }));
    let mask = _mm256_set1_epi64x(MASK as i64);
    Vector(core::array::from_fn(|i| {
        let bit = i * BITS as usize;
        let (word, shift) = (bit / 64, (bit % 64) as i64);
        let mut limb = _mm256_srl_epi64(words[word], _mm_cvtsi64_si128(shift));
        if shift + BITS as i64 > 64 && word + 1 < 4 {
            limb = _mm256_or_si256(
                limb,
                _mm256_sll_epi64(words[word + 1], _mm_cvtsi64_si128(64 - shift)),
            );
        }
        _mm256_and_si256(limb, mask)
    }))
}

/// Stores four values below 2^256 with limbs 0 to 7 below 2^29 (as
/// [`canonical`] leaves them) as little-endian 256-bit integers.
#[target_feature(enable = "avx2")]
#[inline]
fn store4(v: &Vector) -> [Limbs; LANES] {
    let mut words = [_mm256_setzero_si256(); 4];
    for (i, limb) in v.0.iter().enumerate() {
        let bit = i * BITS as usize;
        let (word, shift) = (bit / 64, (bit % 64) as i64);
        words[word] = _mm256_or_si256(
            words[word],
            _mm256_sll_epi64(*limb, _mm_cvtsi64_si128(shift)),
        );
        if shift + BITS as i64 > 64 && word + 1 < 4 {
            words[word + 1] = _mm256_or_si256(
                words[word + 1],
                _mm256_srl_epi64(*limb, _mm_cvtsi64_si128(64 - shift)),
            );
        }
    }
    let mut out = [[0u64; 4]; LANES];
    for (out, value) in out.iter_mut().zip(transpose(words)) {
        // SAFETY: stores exactly the 32 bytes of one `[u64; 4]`.
        unsafe { _mm256_storeu_si256(out.as_mut_ptr().cast(), value) };
    }
    out
}

/// The left and right operand of one chord addition, as canonical scalar
/// Montgomery limbs: `[left x, left y, right x, right y]`.
pub(crate) type ChordOperands = [Limbs; 4];

/// The points, scratch, and field inversion of one [`chord_level`], which the
/// caller owns; every value crossing this interface is a canonical residue in
/// scalar Montgomery limbs.
pub(crate) trait ChordStorage {
    /// The operands of addition `pair`.
    fn operands(&self, pair: usize) -> ChordOperands;
    /// Receives the sum of addition `pair`.
    fn emit(&mut self, pair: usize, x: Limbs, y: Limbs);
    /// Returns the value last given to [`Self::set_scratch`] for `pair`.
    fn scratch(&self, pair: usize) -> Limbs;
    /// Keeps one value per addition between the level's two passes.
    fn set_scratch(&mut self, pair: usize, value: Limbs);
    /// Replaces eight nonzero residues by [`chord_inverse_scale`] times their
    /// inverses, or returns `false` if one of them is zero: the level's one
    /// field inversion, which the scalar kernels supply.
    fn invert(&mut self, lanes: &mut [Limbs; CHORD_LANES]) -> bool;
}

/// One level of affine chord additions: `storage` receives the sum of the
/// operands of every pair below `pairs`, in increasing order.
///
/// The x-coordinates of each pair must differ. When some pair's do not, this
/// returns `false` before the first [`ChordStorage::emit`]; the caller then
/// takes a path that handles doublings and cancellations.
///
/// Pair `i`'s operands are read twice, both times before its own sum is
/// emitted and before the sum of any pair from `i + LANES` on, so sum `i` may
/// overwrite operands `2i` and `2i + 1` of one array.
///
/// The lane products run from the last chunk to the first so that the sums
/// are recovered first to last. Bounds: differences are below `3p` and their
/// scaled forms below `96p < 2^261`; lane products, scaled numerators and
/// running inverses stay below `4.01p` (a bound `B p` becomes at most
/// `96 B p^2 / 2^261 + p`, whose fixed point exceeds `4p` by less than
/// `2^-120 p`); the slope is below `1.126p`, `x3` below `4.32p`, `x - x3`
/// below `6p`, and `y3` below `4.69p`.
#[target_feature(enable = "avx2")]
fn chord_level_avx2<M: PrimeModulus, S: ChordStorage>(pairs: usize, storage: &mut S) -> bool {
    let k2 = const { dominating_multiple::<M>(2) };
    let k3 = const { dominating_multiple::<M>(3) };
    let k5 = const { dominating_multiple::<M>(5) };
    // A padding lane adds (1, 0) and (0, 0): its difference, -1, is a unit,
    // so it leaves the lane product invertible, and its sum is never emitted.
    let padding: ChordOperands = [M::R, [0; 4], [0; 4], [0; 4]];
    let group = |storage: &S, first: usize| -> [ChordOperands; LANES] {
        core::array::from_fn(|lane| {
            if first + lane < pairs {
                storage.operands(first + lane)
            } else {
                padding
            }
        })
    };
    let coordinate = |group: &[ChordOperands; LANES], index: usize| -> Vector {
        load4(core::array::from_fn(|lane| &group[lane][index]))
    };
    let chunks = pairs.div_ceil(CHORD_LANES);

    let mut products = [pack(&[const { montgomery_scale::<M>() }; LANES]); CHORD_VECTORS];
    for chunk in (0..chunks).rev() {
        for (vector, product) in products.iter_mut().enumerate() {
            let first = chunk * CHORD_LANES + vector * LANES;
            let group = group(storage, first);
            let (lx, ly) = (coordinate(&group, 0), coordinate(&group, 1));
            let (rx, ry) = (coordinate(&group, 2), coordinate(&group, 3));
            let numerator = shl5(&sub(&ry, &ly, &k2));
            let denominator = shl5(&sub(&rx, &lx, &k2));
            let scaled = store4(&canonical::<M>(&mul::<M>(&numerator, product)));
            *product = mul::<M>(product, &denominator);
            for (lane, scaled) in scaled.iter().enumerate() {
                if first + lane < pairs {
                    storage.set_scratch(first + lane, *scaled);
                }
            }
        }
    }

    let mut inverses = [[0u64; 4]; CHORD_LANES];
    for (vector, product) in products.iter().enumerate() {
        inverses[vector * LANES..][..LANES].copy_from_slice(&store4(&canonical::<M>(product)));
    }
    if !storage.invert(&mut inverses) {
        return false;
    }
    let mut inverses: [Vector; CHORD_VECTORS] = core::array::from_fn(|vector| {
        load4(core::array::from_fn(|lane| {
            &inverses[vector * LANES + lane]
        }))
    });

    for chunk in 0..chunks {
        for (vector, inverse) in inverses.iter_mut().enumerate() {
            let first = chunk * CHORD_LANES + vector * LANES;
            let group = group(storage, first);
            let (lx, ly, rx) = (
                coordinate(&group, 0),
                coordinate(&group, 1),
                coordinate(&group, 2),
            );
            let denominator = shl5(&sub(&rx, &lx, &k2));
            let scaled: [Limbs; LANES] = core::array::from_fn(|lane| {
                if first + lane < pairs {
                    storage.scratch(first + lane)
                } else {
                    [0; 4]
                }
            });
            let scaled = load4(core::array::from_fn(|lane| &scaled[lane]));
            let slope = mul::<M>(&scaled, inverse);
            *inverse = mul::<M>(inverse, &denominator);
            let slope_scaled = shl5(&slope);
            let x3 = sub(&mul::<M>(&slope, &slope_scaled), &add(&lx, &rx), &k3);
            let y3 = sub(&mul::<M>(&slope_scaled, &sub(&lx, &x3, &k5)), &ly, &k2);
            let xs = store4(&canonical::<M>(&x3));
            let ys = store4(&canonical::<M>(&y3));
            for lane in 0..LANES {
                if first + lane < pairs {
                    storage.emit(first + lane, xs[lane], ys[lane]);
                }
            }
        }
    }
    true
}

/// [`chord_level_avx2`], callable from code compiled without AVX2.
#[inline]
pub(crate) fn chord_level<M: PrimeModulus, S: ChordStorage>(pairs: usize, storage: &mut S) -> bool {
    // SAFETY: this module is compiled only for CPUs with AVX2.
    unsafe { chord_level_avx2::<M, S>(pairs, storage) }
}

/// The scale [`ChordStorage::invert`] applies to each inverse, as scalar
/// Montgomery limbs.
pub(crate) const fn chord_inverse_scale<M: PrimeModulus>() -> Limbs {
    montgomery_scale::<M>()
}
