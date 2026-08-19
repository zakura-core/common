//! GLV (Gallant–Lambert–Vanstone) scalar multiplication for the Pasta curves.
//!
//! Both Pasta curves carry a cube-root endomorphism
//! $\phi(x, y) = (\zeta x, y)$ (exposed as [`CurveExt::endo`]), for which
//! $\phi(P) = \lambda P$ with $\lambda$ = `Scalar::ZETA`. This module uses that
//! structure to split a full-width scalar multiplication $k P$ into two
//! half-width multiplications evaluated against a shared table of odd multiples
//! of $P$ and $\phi(P)$.
//!
//! This path is variable-time in the scalar (GLV decomposition plus wNAF
//! recoding); the `_glv` naming distinguishes it from the native `Mul`
//! implementations, which are unchanged.
//!
//! # References
//!
//! - R. P. Gallant, R. J. Lambert, S. A. Vanstone, "Faster Point Multiplication
//!   on Elliptic Curves with Efficient Endomorphisms", CRYPTO 2001.
//!   <https://www.iacr.org/archive/crypto2001/21390189.pdf>
//! - S. Bowe, J. Grigg, D. Hopwood, "Halo: Recursive Proof Composition without
//!   a Trusted Setup", <https://eprint.iacr.org/2019/1021> (see the GLV section).
//!
//! # Amortization
//!
//! The costs split into three independently reusable pieces:
//!
//! - [`Table`]: per *point*. [`Table::batch`] builds many tables with one
//!   shared batch normalization (a single field inversion for the whole
//!   batch).
//! - [`Decomposed`]: per *scalar*. Decomposition and wNAF recoding are
//!   hoisted so one scalar can be multiplied against many tables.
//! - [`Table::mul_decomposed`]: the remaining per-(point, scalar) work — a
//!   shared-doubling Straus ladder over the two half-width digit strings.
//!
//! One-shot use is [`GlvParams::mul_glv`].

use alloc::vec::Vec;

#[cfg(test)]
use ff::WithSmallOrderMulGroup;
use ff::{Field, PrimeField};
use group::prime::PrimeCurveAffine;
#[cfg(feature = "multicore")]
use maybe_rayon::prelude::*;

use crate::arithmetic::{adc, mac, sbb, CurveExt};
#[cfg(feature = "deferred")]
use crate::deferred::DeferredField;
use crate::{pallas, vesta};

mod private {
    /// Seals [`super::GlvParams`]: the lattice constants are curve-specific
    /// and verified in-crate; external implementations are not supported.
    pub trait Sealed {}
    impl Sealed for crate::pallas::Point {}
    impl Sealed for crate::vesta::Point {}
}

/// Per-curve GLV constants: a short basis for the lattice
/// $\{(a, b) : a + b\lambda \equiv 0 \pmod n\}$ — where $n$ is the order of the
/// group (equivalently the scalar field modulus) and $\lambda$ = `Scalar::ZETA`
/// — together with the Babai rounding coefficients derived from that basis.
///
/// This trait is sealed; it is implemented for [`pallas::Point`] and
/// [`vesta::Point`].
pub trait GlvParams: CurveExt + private::Sealed {
    /// First short lattice vector `v1 = (V1A, -V1B_NEG)`.
    const V1A: u128;
    /// Magnitude of `v1`'s (negative) second component.
    const V1B_NEG: u128;
    /// Second short lattice vector `v2 = (V2A, V2B)`.
    const V2A: u128;
    /// `v2`'s (positive) second component.
    const V2B: u128;
    /// Babai coefficient `round(2^384 * V2B / n)`, little-endian limbs.
    const G1: [u64; 5];
    /// Babai coefficient `round(2^384 * V1B_NEG / n)`, little-endian limbs.
    const G2: [u64; 5];

    /// One-shot `k * self` via the GLV split — variable-time in `k` (see the
    /// module docs), identical in value to `self * k` (including `self` =
    /// identity).
    ///
    /// For repeated multiplications against the same point or the same
    /// scalar, use [`Table`] / [`Decomposed`] directly to reuse the
    /// precomputation.
    fn mul_glv(&self, k: &Self::ScalarExt) -> Self {
        if bool::from(self.is_identity()) {
            // k*O = O. Identity tables work (see [`Table::batch`]), but
            // building one still costs a field inversion; short-circuit.
            return Self::identity();
        }
        Table::new(self).mul(k)
    }
}

/// These constants are computed by `sage/glv_constants.sage`, which prints
/// this impl body verbatim.
///
/// The `constants` test (see the module's test suite) re-verifies the short
/// basis against Pallas's own $\lambda$ = `Scalar::ZETA` using field
/// arithmetic alone, and the Babai coefficients `G1`/`G2` against their
/// defining rounding using limb arithmetic alone; the `decompose` tests prove
/// that the decomposition reconstructs `k`. A wrong constant cannot pass them.
impl GlvParams for pallas::Point {
    const V1A: u128 = 0x49e69d1640f049157fcae1c700000001;
    const V1B_NEG: u128 = 0x49e69d1640a899538cb1279300000000;
    const V2A: u128 = 0x49e69d1640a899538cb1279300000000;
    const V2B: u128 = 0x93cd3a2c8198e2690c7c095a00000001;
    const G1: [u64; 5] = [
        0x111f686111afc293,
        0xc35fbd4d086862e0,
        0x31f0256800000002,
        0x4f34e8b2066389a4,
        0x2,
    ];
    const G2: [u64; 5] = [
        0x4a95a2d972171db4,
        0x61afdea68480fa55,
        0x32c49e4bffffffff,
        0x279a745902a2654e,
        0x1,
    ];
}

/// As for Pallas, these constants are computed by `sage/glv_constants.sage`,
/// and the `constants` and `decompose` tests re-verify them against Vesta's
/// own $\lambda$ = `Scalar::ZETA` and the Babai coefficients' defining
/// rounding.
impl GlvParams for vesta::Point {
    const V1A: u128 = 0x49e69d1640f049157fcae1c700000000;
    const V1B_NEG: u128 = 0x49e69d1640a899538cb1279300000001;
    const V2A: u128 = 0x49e69d1640a899538cb1279300000001;
    const V2B: u128 = 0x93cd3a2c8198e2690c7c095a00000001;
    const G1: [u64; 5] = [
        0x841d8d62296e1563,
        0xc35fbd4d0afe9926,
        0x31f0256800000002,
        0x4f34e8b2066389a4,
        0x2,
    ];
    const G2: [u64; 5] = [
        0x841414c24bf99a83,
        0x61afdea685cc1578,
        0x32c49e4c00000003,
        0x279a745902a2654e,
        0x1,
    ];
}

/// Schoolbook multiply of `a` by `b` into `prod`, which must be zeroed and
/// hold exactly `a.len() + b.len()` limbs. Constant-time: a fixed loop
/// structure with explicit carry propagation.
fn schoolbook_mul(a: &[u64], b: &[u64], prod: &mut [u64]) {
    debug_assert_eq!(prod.len(), a.len() + b.len());
    for (i, &ai) in a.iter().enumerate() {
        let mut carry = 0u64;
        for (j, &bj) in b.iter().enumerate() {
            let (limb, c) = mac(prod[i + j], ai, bj, carry);
            prod[i + j] = limb;
            carry = c;
        }
        // First write to prod[i + b.len()] on each outer iteration.
        prod[i + b.len()] = carry;
    }
}

/// `round((g * k) / 2^384)` for a 5-limb `g` and 4-limb `k` — the Babai
/// coefficient. Fits `u128` (at most ~128 bits by construction).
fn round_mul_shift(g: &[u64; 5], k: &[u64; 4]) -> u128 {
    let mut prod = [0u64; 9];
    schoolbook_mul(g, k, &mut prod);
    // Bits >= 384 live in limbs 6..; round on bit 383 (top bit of limb 5).
    let round = prod[5] >> 63;
    (u128::from(prod[6]) | (u128::from(prod[7]) << 64)).wrapping_add(u128::from(round))
}

/// 256-bit product of two `u128`s, as little-endian limbs.
fn mul_u128(a: u128, b: u128) -> [u64; 4] {
    let mut prod = [0u64; 4];
    schoolbook_mul(
        &[a as u64, (a >> 64) as u64],
        &[b as u64, (b >> 64) as u64],
        &mut prod,
    );
    prod
}

/// 256-bit wrapping subtraction (two's complement).
fn sub256(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    let (d0, borrow) = sbb(a[0], b[0], 0);
    let (d1, borrow) = sbb(a[1], b[1], borrow);
    let (d2, borrow) = sbb(a[2], b[2], borrow);
    let (d3, _) = sbb(a[3], b[3], borrow);
    [d0, d1, d2, d3]
}

/// Interprets a 256-bit two's-complement value as `(is_negative, magnitude)`,
/// taking the low 128 bits of the magnitude.
///
/// GLV decomposition guarantees `|x| < 2^127` for the values reached here
/// (asserted in debug builds, here and in [`wnaf_digits`], and checked by the
/// `decompose` tests), so the high limbs of the magnitude are always zero and
/// no information is lost.
fn signed_halves(x: [u64; 4]) -> (bool, u128) {
    // Guard the truncation itself: the discarded limbs must be the sign
    // extension of bit 127. Values of 2^128 or more would otherwise be
    // silently truncated before `wnaf_digits`' magnitude assertion could
    // observe them.
    let ext = if x[1] >> 63 == 0 { 0 } else { u64::MAX };
    debug_assert!(
        x[2] == ext && x[3] == ext,
        "GLV half does not fit in 128 bits"
    );
    let low = u128::from(x[0]) | (u128::from(x[1]) << 64);
    if x[3] >> 63 == 0 {
        (false, low)
    } else {
        // Two's-complement negation commutes with truncation to the low 128
        // bits, and the magnitude lives entirely there.
        (true, (!low).wrapping_add(1))
    }
}

/// The four little-endian limbs of a Pasta scalar. (Pasta scalars have a
/// 32-byte little-endian representation; the four 8-byte reads cover it
/// exactly.)
fn scalar_limbs<F: PrimeField>(k: &F) -> [u64; 4] {
    let bytes = k.to_repr();
    let bytes: &[u8] = bytes.as_ref();
    let mut limbs = [0u64; 4];
    for (i, limb) in limbs.iter_mut().enumerate() {
        *limb = u64::from_le_bytes(bytes[i * 8..(i + 1) * 8].try_into().expect("8 bytes"));
    }
    limbs
}

/// GLV split: `k = k1 + k2 * lambda (mod n)` with `|k1|`, `|k2|` strictly
/// below `2^127`, each half returned as `(is_negative, magnitude)`.
fn decompose<C: GlvParams>(k: &C::ScalarExt) -> ((bool, u128), (bool, u128)) {
    let kl = scalar_limbs(k);
    let c1 = round_mul_shift(&C::G1, &kl);
    let c2 = round_mul_shift(&C::G2, &kl);
    // k1 = k - c1*V1A - c2*V2A   (two's complement over 256 bits)
    let k1 = sub256(sub256(kl, mul_u128(c1, C::V1A)), mul_u128(c2, C::V2A));
    // k2 = c1*V1B_NEG - c2*V2B   (v1.b = -V1B_NEG, v2.b = +V2B)
    let k2 = sub256(mul_u128(c1, C::V1B_NEG), mul_u128(c2, C::V2B));
    (signed_halves(k1), signed_halves(k2))
}

/// Small MSMs do not amortize GLV decomposition, affine endomorphism mapping,
/// and the two temporary vectors.
const MIN_GLV_MULTIEXP_TERMS: usize = 256;

/// Each GLV decomposition component has magnitude strictly below `2^127`.
const GLV_COMPONENT_BITS: usize = 127;

/// Estimates the dominant group work in a Signed-Booth MSM.
///
/// The serial model counts total point/window visits, bucket additions, and
/// accumulator doublings. The parallel model estimates the corresponding
/// critical-worker cost when windows have independent accumulators. Both omit
/// GLV setup costs; [`MIN_GLV_MULTIEXP_TERMS`] handles their small-MSM
/// amortization separately.
fn estimated_signed_booth_work(
    terms: usize,
    scalar_bits: usize,
    window_bits: usize,
    num_threads: usize,
) -> Option<usize> {
    let windows = scalar_bits.checked_div(window_bits)?.checked_add(1)?;
    let bucket_shift = u32::try_from(window_bits.checked_sub(1)?).ok()?;
    let buckets = 1usize.checked_shl(bucket_shift)?;

    if num_threads <= 1 {
        let point_visits = terms.checked_mul(windows)?;
        let bucket_additions = buckets.checked_mul(windows)?.checked_mul(2)?;
        let doublings = window_bits.checked_mul(windows.checked_sub(1)?)?;
        return point_visits
            .checked_add(bucket_additions)?
            .checked_add(doublings);
    }

    // Parallel windows have independent accumulators. Estimate the critical
    // worker's full-window work and the shifts of its highest-cost windows.
    let workers = num_threads.min(windows);
    let waves = windows.div_ceil(workers);
    let per_window = terms.checked_add(buckets.checked_mul(2)?)?;
    let mut shift_doublings = 0usize;
    let mut window = windows.checked_sub(1)?;
    for _ in 0..waves {
        shift_doublings = shift_doublings.checked_add(window_bits.checked_mul(window)?)?;
        match window.checked_sub(workers) {
            Some(next) => window = next,
            None => break,
        }
    }
    per_window.checked_mul(waves)?.checked_add(shift_doublings)
}

/// Chooses GLV only when its estimated Signed-Booth work is lower.
fn should_use_glv_multiexp<C: GlvParams>(
    terms: usize,
    window_bits: usize,
    num_threads: usize,
) -> bool {
    if terms < MIN_GLV_MULTIEXP_TERMS {
        return false;
    }

    let scalar_bits = <C::ScalarExt as PrimeField>::Repr::default()
        .as_ref()
        .len()
        .checked_mul(u8::BITS as usize);
    let glv_terms = terms.checked_mul(2);

    match (scalar_bits, glv_terms) {
        (Some(scalar_bits), Some(glv_terms)) => {
            match (
                estimated_signed_booth_work(terms, scalar_bits, window_bits, num_threads),
                estimated_signed_booth_work(
                    glv_terms,
                    GLV_COMPONENT_BITS,
                    window_bits,
                    num_threads,
                ),
            ) {
                (Some(generic), Some(glv)) => glv < generic,
                _ => false,
            }
        }
        _ => false,
    }
}

fn current_num_threads() -> usize {
    #[cfg(feature = "multicore")]
    {
        maybe_rayon::current_num_threads()
    }
    #[cfg(not(feature = "multicore"))]
    {
        1
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SignedMagnitude {
    negative: bool,
    magnitude: u128,
}

impl From<(bool, u128)> for SignedMagnitude {
    fn from((negative, magnitude): (bool, u128)) -> Self {
        Self {
            negative,
            magnitude,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct BoothDigit {
    magnitude: usize,
    negative: bool,
}

/// Extracts one signed-Booth digit and folds in the component's overall sign.
fn booth_digit(component: SignedMagnitude, window_bits: usize, window: usize) -> BoothDigit {
    let window_start = window * window_bits;
    let radix = 1usize << window_bits;
    let value = if window_start < u128::BITS as usize {
        ((component.magnitude >> window_start) as usize) & (radix - 1)
    } else {
        0
    };
    let overlap = if window_start == 0 {
        0
    } else {
        ((component.magnitude >> (window_start - 1)) & 1) as usize
    };

    let (magnitude, digit_negative) = if value < radix / 2 {
        (value + overlap, false)
    } else {
        let magnitude = radix - value - overlap;
        (magnitude, magnitude != 0)
    };
    BoothDigit {
        magnitude,
        negative: magnitude != 0 && (digit_negative ^ component.negative),
    }
}

// XYZZ stores `(X, Y, Z^2, Z^3)`, avoiding field inversions while MSM buckets
// are accumulated. The formulas are adapted from Supranational's Apache-2.0
// licensed `sppark` implementation: https://github.com/supranational/sppark.
#[derive(Clone, Copy)]
struct Xyzz<F: Field> {
    x: F,
    y: F,
    zz: F,
    zzz: F,
}

/// Field operations required by the XYZZ formulas.
///
/// With deferred arithmetic, a difference of two terminal products shares a
/// single reduction. The eager fallback preserves `glv` without `deferred`.
trait XyzzField: Field {
    fn difference_of_products(
        positive_left: Self,
        positive_right: Self,
        negative_left: Self,
        negative_right: Self,
    ) -> Self;
}

#[cfg(feature = "deferred")]
impl<F: DeferredField> XyzzField for F {
    fn difference_of_products(
        positive_left: Self,
        positive_right: Self,
        negative_left: Self,
        negative_right: Self,
    ) -> Self {
        let mut accumulator = <Self as DeferredField>::Accumulator::default();
        Self::mul_accumulate(&mut accumulator, &positive_left, &positive_right);
        Self::mul_accumulate(&mut accumulator, &-negative_left, &negative_right);
        Self::reduce(accumulator)
    }
}

#[cfg(not(feature = "deferred"))]
impl<F: Field> XyzzField for F {
    fn difference_of_products(
        positive_left: Self,
        positive_right: Self,
        negative_left: Self,
        negative_right: Self,
    ) -> Self {
        positive_left * positive_right - negative_left * negative_right
    }
}

impl<F: Field> Xyzz<F> {
    fn identity() -> Self {
        Self {
            x: F::ZERO,
            y: F::ZERO,
            zz: F::ZERO,
            zzz: F::ZERO,
        }
    }

    fn from_affine(point: AffinePoint<F>) -> Self {
        Self {
            x: point.x,
            y: point.y,
            zz: F::ONE,
            zzz: F::ONE,
        }
    }

    fn is_identity(&self) -> bool {
        bool::from(self.zz.is_zero() & self.zzz.is_zero())
    }
}

impl<F: XyzzField> Xyzz<F> {
    fn double(&mut self) {
        if self.is_identity() {
            return;
        }

        let u = self.y.double();
        let p = u.square();
        let r = u * p;
        let s = self.x * p;
        let x_squared = self.x.square();
        let m = x_squared.double() + x_squared;
        self.x = m.square() - s - s;
        self.y = F::difference_of_products(s - self.x, m, self.y, r);
        self.zz *= p;
        self.zzz *= r;
    }

    fn add(&mut self, other: &Self) {
        if other.is_identity() {
            return;
        }
        if self.is_identity() {
            *self = *other;
            return;
        }

        let u = self.x * other.zz;
        let s = self.y * other.zzz;
        let mut p = other.x * self.zz - u;
        let r = other.y * self.zzz - s;

        if !bool::from(p.is_zero()) {
            let mut pp = p.square();
            p *= pp;
            self.zz *= pp;
            self.zzz *= p;
            pp *= u;
            self.x = r.square() - p - pp - pp;
            self.y = F::difference_of_products(pp - self.x, r, s, p);
            self.zz *= other.zz;
            self.zzz *= other.zzz;
        } else if bool::from(r.is_zero()) {
            self.double();
        } else {
            *self = Self::identity();
        }
    }
}

#[derive(Clone, Copy)]
struct AffinePoint<F> {
    x: F,
    y: F,
}

struct PendingAffineAddition<F> {
    output: usize,
    left_x: F,
    left_y: F,
    x_sum: F,
    numerator: F,
    denominator: F,
    inversion_scratch: F,
}

const PASTA_FIELD_LIMBS: usize = 4;
const PASTA_REPR_BYTES: usize = PASTA_FIELD_LIMBS * core::mem::size_of::<u64>();
type PastaLimbs = [u64; PASTA_FIELD_LIMBS];

fn repr_limbs<F: PrimeField>(value: &F) -> PastaLimbs {
    let repr = value.to_repr();
    let bytes = repr.as_ref();
    assert_eq!(
        bytes.len(),
        PASTA_REPR_BYTES,
        "Pasta field representations are 256 bits"
    );
    let mut limbs = [0; PASTA_FIELD_LIMBS];
    for (limb, bytes) in limbs
        .iter_mut()
        .zip(bytes.chunks_exact(core::mem::size_of::<u64>()))
    {
        *limb = u64::from_le_bytes(bytes.try_into().unwrap());
    }
    limbs
}

fn field_from_limbs<F: PrimeField>(limbs: PastaLimbs) -> F {
    let mut repr = F::Repr::default();
    let bytes = repr.as_mut();
    assert_eq!(
        bytes.len(),
        PASTA_REPR_BYTES,
        "Pasta field representations are 256 bits"
    );
    for (bytes, limb) in bytes
        .chunks_exact_mut(core::mem::size_of::<u64>())
        .zip(limbs)
    {
        bytes.copy_from_slice(&limb.to_le_bytes());
    }
    Option::<F>::from(F::from_repr(repr)).expect("inverse must be canonical")
}

fn limbs_cmp(left: &PastaLimbs, right: &PastaLimbs) -> core::cmp::Ordering {
    left.iter()
        .zip(right)
        .rev()
        .find_map(|(left, right)| match left.cmp(right) {
            core::cmp::Ordering::Equal => None,
            ordering => Some(ordering),
        })
        .unwrap_or(core::cmp::Ordering::Equal)
}

fn limbs_add_assign(left: &mut PastaLimbs, right: &PastaLimbs) -> u64 {
    let mut carry = 0;
    for (left, right) in left.iter_mut().zip(right) {
        (*left, carry) = adc(*left, *right, carry);
    }
    carry
}

fn limbs_sub_assign(left: &mut PastaLimbs, right: &PastaLimbs) -> bool {
    let mut borrow = 0;
    for (left, right) in left.iter_mut().zip(right) {
        (*left, borrow) = sbb(*left, *right, borrow);
    }
    borrow != 0
}

fn limbs_shr_one(value: &mut PastaLimbs) {
    let mut high_bit = 0;
    for limb in value.iter_mut().rev() {
        let next_high_bit = *limb << 63;
        *limb = (*limb >> 1) | high_bit;
        high_bit = next_high_bit;
    }
}

fn halve_mod(value: &mut PastaLimbs, modulus: &PastaLimbs) {
    if value[0] & 1 == 1 {
        // Both Pasta moduli have a spare high bit, so this cannot overflow.
        let carry = limbs_add_assign(value, modulus);
        debug_assert_eq!(carry, 0);
    }
    limbs_shr_one(value);
}

fn sub_mod(left: &mut PastaLimbs, right: &PastaLimbs, modulus: &PastaLimbs) {
    if limbs_sub_assign(left, right) {
        // The carry cancels the borrow from the subtraction.
        let _ = limbs_add_assign(left, modulus);
    }
}

/// Inverts a public Pasta field element with the binary extended algorithm.
///
/// This is variable-time in `value`, which is appropriate for the public
/// affine denominators produced by verifier/prover MSMs. It must not be
/// exposed as a general replacement for [`Field::invert`].
fn invert_vartime<F: PrimeField>(value: &F) -> Option<F> {
    if bool::from(value.is_zero()) {
        return None;
    }

    let mut one = [0; PASTA_FIELD_LIMBS];
    one[0] = 1;
    let mut modulus = repr_limbs(&-F::ONE);
    let carry = limbs_add_assign(&mut modulus, &one);
    debug_assert_eq!(carry, 0);

    let mut u = repr_limbs(value);
    let mut v = modulus;
    let mut b = one;
    let mut c = [0; PASTA_FIELD_LIMBS];

    while u != one && v != one {
        while u[0] & 1 == 0 {
            limbs_shr_one(&mut u);
            halve_mod(&mut b, &modulus);
        }
        while v[0] & 1 == 0 {
            limbs_shr_one(&mut v);
            halve_mod(&mut c, &modulus);
        }

        if limbs_cmp(&v, &u).is_lt() {
            let borrow = limbs_sub_assign(&mut u, &v);
            debug_assert!(!borrow);
            sub_mod(&mut b, &c, &modulus);
        } else {
            let borrow = limbs_sub_assign(&mut v, &u);
            debug_assert!(!borrow);
            sub_mod(&mut c, &b, &modulus);
        }
    }

    Some(field_from_limbs(if u == one { b } else { c }))
}

fn batch_invert_denominators_vartime<F: PrimeField>(additions: &mut [PendingAffineAddition<F>]) {
    if additions.is_empty() {
        return;
    }

    let mut product = F::ONE;
    for addition in additions.iter_mut() {
        debug_assert!(!bool::from(addition.denominator.is_zero()));
        addition.inversion_scratch = product;
        product *= addition.denominator;
    }

    let mut product_inverse = invert_vartime(&product).expect("nonzero product");
    for addition in additions.iter_mut().rev() {
        let denominator = addition.denominator;
        addition.denominator = addition.inversion_scratch * product_inverse;
        product_inverse *= denominator;
    }
}

/// Visits the nonzero signed points assigned to one Booth window.
fn for_each_window_point<C, Visit>(
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[C::AffineExt],
    endo_bases: &[C::AffineExt],
    window_bits: usize,
    window: usize,
    mut visit: Visit,
) where
    C: GlvParams,
    Visit: FnMut(usize, C::AffineExt, bool),
{
    for (((first, second), base), endo_base) in components.iter().zip(bases).zip(endo_bases) {
        for (component, base) in [(*first, *base), (*second, *endo_base)] {
            let digit = booth_digit(component, window_bits, window);
            if digit.magnitude != 0 && !bool::from(base.is_identity()) {
                visit(digit.magnitude - 1, base, digit.negative);
            }
        }
    }
}

/// Reduces every affine bucket through shared Montgomery batch inversions.
///
/// `offsets` partitions `points` into one contiguous range per bucket. At
/// each tree level, all independent additions share one inversion. Identity,
/// doubling, and inverse pairs are handled explicitly because verifier MSM
/// inputs are public but not trusted.
fn reduce_affine_buckets<F: PrimeField>(
    mut points: Vec<AffinePoint<F>>,
    mut offsets: Vec<usize>,
) -> Vec<Xyzz<F>> {
    debug_assert!(!offsets.is_empty());
    let bucket_count = offsets.len() - 1;

    while offsets.windows(2).any(|range| range[1] - range[0] > 1) {
        let mut next_points = Vec::with_capacity((points.len() + bucket_count) / 2);
        let mut next_offsets = Vec::with_capacity(offsets.len());
        let mut pending = Vec::with_capacity(points.len() / 2);
        next_offsets.push(0);

        for range in offsets.windows(2) {
            let bucket = &points[range[0]..range[1]];
            for pair in bucket.chunks_exact(2) {
                let left = pair[0];
                let right = pair[1];

                let (numerator, denominator) = if left.x == right.x {
                    if left.y != right.y || bool::from(left.y.is_zero()) {
                        // The points are inverses, or this is a point of order
                        // two. Their sum is the identity, which is omitted.
                        continue;
                    }
                    let x_squared = left.x.square();
                    (x_squared.double() + x_squared, left.y.double())
                } else {
                    (right.y - left.y, right.x - left.x)
                };

                let output = next_points.len();
                next_points.push(AffinePoint {
                    x: F::ZERO,
                    y: F::ZERO,
                });
                pending.push(PendingAffineAddition {
                    output,
                    left_x: left.x,
                    left_y: left.y,
                    x_sum: left.x + right.x,
                    numerator,
                    denominator,
                    inversion_scratch: F::ZERO,
                });
            }
            if bucket.len() % 2 == 1 {
                next_points.push(bucket[bucket.len() - 1]);
            }
            next_offsets.push(next_points.len());
        }

        batch_invert_denominators_vartime(&mut pending);
        for addition in pending {
            let slope = addition.numerator * addition.denominator;
            let x = slope.square() - addition.x_sum;
            let y = slope * (addition.left_x - x) - addition.left_y;
            next_points[addition.output] = AffinePoint { x, y };
        }

        points = next_points;
        offsets = next_offsets;
    }

    let mut buckets = alloc::vec![Xyzz::identity(); bucket_count];
    for (bucket, range) in buckets.iter_mut().zip(offsets.windows(2)) {
        if range[0] != range[1] {
            debug_assert_eq!(range[1] - range[0], 1);
            *bucket = Xyzz::from_affine(points[range[0]]);
        }
    }
    buckets
}

fn sum_buckets<F: XyzzField>(buckets: &[Xyzz<F>]) -> Xyzz<F> {
    let mut running = Xyzz::identity();
    let mut sum = Xyzz::identity();
    for bucket in buckets.iter().rev() {
        running.add(bucket);
        sum.add(&running);
    }
    sum
}

fn fill_window<C, Coordinates>(
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[C::AffineExt],
    endo_bases: &[C::AffineExt],
    window_bits: usize,
    window: usize,
    affine_coordinates: &Coordinates,
) -> Vec<Xyzz<C::Base>>
where
    C: GlvParams,
    Coordinates: Fn(C::AffineExt) -> (C::Base, C::Base),
{
    let bucket_count = 1 << (window_bits - 1);
    let mut counts = alloc::vec![0usize; bucket_count];
    for_each_window_point::<C, _>(
        components,
        bases,
        endo_bases,
        window_bits,
        window,
        |bucket, _, _| counts[bucket] += 1,
    );

    let mut offsets = Vec::with_capacity(bucket_count + 1);
    offsets.push(0);
    for count in counts {
        offsets.push(offsets.last().copied().unwrap() + count);
    }

    let mut positions = offsets[..bucket_count].to_vec();
    let mut points = alloc::vec![
        AffinePoint {
            x: C::Base::ZERO,
            y: C::Base::ZERO,
        };
        *offsets.last().unwrap()
    ];
    for_each_window_point::<C, _>(
        components,
        bases,
        endo_bases,
        window_bits,
        window,
        |bucket, base, negative| {
            let (x, y) = affine_coordinates(base);
            let position = positions[bucket];
            points[position] = AffinePoint {
                x,
                y: if negative { -y } else { y },
            };
            positions[bucket] += 1;
        },
    );

    reduce_affine_buckets(points, offsets)
}

fn multiexp_serial<C, Coordinates>(
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[C::AffineExt],
    endo_bases: &[C::AffineExt],
    window_bits: usize,
    affine_coordinates: &Coordinates,
) -> Xyzz<C::Base>
where
    C: GlvParams,
    C::Base: XyzzField,
    Coordinates: Fn(C::AffineExt) -> (C::Base, C::Base),
{
    let window_count = GLV_COMPONENT_BITS / window_bits + 1;
    let mut acc = Xyzz::identity();

    for window in (0..window_count).rev() {
        if window + 1 != window_count {
            for _ in 0..window_bits {
                acc.double();
            }
        }

        let buckets = fill_window::<C, Coordinates>(
            components,
            bases,
            endo_bases,
            window_bits,
            window,
            affine_coordinates,
        );
        acc.add(&sum_buckets(&buckets));
    }
    acc
}

#[cfg(feature = "multicore")]
fn multiexp_parallel<C, Coordinates>(
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[C::AffineExt],
    endo_bases: &[C::AffineExt],
    window_bits: usize,
    affine_coordinates: &Coordinates,
) -> Xyzz<C::Base>
where
    C: GlvParams,
    C::Base: XyzzField,
    Coordinates: Fn(C::AffineExt) -> (C::Base, C::Base) + Sync,
{
    let window_count = GLV_COMPONENT_BITS / window_bits + 1;
    (0..window_count)
        .into_par_iter()
        .map(|window| {
            let buckets = fill_window::<C, Coordinates>(
                components,
                bases,
                endo_bases,
                window_bits,
                window,
                affine_coordinates,
            );
            let mut sum = sum_buckets(&buckets);
            for _ in 0..window_bits * window {
                sum.double();
            }
            sum
        })
        .reduce(Xyzz::identity, |mut left, right| {
            left.add(&right);
            left
        })
}

fn multiexp<C, Coordinates, ToCurve>(
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[C::AffineExt],
    endo_bases: &[C::AffineExt],
    window_bits: usize,
    num_threads: usize,
    affine_coordinates: &Coordinates,
    xyzz_to_curve: ToCurve,
) -> C
where
    C: GlvParams,
    C::Base: XyzzField,
    Coordinates: Fn(C::AffineExt) -> (C::Base, C::Base) + Sync,
    ToCurve: FnOnce(C::Base, C::Base, C::Base, C::Base) -> C,
{
    debug_assert_eq!(components.len(), bases.len());
    debug_assert_eq!(components.len(), endo_bases.len());

    #[cfg(not(feature = "multicore"))]
    let _ = num_threads;
    #[cfg(feature = "multicore")]
    let acc = if num_threads > 1 {
        multiexp_parallel::<C, Coordinates>(
            components,
            bases,
            endo_bases,
            window_bits,
            affine_coordinates,
        )
    } else {
        multiexp_serial::<C, Coordinates>(
            components,
            bases,
            endo_bases,
            window_bits,
            affine_coordinates,
        )
    };
    #[cfg(not(feature = "multicore"))]
    let acc = multiexp_serial::<C, Coordinates>(
        components,
        bases,
        endo_bases,
        window_bits,
        affine_coordinates,
    );
    xyzz_to_curve(acc.x, acc.y, acc.zz, acc.zzz)
}

fn try_multiexp_inner<C>(
    scalars: &[C::ScalarExt],
    bases: &[C::AffineExt],
    window_bits: usize,
    mut affine_endo: impl FnMut(C::AffineExt) -> C::AffineExt,
    affine_coordinates: impl Fn(C::AffineExt) -> (C::Base, C::Base) + Sync,
    xyzz_to_curve: impl FnOnce(C::Base, C::Base, C::Base, C::Base) -> C,
) -> Option<C>
where
    C: GlvParams,
    C::Base: XyzzField,
{
    assert_eq!(scalars.len(), bases.len());
    assert!(window_bits > 0 && window_bits < usize::BITS as usize);
    let num_threads = current_num_threads();
    if !should_use_glv_multiexp::<C>(scalars.len(), window_bits, num_threads) {
        return None;
    }

    let components = scalars
        .iter()
        .map(decompose::<C>)
        .map(|(first, second)| (first.into(), second.into()))
        .collect::<Vec<_>>();
    let endo_bases = bases
        .iter()
        .copied()
        .map(&mut affine_endo)
        .collect::<Vec<_>>();
    Some(multiexp(
        &components,
        bases,
        &endo_bases,
        window_bits,
        num_threads,
        &affine_coordinates,
        xyzz_to_curve,
    ))
}

/// Attempts a GLV Signed-Booth multiscalar multiplication for a large Pasta
/// MSM. The caller supplies the affine endomorphism because the concrete
/// affine coordinates remain private to `curves`.
#[cfg(feature = "deferred")]
pub(crate) fn try_multiexp<C>(
    scalars: &[C::ScalarExt],
    bases: &[C::AffineExt],
    window_bits: usize,
    affine_endo: impl FnMut(C::AffineExt) -> C::AffineExt,
    affine_coordinates: impl Fn(C::AffineExt) -> (C::Base, C::Base) + Sync,
    xyzz_to_curve: impl FnOnce(C::Base, C::Base, C::Base, C::Base) -> C,
) -> Option<C>
where
    C: GlvParams,
    C::Base: DeferredField,
{
    try_multiexp_inner(
        scalars,
        bases,
        window_bits,
        affine_endo,
        affine_coordinates,
        xyzz_to_curve,
    )
}

/// Attempts a GLV Signed-Booth multiscalar multiplication for a large Pasta
/// MSM. The caller supplies the affine endomorphism because the concrete
/// affine coordinates remain private to `curves`.
#[cfg(not(feature = "deferred"))]
pub(crate) fn try_multiexp<C: GlvParams>(
    scalars: &[C::ScalarExt],
    bases: &[C::AffineExt],
    window_bits: usize,
    affine_endo: impl FnMut(C::AffineExt) -> C::AffineExt,
    affine_coordinates: impl Fn(C::AffineExt) -> (C::Base, C::Base) + Sync,
    xyzz_to_curve: impl FnOnce(C::Base, C::Base, C::Base, C::Base) -> C,
) -> Option<C> {
    try_multiexp_inner(
        scalars,
        bases,
        window_bits,
        affine_endo,
        affine_coordinates,
        xyzz_to_curve,
    )
}

/// The GLV window for one base point: the odd multiples `{1, 3, 5, 7} * P` and
/// `{1, 3, 5, 7} * phi(P)` in affine coordinates. 512 bytes per table.
///
/// Build one with [`Table::new`], or many with one shared normalization via
/// [`Table::batch`].
#[derive(Clone, Copy, Debug)]
pub struct Table<C: GlvParams> {
    /// `{1, 3, 5, 7} * P`
    t1: [C::AffineExt; 4],
    /// `{1, 3, 5, 7} * phi(P)`
    t2: [C::AffineExt; 4],
}

impl<C: GlvParams> Table<C> {
    /// Builds the window for a single point (with no heap allocation, but
    /// one field inversion; amortize that with [`Table::batch`]).
    pub fn new(p: &C) -> Self {
        let proj = Self::window_proj(p);
        let mut affine = [C::AffineExt::identity(); 8];
        C::batch_normalize(&proj, &mut affine);
        Self::from_window(&affine)
    }

    /// Builds [`Table`]s for a batch of points with one shared
    /// batch normalization across all `8 * n` window entries — a single field
    /// inversion for the whole batch, where building each window individually
    /// pays one inversion per point.
    ///
    /// Identity inputs produce identity tables and may be mixed with
    /// non-identity points in the same batch.
    pub fn batch(points: &[C]) -> Vec<Table<C>> {
        let n = points.len();
        if n == 0 {
            return Vec::new();
        }
        let mut proj = Vec::with_capacity(n * 8);
        for p in points {
            proj.extend_from_slice(&Self::window_proj(p));
        }
        // One inversion for the whole batch.
        let mut affine = alloc::vec![C::AffineExt::identity(); n * 8];
        C::batch_normalize(&proj, &mut affine);
        affine.chunks_exact(8).map(Self::from_window).collect()
    }

    /// The eight projective window entries for one point:
    /// `[1P, 3P, 5P, 7P, 1phi(P), 3phi(P), 5phi(P), 7phi(P)]`. Projective
    /// group operations only (cheap additions and endomorphism, no
    /// inversions); the endomorphism multiples are taken via
    /// [`CurveExt::endo`] so they ride along in the caller's normalization.
    fn window_proj(p: &C) -> [C; 8] {
        let two_p = p.double();
        let mut w = [*p; 8];
        for i in 1..4 {
            w[i] = w[i - 1] + two_p;
        }
        for i in 0..4 {
            w[i + 4] = w[i].endo();
        }
        w
    }

    /// Assembles a table from one normalized 8-entry window.
    fn from_window(w: &[C::AffineExt]) -> Self {
        Table {
            t1: w[..4].try_into().expect("four P multiples"),
            t2: w[4..8].try_into().expect("four phi(P) multiples"),
        }
    }

    /// The base point P (= t1\[0\]) back as a projective point.
    #[cfg(test)]
    fn point(&self) -> C {
        C::from(self.t1[0])
    }

    /// `k * P` for the P encoded by this table, decomposing `k` on the spot.
    ///
    /// When one scalar meets many tables, decompose once with
    /// [`Decomposed::new`] and use [`Table::mul_decomposed`] instead.
    pub fn mul(&self, k: &C::ScalarExt) -> C {
        self.mul_decomposed(&Decomposed::new(k))
    }

    /// `k * P` for the P encoded by this table, via the Straus
    /// shared-doubling ladder over the GLV split. Identical to `P * k`
    /// (tested).
    pub fn mul_decomposed(&self, k: &Decomposed<C>) -> C {
        let mut acc = C::identity();
        for i in (0..k.len).rev() {
            // `acc` is still the identity on the first iteration; skip the
            // wasted doubling.
            if i + 1 < k.len {
                acc = acc.double();
            }
            Self::add_digit(&mut acc, &self.t1, k.digits1[i]);
            Self::add_digit(&mut acc, &self.t2, k.digits2[i]);
        }
        acc
    }

    /// Adds `d * B` to `acc`, where `table` holds `{1, 3, 5, 7} * B` and `d`
    /// is a signed odd wNAF digit (zero adds nothing).
    fn add_digit(acc: &mut C, table: &[C::AffineExt; 4], d: i8) {
        if d != 0 {
            let mut a = table[(d.unsigned_abs() / 2) as usize];
            if d < 0 {
                a = -a;
            }
            *acc += a;
        }
    }
}

/// A scalar in GLV-decomposed, wNAF-recoded form, ready for
/// [`Table::mul_decomposed`].
///
/// Building this once per scalar hoists the decomposition and digit
/// recoding out of a loop that multiplies the same scalar against many
/// tables (e.g. one viewing key against a batch of ephemeral keys).
#[derive(Clone, Debug)]
pub struct Decomposed<C: GlvParams> {
    digits1: [i8; MAX_WNAF_DIGITS],
    digits2: [i8; MAX_WNAF_DIGITS],
    /// Digit positions in use: the longer of the two halves' wNAF lengths.
    /// Both arrays are zero beyond their own half's length.
    len: usize,
    _curve: core::marker::PhantomData<C>,
}

impl<C: GlvParams> Decomposed<C> {
    /// Decomposes `k` and recodes both halves as width-4 wNAF digits, with
    /// each half's sign folded into its digits.
    pub fn new(k: &C::ScalarExt) -> Self {
        let ((neg1, a1), (neg2, a2)) = decompose::<C>(k);
        let (digits1, len1) = wnaf_digits(a1, neg1);
        let (digits2, len2) = wnaf_digits(a2, neg2);
        Decomposed {
            digits1,
            digits2,
            len: len1.max(len2),
            _curve: core::marker::PhantomData,
        }
    }
}

/// Upper bound on the number of width-4 wNAF digits of a decomposition half:
/// an n-bit magnitude yields at most n + 1 digits, and [`decompose`] bounds
/// the halves below `2^127`.
const MAX_WNAF_DIGITS: usize = 128;

/// Width-4 wNAF digits of a u128 magnitude, lowest position first, with the
/// half's overall sign folded into the digits when `negate` is set.
fn wnaf_digits(a: u128, negate: bool) -> ([i8; MAX_WNAF_DIGITS], usize) {
    debug_assert!(a >> 127 == 0, "magnitude must be at most 127 bits");
    let mut digits = [0i8; MAX_WNAF_DIGITS];
    let mut n = 0;
    let mut k = a;
    while k != 0 {
        if k & 1 == 1 {
            let low = (k & 0xF) as i8;
            let d = if low >= 8 { low - 16 } else { low };
            digits[n] = if negate { -d } else { d };
            if d >= 0 {
                k -= d as u128;
            } else {
                k += (-d) as u128;
            }
        }
        n += 1;
        k >>= 1;
    }
    (digits, n)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::{adc, CurveAffine};
    use ff::Field;

    #[test]
    fn multiexp_backend_selection() {
        assert_eq!(estimated_signed_booth_work(2_150, 256, 8, 1), Some(79_654));
        assert_eq!(
            estimated_signed_booth_work(4_300, GLV_COMPONENT_BITS, 8, 1),
            Some(73_016)
        );
        assert_eq!(estimated_signed_booth_work(5_678, 256, 9, 1), Some(179_762));
        assert_eq!(
            estimated_signed_booth_work(11_356, GLV_COMPONENT_BITS, 9, 1),
            Some(178_146)
        );

        assert!(!should_use_glv_multiexp::<pallas::Point>(255, 8, 1));
        assert!(should_use_glv_multiexp::<pallas::Point>(2_150, 8, 1));
        assert!(should_use_glv_multiexp::<vesta::Point>(5_678, 9, 1));

        assert_eq!(estimated_signed_booth_work(2_150, 256, 8, 8), Some(12_670));
        assert_eq!(
            estimated_signed_booth_work(4_300, GLV_COMPONENT_BITS, 8, 8),
            Some(9_288)
        );
        assert_eq!(estimated_signed_booth_work(5_678, 256, 9, 8), Some(25_336));
        assert_eq!(
            estimated_signed_booth_work(11_356, GLV_COMPONENT_BITS, 9, 8),
            Some(23_916)
        );
        assert!(should_use_glv_multiexp::<pallas::Point>(2_150, 8, 8));
        assert!(should_use_glv_multiexp::<vesta::Point>(5_678, 9, 8));

        // At sufficiently large sizes, doubling the term count outweighs the
        // shorter components for this unchanged window width.
        assert!(!should_use_glv_multiexp::<pallas::Point>(1_000_000, 14, 1));
        assert!(!should_use_glv_multiexp::<pallas::Point>(1_000_000, 14, 8));
        assert!(!should_use_glv_multiexp::<pallas::Point>(usize::MAX, 14, 8));
    }

    #[test]
    fn integer_multiplication_carry_boundaries() {
        assert_eq!(
            mul_u128(u128::MAX, u128::MAX),
            [1, 0, u64::MAX - 1, u64::MAX]
        );

        let pallas_scalar_max = [
            0x8c46eb2100000000,
            0x224698fc0994a8dd,
            0,
            0x4000000000000000,
        ];
        assert_eq!(
            round_mul_shift(&pallas::Point::G1, &pallas_scalar_max),
            0x93cd3a2c8198e2690c7c095a00000001
        );
        assert_eq!(
            round_mul_shift(&pallas::Point::G2, &pallas_scalar_max),
            0x49e69d1640a899538cb1279300000000
        );

        let vesta_scalar_max = [
            0x992d30ed00000000,
            0x224698fc094cf91b,
            0,
            0x4000000000000000,
        ];
        assert_eq!(
            round_mul_shift(&vesta::Point::G1, &vesta_scalar_max),
            0x93cd3a2c8198e2690c7c095a00000001
        );
        assert_eq!(
            round_mul_shift(&vesta::Point::G2, &vesta_scalar_max),
            0x49e69d1640a899538cb1279300000001
        );
    }

    /// Deterministic full-width scalars for the known-answer tests.
    fn scalars<F: PrimeField>(n: u64) -> impl Iterator<Item = F> {
        (0..n).map(|i| {
            (F::from(0x9E37_79B9_7F4A_7C15u64 + i).square() + F::from(0x0123_4567_89AB_CDEFu64))
                .square()
                + F::from(i)
        })
    }

    /// Checks `g == round(2^384 * v / n)` for the curve's scalar modulus `n`,
    /// using limb arithmetic only: `g` is that rounding if and only if
    /// `|2^384 * v - g * n| < n/2` (an exact tie is impossible: `n` is odd,
    /// so `n/2` is not an integer).
    fn babai_coefficient_verify<C: GlvParams>(g: &[u64; 5], v: u128) {
        // n = (n - 1) + 1, with n - 1 read out of the field type as -1.
        // n is odd, so n - 1 is even and adding the 1 back cannot carry.
        let mut n = scalar_limbs(&-C::ScalarExt::ONE);
        n[0] += 1;

        // 2^384 * v occupies limbs 6..8 of a 9-limb value.
        let mut target = [0u64; 9];
        target[6] = v as u64;
        target[7] = (v >> 64) as u64;

        let mut gn = [0u64; 9];
        schoolbook_mul(g, &n, &mut gn);

        // residual = 2^384 * v - g*n, two's complement over 9 limbs; negate
        // to a magnitude if the subtraction borrows.
        let mut residual = [0u64; 9];
        let mut borrow = 0;
        for (r, (&t, &m)) in residual.iter_mut().zip(target.iter().zip(gn.iter())) {
            let (limb, b) = sbb(t, m, borrow);
            *r = limb;
            borrow = b;
        }
        if borrow != 0 {
            let mut carry = 1;
            for limb in residual.iter_mut() {
                let (l, c) = adc(!*limb, 0, carry);
                *limb = l;
                carry = c;
            }
        }

        // |residual| < n/2 requires it to fit four limbs in the first place.
        assert!(
            residual[4..].iter().all(|&l| l == 0),
            "Babai residual far exceeds n"
        );
        // |residual| < n/2 <=> 2*|residual| < n, checked by subtraction:
        // n - 2*|residual| must not borrow (and equality is impossible, as
        // n is odd and the doubled value even).
        let mut doubled = [0u64; 5];
        doubled[0] = residual[0] << 1;
        for i in 1..5 {
            doubled[i] = (residual[i] << 1) | (residual[i - 1] >> 63);
        }
        let n5 = [n[0], n[1], n[2], n[3], 0];
        let mut borrow = 0;
        for (&ni, &di) in n5.iter().zip(doubled.iter()) {
            let (_, b) = sbb(ni, di, borrow);
            borrow = b;
        }
        assert!(borrow == 0, "g is not round(2^384 * v / n)");
    }

    /// The short-basis lattice relations, re-verified against the curve's
    /// own lambda (= `Scalar::ZETA`) using field arithmetic only:
    ///   V1A - V1B_NEG*lambda == 0  and  V2A + V2B*lambda == 0  (mod n),
    /// plus the Babai coefficients G1/G2 against their defining rounding.
    fn constants_verify<C: GlvParams>() {
        let lambda = C::ScalarExt::ZETA;
        let from = C::ScalarExt::from_u128;
        assert_eq!(from(C::V1A), from(C::V1B_NEG) * lambda, "v1 not in lattice");
        assert_eq!(from(C::V2A), -(from(C::V2B) * lambda), "v2 not in lattice");
        babai_coefficient_verify::<C>(&C::G1, C::V2B);
        babai_coefficient_verify::<C>(&C::G2, C::V1B_NEG);
    }

    /// The endomorphism / lambda pairing on the real curve, on the same
    /// projective `endo` the table build relies on: `phi(P) == ZETA * P`.
    fn endo_map_is_lambda<C: GlvParams>() {
        let g = C::generator();
        for k in scalars::<C::ScalarExt>(64) {
            let p = g * k;
            assert_eq!(
                p.endo(),
                p * C::ScalarExt::ZETA,
                "phi(P) must equal ZETA_scalar * P"
            );
        }
    }

    /// The algebraic gate: k1 + k2*lambda == k (mod n) with both halves at most
    /// 2^127, for full-width scalars and the edge cases. Wrong GLV
    /// constants cannot pass this.
    fn decompose_reconstructs<C: GlvParams>() {
        let lambda = C::ScalarExt::ZETA;
        let check = |k: C::ScalarExt| {
            let ((neg1, a1), (neg2, a2)) = decompose::<C>(&k);
            assert!(a1 >> 127 == 0, "k1 exceeds 127 bits");
            assert!(a2 >> 127 == 0, "k2 exceeds 127 bits");
            let s1 = C::ScalarExt::from_u128(a1);
            let s1 = if neg1 { -s1 } else { s1 };
            let s2 = C::ScalarExt::from_u128(a2);
            let s2 = if neg2 { -s2 } else { s2 };
            assert_eq!(s1 + s2 * lambda, k, "decomposition must reconstruct k");
        };
        check(C::ScalarExt::ZERO);
        check(C::ScalarExt::ONE);
        check(-C::ScalarExt::ONE);
        check(lambda);
        check(-lambda);
        for k in scalars::<C::ScalarExt>(1000) {
            check(k);
        }
    }

    /// Table-based multiplication matches the group's native `Mul`.
    fn table_mul_matches_group_mul<C: GlvParams>() {
        let g = C::generator();
        for (i, k) in scalars::<C::ScalarExt>(64).enumerate() {
            let p = g * (k + C::ScalarExt::from(i as u64 + 1));
            let table = Table::new(&p);
            for k2 in scalars::<C::ScalarExt>(4) {
                assert_eq!(table.mul(&k2), p * k2, "table mul must match group mul");
            }
        }
    }

    /// One-shot `mul_glv` matches the native operator.
    fn mul_glv_matches_operator<C: GlvParams>() {
        let g = C::generator();
        for k in scalars::<C::ScalarExt>(64) {
            let p = g * (k + C::ScalarExt::ONE);
            assert_eq!(p.mul_glv(&k), p * k, "mul_glv must match operator");
        }
    }

    /// The batched table build equals the solo build, point by point.
    fn batch_tables_equal_solo<C: GlvParams>() {
        let g = C::generator();
        let points: Vec<C> = scalars::<C::ScalarExt>(16)
            .map(|k| g * (k + C::ScalarExt::ONE))
            .collect();
        let batched = Table::batch(&points);
        assert_eq!(batched.len(), points.len());
        for (p, table) in points.iter().zip(batched.iter()) {
            let solo = Table::new(p);
            assert_eq!(table.point(), solo.point());
            let k = C::ScalarExt::from(0xDEAD_BEEFu64);
            assert_eq!(
                table.mul(&k),
                solo.mul(&k),
                "batched table must act like solo"
            );
        }
    }

    /// Identity tables work both alone and alongside non-identity tables.
    fn identity_tables<C: GlvParams>() {
        let identity = C::identity();
        let generator = C::generator();
        let k = C::ScalarExt::from(0xDEAD_BEEFu64);

        let solo = Table::new(&identity);
        assert_eq!(solo.point(), identity);
        assert_eq!(solo.mul(&k), identity);

        let batched = Table::batch(&[identity, generator]);
        assert_eq!(batched.len(), 2);
        assert_eq!(batched[0].point(), identity);
        assert_eq!(batched[0].mul(&k), identity);
        assert_eq!(batched[1].point(), generator);
        assert_eq!(batched[1].mul(&k), generator * k);
    }

    /// A reused [`Decomposed`] gives the same products as decomposing
    /// per-multiplication.
    fn decomposed_reuse_matches_fresh<C: GlvParams>() {
        let g = C::generator();
        let k = scalars::<C::ScalarExt>(1).next().unwrap();
        let decomposed = Decomposed::<C>::new(&k);
        for k2 in scalars::<C::ScalarExt>(16) {
            let p = g * (k2 + C::ScalarExt::ONE);
            let table = Table::new(&p);
            assert_eq!(
                table.mul_decomposed(&decomposed),
                table.mul(&k),
                "hoisted decomposition must match fresh"
            );
        }
    }

    fn xyzz_matches_native<C>()
    where
        C: GlvParams,
        C::Base: XyzzField,
        C::AffineExt: CurveAffine<Base = C::Base>,
    {
        let generator = C::generator();
        let affine = C::AffineExt::from(generator);
        let coordinates = affine.coordinates().unwrap();
        let (x, y) = (*coordinates.x(), *coordinates.y());
        let to_curve = |point: Xyzz<C::Base>| {
            if point.is_identity() {
                C::identity()
            } else {
                C::new_jacobian(
                    point.x * point.zz.square(),
                    point.y * point.zzz.square(),
                    point.zzz,
                )
                .unwrap()
            }
        };

        let affine = Xyzz::from_affine(AffinePoint { x, y });
        let negative_affine = Xyzz::from_affine(AffinePoint { x, y: -y });

        let mut positive = affine;
        assert_eq!(to_curve(positive), generator);
        positive.add(&affine);
        assert_eq!(to_curve(positive), generator.double());

        let mut negative = negative_affine;
        negative.add(&negative_affine);
        assert_eq!(to_curve(negative), -generator.double());

        positive.add(&negative);
        assert_eq!(to_curve(positive), C::identity());

        let mut two = affine;
        two.double();
        let mut three = two;
        three.add(&affine);
        two.add(&three);
        assert_eq!(to_curve(two), generator * C::ScalarExt::from(5));
    }

    fn batch_affine_buckets_match_native<C>()
    where
        C: GlvParams,
        C::AffineExt: CurveAffine<Base = C::Base>,
    {
        let generator = C::generator();
        let two = generator.double();
        let three = two + generator;
        let four = three + generator;
        let five = four + generator;
        let source = [
            Vec::new(),
            alloc::vec![generator],
            alloc::vec![generator, generator],
            alloc::vec![generator, -generator],
            alloc::vec![generator, two, three],
            alloc::vec![generator, two, -three],
            alloc::vec![generator, two, three, four, five],
        ];

        let mut points = Vec::new();
        let mut offsets = Vec::with_capacity(source.len() + 1);
        offsets.push(0);
        for bucket in &source {
            for point in bucket {
                let affine = C::AffineExt::from(*point);
                let coordinates = affine.coordinates().unwrap();
                points.push(AffinePoint {
                    x: *coordinates.x(),
                    y: *coordinates.y(),
                });
            }
            offsets.push(points.len());
        }

        let reduced = reduce_affine_buckets(points, offsets);
        assert_eq!(reduced.len(), source.len());
        for (actual, bucket) in reduced.into_iter().zip(source) {
            let actual = if actual.is_identity() {
                C::identity()
            } else {
                C::new_jacobian(
                    actual.x * actual.zz.square(),
                    actual.y * actual.zzz.square(),
                    actual.zzz,
                )
                .unwrap()
            };
            let expected = bucket.into_iter().sum::<C>();
            assert_eq!(actual, expected);
        }
    }

    fn vartime_inverse_matches_field<F: PrimeField>() {
        assert_eq!(invert_vartime(&F::ZERO), None);
        for value in [F::ONE, -F::ONE].into_iter().chain(scalars::<F>(1_000)) {
            assert_eq!(invert_vartime(&value), Option::<F>::from(value.invert()));
        }
    }

    macro_rules! glv_tests {
        ($mod_name:ident, $curve:ty) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn constants() {
                    constants_verify::<$curve>();
                }
                #[test]
                fn endo_map() {
                    endo_map_is_lambda::<$curve>();
                }
                #[test]
                fn decompose() {
                    decompose_reconstructs::<$curve>();
                }
                #[test]
                fn table_mul() {
                    table_mul_matches_group_mul::<$curve>();
                }
                #[test]
                fn one_shot() {
                    mul_glv_matches_operator::<$curve>();
                }
                #[test]
                fn batch_build() {
                    batch_tables_equal_solo::<$curve>();
                }
                #[test]
                fn identity_table() {
                    identity_tables::<$curve>();
                }
                #[test]
                fn decomposed_reuse() {
                    decomposed_reuse_matches_fresh::<$curve>();
                }
                #[test]
                fn xyzz() {
                    xyzz_matches_native::<$curve>();
                }
                #[test]
                fn batch_affine_buckets() {
                    batch_affine_buckets_match_native::<$curve>();
                }
                #[test]
                fn vartime_inverse() {
                    vartime_inverse_matches_field::<<$curve as CurveExt>::Base>();
                }
            }
        };
    }

    glv_tests!(pallas_glv, pallas::Point);
    glv_tests!(vesta_glv, vesta::Point);

    /// Edge-case scalars exercised through the FULL `mul_glv` path (not just
    /// `decompose`): the additive/multiplicative identities and their
    /// negations, lambda and its neighbours (the decomposition's own axis), and
    /// the half-width boundary where k1/k2 magnitudes live.
    fn edge_case_matrix<C: GlvParams>() {
        let lambda = C::ScalarExt::ZETA;
        let edge_scalars = [
            C::ScalarExt::ZERO,
            C::ScalarExt::ONE,
            -C::ScalarExt::ONE,
            C::ScalarExt::from(2),
            lambda,
            -lambda,
            lambda + C::ScalarExt::ONE,
            C::ScalarExt::from(u64::MAX),
            C::ScalarExt::from_u128((1u128 << 127) - 1),
            C::ScalarExt::from_u128(1u128 << 127),
            C::ScalarExt::from_u128((1u128 << 127) + 1),
        ];
        let g = C::generator();
        let points = [g, g * (lambda + C::ScalarExt::from(42))];
        for p in points {
            for k in edge_scalars {
                assert_eq!(p.mul_glv(&k), p * k, "mul_glv must match Mul on edges");
            }
        }
        // k*O = O for every scalar, including 0.
        let identity = C::identity();
        for k in edge_scalars {
            assert_eq!(identity.mul_glv(&k), C::identity(), "k*O must be O");
        }
    }

    #[test]
    fn edge_cases_pallas() {
        edge_case_matrix::<pallas::Point>();
    }
    #[test]
    fn edge_cases_vesta() {
        edge_case_matrix::<vesta::Point>();
    }

    /// Loads a Pasta scalar from its four little-endian limbs.
    fn scalar_from_limbs<F: PrimeField>(limbs: [u64; 4]) -> F {
        let mut bytes = [0u8; 32];
        for (chunk, limb) in bytes.chunks_exact_mut(8).zip(limbs.iter()) {
            chunk.copy_from_slice(&limb.to_le_bytes());
        }
        let mut repr = F::Repr::default();
        repr.as_mut().copy_from_slice(&bytes);
        F::from_repr(repr).unwrap()
    }

    /// The lattice-constructed Babai-boundary scalars, computed by
    /// `sage/glv_boundary_scalars.sage` (which prints these constants
    /// verbatim); provenance in [`babai_boundary_witness`].
    const PALLAS_BOUNDARY_SCALAR: [u64; 4] = [
        0xf1616cb5a3632910,
        0xa487c2df3b0d145f,
        0xd70a3d98c2549413,
        0x3d70a3d70a3d70a3,
    ];
    const VESTA_BOUNDARY_SCALAR: [u64; 4] = [
        0x17b30ff8ae506c98,
        0xecc8ab77c7c0d84f,
        0xd70a3d86799d8e38,
        0x3d70a3d70a3d70a3,
    ];

    /// A scalar constructed (by lattice reduction over the joint residues
    /// `G1*k mod 2^384`, `G2*k mod 2^384` — see
    /// `sage/glv_boundary_scalars.sage`) to sit on the Babai rounding
    /// boundary: flipping bit 127 of `G2` — a corruption that the suite
    /// predating `babai_coefficient_verify` provably accepted, since it
    /// leaves the `round_mul_shift` known-answer test unmoved and shifts
    /// `c2` for only ~2^-16 of random scalars — moves `c2` by one *here*
    /// and pushes `|k2|` past the half-width bound that `wnaf_digits` and
    /// `MAX_WNAF_DIGITS` rely on.
    ///
    /// With the shipped constants the witness must behave like any other
    /// scalar; the second half of the test pins its boundary geometry.
    fn babai_boundary_witness<C: GlvParams>(limbs: [u64; 4]) {
        let k = scalar_from_limbs::<C::ScalarExt>(limbs);
        assert_eq!(
            scalar_limbs(&k),
            limbs,
            "witness must be a canonical scalar"
        );

        // In bounds, reconstructs, and multiplies correctly as shipped.
        let ((neg1, a1), (neg2, a2)) = decompose::<C>(&k);
        assert!(
            a1 >> 127 == 0 && a2 >> 127 == 0,
            "witness must be in bounds"
        );
        let s1 = C::ScalarExt::from_u128(a1);
        let s2 = C::ScalarExt::from_u128(a2);
        let (s1, s2) = (if neg1 { -s1 } else { s1 }, if neg2 { -s2 } else { s2 });
        assert_eq!(s1 + s2 * C::ScalarExt::ZETA, k, "witness must reconstruct");
        assert_eq!(C::generator().mul_glv(&k), C::generator() * k);

        // The boundary geometry under the bit flip.
        let mut g2_bad = C::G2;
        g2_bad[1] ^= 1 << 63;
        let kl = scalar_limbs(&k);
        let c1 = round_mul_shift(&C::G1, &kl);
        let c2 = round_mul_shift(&C::G2, &kl);
        assert_eq!(
            round_mul_shift(&g2_bad, &kl),
            c2 + 1,
            "witness must straddle the rounding boundary"
        );
        let k2_bad = sub256(mul_u128(c1, C::V1B_NEG), mul_u128(c2 + 1, C::V2B));
        let mag = if k2_bad[3] >> 63 == 1 {
            sub256([0; 4], k2_bad)
        } else {
            k2_bad
        };
        assert!(
            mag[2] == 0 && mag[3] == 0,
            "witness |k2'| stays below 2^128"
        );
        let mag = u128::from(mag[0]) | (u128::from(mag[1]) << 64);
        assert!(
            mag >> 127 == 1,
            "flipped G2 must push |k2| past 2^127 at this scalar"
        );
    }

    #[test]
    fn babai_boundary_pallas() {
        babai_boundary_witness::<pallas::Point>(PALLAS_BOUNDARY_SCALAR);
    }
    #[test]
    fn babai_boundary_vesta() {
        babai_boundary_witness::<vesta::Point>(VESTA_BOUNDARY_SCALAR);
    }

    /// Native (constant-time) `Mul` against the whole GLV pipeline at the
    /// boundary scalars — nothing but two multiplications and an equality.
    /// Native multiplication never reads the GLV constants, so the sides
    /// only diverge if the GLV path regresses, and at these scalars it
    /// does so for exactly the suite-invisible corruption identified
    /// above (`G2[1] ^= 1 << 63`): the decomposition half leaves its
    /// 2^127 bound and the pipeline panics on a bound assertion in debug
    /// builds — how tests run. (Any corruption small enough to evade the
    /// known-answer tests keeps `|k2| < 2^128`, which the wNAF ladder
    /// still multiplies correctly, so release products stay numerically
    /// right; the broken invariant is the observable, not a wrong point.)
    /// On the pre-`babai_coefficient_verify` code, this test alone
    /// detects the flip; nothing else in that suite did.
    fn native_vs_glv_boundary<C: GlvParams>(limbs: [u64; 4]) {
        let k = scalar_from_limbs::<C::ScalarExt>(limbs);
        let p = C::generator() * (k + C::ScalarExt::ONE);
        assert_eq!(p.mul_glv(&k), p * k, "GLV must agree with native Mul");
        assert_eq!(C::generator().mul_glv(&k), C::generator() * k);
    }

    #[test]
    fn native_vs_glv_boundary_pallas() {
        native_vs_glv_boundary::<pallas::Point>(PALLAS_BOUNDARY_SCALAR);
    }
    #[test]
    fn native_vs_glv_boundary_vesta() {
        native_vs_glv_boundary::<vesta::Point>(VESTA_BOUNDARY_SCALAR);
    }

    /// Property-based tests: scalars are drawn as four uniform u64 limbs
    /// widened through `from_uniform_bytes` (so the whole field is reachable
    /// without modular bias), and points as `G*(s+1)`.
    mod pbt {
        use group::Group;
        use proptest::prelude::*;

        use super::*;

        fn scalar_strategy<F: PrimeField + ff::FromUniformBytes<64>>() -> impl Strategy<Value = F> {
            proptest::array::uniform4(any::<u64>()).prop_map(|limbs| {
                let mut bytes = [0u8; 64];
                for (i, l) in limbs.iter().enumerate() {
                    bytes[i * 8..(i + 1) * 8].copy_from_slice(&l.to_le_bytes());
                }
                F::from_uniform_bytes(&bytes)
            })
        }

        macro_rules! glv_pbt {
            ($mod_name:ident, $curve:ty) => {
                mod $mod_name {
                    use super::*;

                    type Scalar = <$curve as CurveExt>::ScalarExt;

                    proptest! {
                        /// For all P != O, k: P.mul_glv(k) == P * k.
                        #[test]
                        fn mul_glv_matches_mul(
                            s in scalar_strategy::<Scalar>(),
                            k in scalar_strategy::<Scalar>(),
                        ) {
                            let p = <$curve>::generator() * (s + Scalar::ONE);
                            prop_assert_eq!(p.mul_glv(&k), p * k);
                        }

                        /// For all k: the GLV split reconstructs k with half-width parts.
                        #[test]
                        fn decompose_reconstructs(k in scalar_strategy::<Scalar>()) {
                            let ((neg1, a1), (neg2, a2)) = decompose::<$curve>(&k);
                            prop_assert!(a1 >> 127 == 0);
                            prop_assert!(a2 >> 127 == 0);
                            let s1 = Scalar::from_u128(a1);
                            let s1 = if neg1 { -s1 } else { s1 };
                            let s2 = Scalar::from_u128(a2);
                            let s2 = if neg2 { -s2 } else { s2 };
                            prop_assert_eq!(s1 + s2 * Scalar::ZETA, k);
                        }

                        /// For all points: batched tables act identically to solo tables.
                        #[test]
                        fn batch_equals_solo(
                            seeds in proptest::collection::vec(scalar_strategy::<Scalar>(), 1..8),
                            k in scalar_strategy::<Scalar>(),
                        ) {
                            let points: alloc::vec::Vec<$curve> = seeds
                                .iter()
                                .map(|s| <$curve>::generator() * (*s + Scalar::ONE))
                                .collect();
                            let batched = Table::batch(&points);
                            for (p, table) in points.iter().zip(batched.iter()) {
                                prop_assert_eq!(table.mul(&k), Table::new(p).mul(&k));
                                prop_assert_eq!(table.mul(&k), *p * k);
                            }
                        }

                        /// For all k reused across points: hoisted decomposition == fresh.
                        #[test]
                        fn decomposed_reuse(
                            s in scalar_strategy::<Scalar>(),
                            k in scalar_strategy::<Scalar>(),
                        ) {
                            let p = <$curve>::generator() * (s + Scalar::ONE);
                            let table = Table::new(&p);
                            let hoisted = Decomposed::<$curve>::new(&k);
                            prop_assert_eq!(table.mul_decomposed(&hoisted), table.mul(&k));
                        }
                    }
                }
            };
        }

        glv_pbt!(pallas_pbt, pallas::Point);
        glv_pbt!(vesta_pbt, vesta::Point);
    }
}
