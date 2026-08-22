//! GLV (Gallant–Lambert–Vanstone) scalar multiplication for the Pasta curves.
//!
//! Both Pasta curves carry a cube-root endomorphism
//! $\phi(x, y) = (\zeta x, y)$ (exposed as [`CurveExt::endo`]), for which
//! $\phi(P) = \lambda P$ with $\lambda$ = `Scalar::ZETA`. This module uses
//! that structure twice:
//!
//! - The scalar is split as $k = k_1 + k_2\lambda \pmod n$ with
//!   $|k_1|, |k_2| < 2^{127}$ (Babai rounding against a precomputed short
//!   lattice basis), and the pair is recoded as **one** width-3 NAF digit
//!   string over the Eisenstein integers $\mathbf{Z}[\omega]$
//!   ($\omega^2 + \omega + 1 = 0$, $\omega \mapsto \phi$). Digits are drawn
//!   from $\{0\} \cup U\Delta$, where $U = \{\pm1, \pm\omega, \pm\omega^2\}$
//!   are the units and $\Delta$ eight orbit representatives tiling the 48
//!   odd residue classes mod $8\mathbf{Z}[\omega]$; every nonzero digit is
//!   followed by at least two zeros. The ~127-column shared ladder then
//!   averages ~38–39 digit additions (at most 44), versus ~51 for two
//!   independent width-4 wNAFs over the halves.
//! - A digit $\pm\omega^e\delta$ acts on a stored point by an x-coordinate
//!   rotation (multiplication by $\zeta^e$, precomputed in the [`Table`])
//!   and a y negation, so one 8-orbit table serves all 48 nonzero digits.
//!
//! [`Table::mul_decomposed_batch`] additionally runs one scalar against many
//! points on *affine* accumulators: the digit schedule is shared by the
//! whole batch, so each ladder column batch-inverts its denominators with
//! Montgomery's trick, and every nonzero-digit column is evaluated with a
//! direct affine $2P + D$ formula. Algebraically combining its two dependent
//! chord denominators leaves one inversion batch for the whole column.
//! Exceptional column schedules — those that would hand the affine formula a
//! zero denominator — depend only on the scalar, are checked exactly per
//! batch, and fall back to the per-point ladder.
//!
//! This path is variable-time in the scalar (GLV decomposition plus digit
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
//! - K. Eisenträger, K. Lauter, P. L. Montgomery, "Fast Elliptic Curve
//!   Arithmetic and Improved Weil Pairing Evaluation", CT-RSA 2003.
//!   <https://arxiv.org/abs/math/0208038> (the fused affine $2P + Q$).
//!
//! # Amortization
//!
//! The costs split into three independently reusable pieces:
//!
//! - [`Table`]: per *point*. [`Table::batch`] builds many tables with one
//!   shared batch normalization (a single field inversion for the whole
//!   batch).
//! - [`Decomposed`]: per *scalar*. Decomposition and joint digit recoding
//!   are hoisted so one scalar can be multiplied against many tables.
//! - [`Table::mul_decomposed`] / [`Table::mul_decomposed_batch`]: the
//!   remaining per-(point, scalar) work — a shared-doubling ladder over the
//!   joint digit string, batched across points where the batch is large
//!   enough to amortize its per-column inversions.
//!
//! One-shot use is [`GlvParams::mul_glv`].

use alloc::vec::Vec;
use core::marker::PhantomData;

use ff::{Field, PrimeField, WithSmallOrderMulGroup};
use group::CurveAffine as _;
#[cfg(feature = "multicore")]
use maybe_rayon::prelude::*;

use crate::arithmetic::{mac, sbb, CurveExt};
use crate::{pallas, vesta};

mod private {
    use crate::arithmetic::CurveExt;

    /// Proof-of-crate argument for [`Sealed::affine_unchecked`]: unnameable
    /// outside this crate, with a `pub(super)` field, so downstream code
    /// cannot construct one — not even through a `C: GlvParams` bound, which
    /// does expose supertrait items to generic code.
    #[derive(Debug)]
    pub struct CrateToken(pub(super) ());

    /// Seals [`super::GlvParams`]: the lattice constants are curve-specific
    /// and verified in-crate; external implementations are not supported.
    ///
    /// Also hosts the raw-coordinate plumbing for the digit tables and the
    /// batch-affine ladder, which move between affine points and their
    /// coordinates without per-use on-curve checks (the table and ladder
    /// arithmetic stays on the curve by construction). Keeping the unchecked
    /// constructor here, behind a [`CrateToken`], keeps it out of the
    /// crate's externally callable surface.
    pub trait Sealed: CurveExt {
        /// Constructs an affine point directly from raw coordinates, with no
        /// on-curve check; `(0, 0)` is the affine identity encoding.
        fn affine_unchecked(x: Self::Base, y: Self::Base, token: CrateToken) -> Self::AffineExt;

        /// The raw affine coordinates of `p` (`(0, 0)` for the identity).
        fn affine_xy(p: &Self::AffineExt) -> (Self::Base, Self::Base);

        /// Multiplies base-field values in place, interleaving adjacent pairs
        /// where the backend supports it.
        fn mul_base_assign_pairs(lhs: &mut [Self::Base], rhs: &[Self::Base], _: CrateToken) {
            assert_eq!(lhs.len(), rhs.len());
            for (lhs, rhs) in lhs.iter_mut().zip(rhs) {
                *lhs *= rhs;
            }
        }

        /// Finishes the two-chain back-substitution of a nonzero base-field
        /// batch inversion.
        #[cfg(all(
            feature = "aarch64-asm",
            target_arch = "aarch64",
            target_vendor = "apple"
        ))]
        fn batch_invert_backsub(
            values: &mut [Self::Base],
            prefixes: &[Self::Base],
            acc0: Self::Base,
            acc1: Self::Base,
            token: CrateToken,
        );
    }

    impl Sealed for crate::pallas::Point {
        fn affine_unchecked(x: Self::Base, y: Self::Base, _: CrateToken) -> Self::AffineExt {
            crate::pallas::Affine::from_xy_unchecked(x, y)
        }

        fn affine_xy(p: &Self::AffineExt) -> (Self::Base, Self::Base) {
            p.raw_xy()
        }

        #[cfg(all(
            feature = "aarch64-asm",
            target_arch = "aarch64",
            target_vendor = "apple"
        ))]
        #[inline(always)]
        fn mul_base_assign_pairs(lhs: &mut [Self::Base], rhs: &[Self::Base], _: CrateToken) {
            crate::Fp::mul_assign_pairs_runtime(lhs, rhs)
        }

        #[cfg(all(
            feature = "aarch64-asm",
            target_arch = "aarch64",
            target_vendor = "apple"
        ))]
        #[inline(always)]
        fn batch_invert_backsub(
            values: &mut [Self::Base],
            prefixes: &[Self::Base],
            acc0: Self::Base,
            acc1: Self::Base,
            _: CrateToken,
        ) {
            crate::Fp::batch_invert_backsub_runtime(values, prefixes, acc0, acc1)
        }
    }

    impl Sealed for crate::vesta::Point {
        fn affine_unchecked(x: Self::Base, y: Self::Base, _: CrateToken) -> Self::AffineExt {
            crate::vesta::Affine::from_xy_unchecked(x, y)
        }

        fn affine_xy(p: &Self::AffineExt) -> (Self::Base, Self::Base) {
            p.raw_xy()
        }

        #[cfg(all(
            feature = "aarch64-asm",
            target_arch = "aarch64",
            target_vendor = "apple"
        ))]
        #[inline(always)]
        fn mul_base_assign_pairs(lhs: &mut [Self::Base], rhs: &[Self::Base], _: CrateToken) {
            crate::Fq::mul_assign_pairs_runtime(lhs, rhs)
        }

        #[cfg(all(
            feature = "aarch64-asm",
            target_arch = "aarch64",
            target_vendor = "apple"
        ))]
        #[inline(always)]
        fn batch_invert_backsub(
            values: &mut [Self::Base],
            prefixes: &[Self::Base],
            acc0: Self::Base,
            acc1: Self::Base,
            _: CrateToken,
        ) {
            crate::Fq::batch_invert_backsub_runtime(values, prefixes, acc0, acc1)
        }
    }
}

/// Per-curve GLV constants: a short basis for the lattice
/// $\{(a, b) : a + b\lambda \equiv 0 \pmod n\}$ — where $n$ is the order of the
/// group (equivalently the scalar field modulus) and $\lambda$ = `Scalar::ZETA`
/// — together with the Babai rounding coefficients derived from that basis.
///
/// This trait is sealed; it is implemented for [`pallas::Point`] and
/// [`vesta::Point`]. (The private seal also hosts the raw-coordinate
/// plumbing used by the digit tables and the batch-affine ladder, keeping
/// its unchecked affine constructor uncallable outside the crate.)
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
/// (asserted in debug builds here, in every profile by [`Decomposed::new`],
/// and checked by the `decompose` tests), so the high limbs of the magnitude
/// are always zero and no information is lost.
fn signed_halves(x: [u64; 4]) -> (bool, u128) {
    // Guard the truncation itself: the discarded limbs must be the sign
    // extension of bit 127. Values of 2^128 or more would otherwise be
    // silently truncated before the recoder's magnitude assertion could
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

/// The eight Eisenstein digit-orbit representatives $\Delta$, as coefficient
/// pairs $(a, b)$ of $a + b\omega$ (norms 1, 3, 7, 7, 9, 13, 13, 19). The
/// 48 nonzero digits are $U\Delta$ for the six units
/// $U = \{\pm1, \pm\omega, \pm\omega^2\}$, and tile the odd residue classes
/// mod $8\mathbf{Z}[\omega]$ exactly (64 classes, minus the 16 divisible by
/// 2, each hit once) — re-derived by the
/// `joint_digit_table_matches_first_principles` test.
const DELTA: [(i8, i8); 8] = [
    (1, 0),
    (1, -1),
    (2, -1),
    (1, -2),
    (3, 0),
    (3, -1),
    (1, -3),
    (2, -3),
];

/// Digit lookup for the joint recoding, indexed by
/// `((a mod 8) << 3) | (b mod 8)`: entry `(da, db, code)` is the unique
/// element $d_a + d_b\omega$ of $U\Delta$ congruent to $a + b\omega$ mod
/// $8\mathbf{Z}[\omega]$, or `(0, 0, 0)` for the 16 classes divisible by 2
/// (where the recoder emits a zero digit). `code` packs
/// `1 + 6*orbit + unit`, with units ordered
/// `[+1, -1, +ω, -ω, +ω², -ω²]` (so `unit >> 1` is the rotation exponent and
/// `unit & 1` the negation); the
/// `joint_digit_table_matches_first_principles` test rebuilds every entry
/// from those definitions.
#[rustfmt::skip]
const JOINT_DIGITS: [(i8, i8, u8); 64] = [
    (0, 0, 0), (0, 1, 3), (0, 0, 0), (0, 3, 27), (0, 0, 0), (0, -3, 28), (0, 0, 0), (0, -1, 4),
    (1, 0, 1), (1, 1, 6), (1, 2, 9), (1, 3, 15), (1, 4, 33), (1, -3, 37), (1, -2, 19), (1, -1, 7),
    (0, 0, 0), (2, 1, 12), (0, 0, 0), (2, 3, 21), (0, 0, 0), (2, -3, 43), (0, 0, 0), (2, -1, 13),
    (3, 0, 25), (3, 1, 24), (3, 2, 18), (3, 3, 30), (3, 4, 39), (3, 5, 45), (-5, -2, 47), (3, -1, 31),
    (0, 0, 0), (4, 1, 42), (0, 0, 0), (4, 3, 36), (0, 0, 0), (-4, -3, 35), (0, 0, 0), (-4, -1, 41),
    (-3, 0, 26), (-3, 1, 32), (5, 2, 48), (-3, -5, 46), (-3, -4, 40), (-3, -3, 29), (-3, -2, 17), (-3, -1, 23),
    (0, 0, 0), (-2, 1, 14), (0, 0, 0), (-2, 3, 44), (0, 0, 0), (-2, -3, 22), (0, 0, 0), (-2, -1, 11),
    (-1, 0, 2), (-1, 1, 8), (-1, 2, 20), (-1, 3, 38), (-1, -4, 34), (-1, -3, 16), (-1, -2, 10), (-1, -1, 5),
];

/// Upper bound on the number of joint digit positions. The recoding
/// coefficients start below `2^127` and each step at least halves them up
/// to a coefficient-5 digit (`r' <= (r + 5)/2`), so 127 steps reach the box
/// `max(|a|, |b|) <= 5`; exhaustive search over that box (the
/// `tail_bound_exhaustive` test) shows at most 5 further positions.
const MAX_JOINT_DIGITS: usize = 132;

/// Splits a nonzero digit code into `(orbit, rotation, negate)`.
fn decode_digit(code: u8) -> (usize, usize, bool) {
    debug_assert!((1..=48).contains(&code), "invalid digit code");
    let v = usize::from(code - 1);
    (v / 6, (v % 6) >> 1, (v % 6) & 1 == 1)
}

/// The Eisenstein coefficients `(a, b)` of a nonzero digit code, i.e. the
/// digit as $a + b\omega$. Both are at most 5 in magnitude.
fn digit_coeffs(code: u8) -> (i8, i8) {
    let (orbit, e, negate) = decode_digit(code);
    let (mut a, mut b) = DELTA[orbit];
    // Multiplication by omega: (a + b*omega)*omega = -b + (a - b)*omega.
    for _ in 0..e {
        let (ra, rb) = (-b, a - b);
        a = ra;
        b = rb;
    }
    if negate {
        a = -a;
        b = -b;
    }
    (a, b)
}

/// The scalar a nonzero digit multiplies the base point by:
/// $a + b\lambda \pmod n$. Never zero — the digit's Eisenstein norm
/// $a^2 - ab + b^2$ is a nonzero integer of at most 75, far below $n$.
fn digit_scalar<F: WithSmallOrderMulGroup<3>>(code: u8) -> F {
    let (da, db) = digit_coeffs(code);
    let signed = |v: i8| {
        let m = F::from(u64::from(v.unsigned_abs()));
        if v < 0 {
            -m
        } else {
            m
        }
    };
    signed(da) + signed(db) * F::ZETA
}

/// Joint width-3 NAF recoding of $a + b\omega$ over the Eisenstein integers,
/// lowest position first: while the value is nonzero, emit 0 if it is
/// divisible by 2 (both coefficients even), else the unique $U\Delta$ digit
/// congruent to it mod $8\mathbf{Z}[\omega]$; then subtract and halve. A
/// nonzero digit leaves a multiple of 8, so the following two digits are
/// forced zeros.
///
/// The subtract-and-halve is computed as `(a >> 1) - (da >> 1)`, exact
/// because `a ≡ da (mod 2)` in every case (zero digits are only emitted when
/// both coefficients are even, and nonzero digits match the value's residue
/// class); the naive `(a - da) / 2` could overflow `i128` by up to 4 when
/// `|a|` starts at its `2^127 - 1` bound.
fn joint_digits(mut a: i128, mut b: i128) -> ([u8; MAX_JOINT_DIGITS], usize) {
    let mut digits = [0u8; MAX_JOINT_DIGITS];
    let mut n = 0;
    while a != 0 || b != 0 {
        let idx = (((a & 7) << 3) | (b & 7)) as usize;
        let (da, db, code) = JOINT_DIGITS[idx];
        digits[n] = code;
        a = (a >> 1) - (i128::from(da) >> 1);
        b = (b >> 1) - (i128::from(db) >> 1);
        n += 1;
    }
    (digits, n)
}

/// Batches of at least this many live (non-identity) points take the
/// batch-affine ladder in [`Table::mul_decomposed_batch`]; smaller ones fall
/// back to per-point Jacobian ladders.
///
/// Per point, the affine ladder replaces the Jacobian ladder's
/// `127·(2M + 5S) + H·(7M + 4S)` with `(5D + 4H)M + 2D·S` plus a
/// `(D + H)/n` share of one field inversion per ladder column phase
/// (`D ≈ 127` doublings, `H ≈ 39` active columns): it eliminates ~585
/// squarings but adds ~264 multiplications and the shared inversions.
/// With this crate's divstep inversion (measured `I/M ≈ 77`, `S/M ≈ 0.86`
/// on Apple aarch64 with the assembly backend) the operation-count model
/// that put break-even at `n ≈ 365` under the old Fermat inversion
/// (`I/M ≈ 440`) scales linearly in `I` to `n ≈ 64`; the ladder's lean
/// nonzero-only batched inversions (see [`batch_invert_nonzero`]) shave a
/// further few multiplications' worth per point per column, and the
/// *measured* curve (same-scalar batch benches in `benches/glv.rs`,
/// kernel forced on at every size) ties the per-point Jacobian ladders at
/// 32 points (−0.1% on both curves), and wins ~5% per point at 64 and
/// ~10% at 128. The threshold sits on that measured break-even, so
/// smaller batches keep the plain per-point ladders. (The Fermat-era gate
/// was 512: the cheaper inversion moved break-even to 64, and dropping
/// `ff::BatchInverter`'s per-element zero handling moved it to 32.)
const BATCH_AFFINE_MIN_POINTS: usize = 32;
// This range is tuned for the k = 11 parameter generation used by Orchard.
// Larger domains retain the point-major schedule above the measured range.
const TWIDDLE_MAJOR_MIN_CHUNK: usize = 16;
const TWIDDLE_MAJOR_MAX_CHUNK: usize = 2048;

/// Montgomery-batched inversion for a nonempty slice of provably nonzero
/// values: prefix products into `scratch`, one shared field inversion,
/// back-substitution. The ladder's denominators are guaranteed nonzero by
/// [`affine_ladder_safe`], so unlike `ff::BatchInverter` this skips the
/// per-element zero handling (one extra multiplication and two conditional
/// selects per element), which is a measurable share of each ladder column.
/// Twin implementation: `batch_invert_multi` in
/// `halo2_proofs/src/arithmetic.rs` is the same even/odd two-lane walk with
/// `ff`-style (variable-time) zero skipping and internally allocated
/// scratch; `Curve::batch_normalize` in `src/curves.rs` fuses the walk with
/// the Jacobian-to-affine conversion. Keep the three in step when changing
/// any of them.
#[cfg(all(
    feature = "aarch64-asm",
    target_arch = "aarch64",
    target_vendor = "apple"
))]
fn batch_invert_nonzero<C: GlvParams>(values: &mut [C::Base], scratch: &mut [C::Base]) {
    assert_eq!(values.len(), scratch.len());
    assert!(!values.is_empty());
    if values.len() == 1 {
        scratch[0] = C::Base::ONE;
        values[0] = values[0].invert().unwrap();
        return;
    }
    // Two accumulator chains, stepped in (even, odd) pairs: the classic
    // single-chain walk runs both passes at the field multiplication's
    // dependency latency, while independent even/odd chains run at its
    // throughput, for a fixed overhead of three extra multiplications per
    // call (one join before the shared inversion, two lane-seed recoveries
    // after). Each chain starts from its first value, avoiding a field
    // multiplication by one. The ladder only calls this with
    // `BATCH_AFFINE_MIN_POINTS` or more live lanes — at the measured two-lane
    // crossover on both x86-64 (portable) and Apple aarch64 (assembly
    // backend) — so no small-batch fallback is needed. A trailing element
    // (odd length) has an even index and belongs to the first chain.
    debug_assert!(!values[0].is_zero_vartime());
    debug_assert!(!values[1].is_zero_vartime());
    scratch[0] = C::Base::ONE;
    scratch[1] = C::Base::ONE;
    let mut acc0 = values[0];
    let mut acc1 = values[1];
    for (pair, slots) in values[2..]
        .chunks_exact(2)
        .zip(scratch[2..].chunks_exact_mut(2))
    {
        debug_assert!(!pair[0].is_zero_vartime());
        debug_assert!(!pair[1].is_zero_vartime());
        slots[0] = acc0;
        acc0 *= pair[0];
        slots[1] = acc1;
        acc1 *= pair[1];
    }
    if let (Some(value), Some(slot)) = (
        values.chunks_exact(2).remainder().first(),
        scratch.chunks_exact_mut(2).into_remainder().first_mut(),
    ) {
        debug_assert!(!value.is_zero_vartime());
        *slot = acc0;
        acc0 *= value;
    }

    // A product of nonzero field elements is nonzero, so this cannot fail.
    let inverse = (acc0 * acc1).invert().unwrap();
    let seed0 = inverse * acc1;
    let seed1 = inverse * acc0;
    C::batch_invert_backsub(values, scratch, seed0, seed1, private::CrateToken(()));
}

#[cfg(not(all(
    feature = "aarch64-asm",
    target_arch = "aarch64",
    target_vendor = "apple"
)))]
fn batch_invert_nonzero<F: Field>(values: &mut [F], scratch: &mut [F]) {
    assert_eq!(values.len(), scratch.len());
    assert!(!values.is_empty());
    if values.len() == 1 {
        scratch[0] = F::ONE;
        values[0] = values[0].invert().unwrap();
        return;
    }
    // Two accumulator chains, stepped in (even, odd) pairs: the classic
    // single-chain walk runs both passes at the field multiplication's
    // dependency latency, while independent even/odd chains run at its
    // throughput, for a fixed overhead of three extra multiplications per
    // call (one join before the shared inversion, two lane-seed recoveries
    // after). Each chain starts from its first value, avoiding a field
    // multiplication by one. The ladder only calls this with
    // `BATCH_AFFINE_MIN_POINTS` or more live lanes — at the measured two-lane
    // crossover on both x86-64 (portable) and Apple aarch64 (assembly
    // backend) — so no small-batch fallback is needed. A trailing element
    // (odd length) has an even index and belongs to the first chain.
    debug_assert!(!values[0].is_zero_vartime());
    debug_assert!(!values[1].is_zero_vartime());
    scratch[0] = F::ONE;
    scratch[1] = F::ONE;
    let mut acc0 = values[0];
    let mut acc1 = values[1];
    for (pair, slots) in values[2..]
        .chunks_exact(2)
        .zip(scratch[2..].chunks_exact_mut(2))
    {
        debug_assert!(!pair[0].is_zero_vartime());
        debug_assert!(!pair[1].is_zero_vartime());
        slots[0] = acc0;
        acc0 *= pair[0];
        slots[1] = acc1;
        acc1 *= pair[1];
    }
    if let (Some(value), Some(slot)) = (
        values.chunks_exact(2).remainder().first(),
        scratch.chunks_exact_mut(2).into_remainder().first_mut(),
    ) {
        debug_assert!(!value.is_zero_vartime());
        *slot = acc0;
        acc0 *= value;
    }

    // A product of nonzero field elements is nonzero, so this cannot fail.
    let inverse = (acc0 * acc1).invert().unwrap();
    let seed0 = inverse * acc1;
    let seed1 = inverse * acc0;
    let mut acc0 = seed0;
    let mut acc1 = seed1;

    if let (Some(value), Some(slot)) = (
        values.chunks_exact_mut(2).into_remainder().first_mut(),
        scratch.chunks_exact(2).remainder().first(),
    ) {
        let inverted = acc0 * slot;
        acc0 *= *value;
        *value = inverted;
    }
    for (pair, slots) in values
        .chunks_exact_mut(2)
        .zip(scratch.chunks_exact(2))
        .rev()
    {
        let inverted0 = acc0 * slots[0];
        let inverted1 = acc1 * slots[1];
        acc0 *= pair[0];
        acc1 *= pair[1];
        pair[0] = inverted0;
        pair[1] = inverted1;
    }
}

/// Denominator and reusable square for the one-inversion affine `2P + Q`
/// formula.
#[cfg(test)]
#[inline(always)]
fn double_add_denominator<F: Field>(x: F, y: F, u: F, v: F) -> (F, F) {
    let h = u - x;
    let r = v - y;
    let h_squared = h.square();
    let denominator = h_squared * (x.double() + u) - r.square();
    (denominator, h_squared)
}

/// Completes the one-inversion affine `2P + Q` formula from the inverse of
/// [`double_add_denominator`].
#[cfg(test)]
#[inline(always)]
fn double_add_finish<F: Field>(
    x: F,
    y: F,
    u: F,
    v: F,
    h_squared: F,
    denominator_inverse: F,
) -> (F, F) {
    let h = u - x;
    let r = v - y;
    let a = y * denominator_inverse;
    let b = a * h;
    let c = b * h_squared;
    let lambda = c - r;
    let x2 = u + (b * lambda).double().double();
    let y2 = -y - (F::ONE + (a * lambda).double().double()) * (lambda + c);
    (x2, y2)
}

/// Completes a batch of one-inversion affine `2P + Q` formulas stage by
/// stage, so adjacent field multiplications can share one backend invocation.
/// Each intermediate overwrites an input after its final use.
fn double_add_finish_batch<C: GlvParams>(
    y: &[C::Base],
    h: &mut [C::Base],
    r: &mut [C::Base],
    h_squared: &mut [C::Base],
    denominator_inverse: &mut [C::Base],
) {
    let token = private::CrateToken(());
    C::mul_base_assign_pairs(denominator_inverse, y, token);
    C::mul_base_assign_pairs(h, denominator_inverse, private::CrateToken(()));
    C::mul_base_assign_pairs(h_squared, h, private::CrateToken(()));
    for i in 0..r.len() {
        r[i] = h_squared[i] - r[i];
    }
    C::mul_base_assign_pairs(h, r, private::CrateToken(()));
    C::mul_base_assign_pairs(denominator_inverse, r, private::CrateToken(()));
    for ((factor, square), lambda) in denominator_inverse
        .iter_mut()
        .zip(h_squared.iter_mut())
        .zip(r)
    {
        *factor = C::Base::ONE + factor.double().double();
        *square += *lambda;
    }
    C::mul_base_assign_pairs(denominator_inverse, h_squared, private::CrateToken(()));
}

/// Small MSMs do not amortize GLV decomposition, affine endomorphism mapping,
/// and the two temporary vectors.
const MIN_GLV_MULTIEXP_TERMS: usize = 256;

/// Each GLV decomposition component has magnitude strictly below `2^127`.
const GLV_COMPONENT_BITS: usize = 127;

/// Estimates the dominant group work in a Signed-Booth MSM.
///
/// The model counts one unit for each point/window visit, two bucket additions
/// per bucket/window for summation by parts, and each accumulator doubling.
/// It deliberately omits GLV setup costs; [`MIN_GLV_MULTIEXP_TERMS`] handles
/// their small-MSM amortization separately.
fn estimated_signed_booth_work(
    terms: usize,
    scalar_bits: usize,
    window_bits: usize,
) -> Option<usize> {
    let windows = scalar_bits.checked_div(window_bits)?.checked_add(1)?;
    let bucket_shift = u32::try_from(window_bits.checked_sub(1)?).ok()?;
    let buckets = 1usize.checked_shl(bucket_shift)?;

    let point_visits = terms.checked_mul(windows)?;
    let bucket_additions = buckets.checked_mul(windows)?.checked_mul(2)?;
    let doublings = window_bits.checked_mul(windows.checked_sub(1)?)?;
    point_visits
        .checked_add(bucket_additions)?
        .checked_add(doublings)
}

/// Floors of `e^k` for `k = 4..=22`.
///
/// These preserve the established `ceil(ln(terms))` window schedule without
/// requiring floating-point transcendental functions, which are unavailable
/// in `no_std` builds.
const DEFAULT_MULTIEXP_WINDOW_THRESHOLDS: [u32; 19] = [
    54,
    148,
    403,
    1_096,
    2_980,
    8_103,
    22_026,
    59_874,
    162_754,
    442_413,
    1_202_604,
    3_269_017,
    8_886_110,
    24_154_952,
    65_659_969,
    178_482_300,
    485_165_195,
    1_318_815_734,
    3_584_912_846,
];

fn default_multiexp_window_bits(terms: usize) -> Option<usize> {
    if terms < 4 {
        Some(1)
    } else if terms < 32 {
        Some(3)
    } else {
        let terms = u32::try_from(terms).ok()?;
        let threshold = DEFAULT_MULTIEXP_WINDOW_THRESHOLDS
            .iter()
            .position(|upper| terms <= *upper)
            .unwrap_or(DEFAULT_MULTIEXP_WINDOW_THRESHOLDS.len());
        Some(4 + threshold)
    }
}

fn scalar_repr_bits<C: GlvParams>() -> Option<usize> {
    <C::ScalarExt as PrimeField>::Repr::default()
        .as_ref()
        .len()
        .checked_mul(u8::BITS as usize)
}

/// Selects the backend's signed-window width.
///
/// The accepted serial sweep found a wider successor useful only when the
/// default selected 9 bits. Keep that comparison narrow because the operation
/// model deliberately omits cache behavior.
fn multiexp_window_bits<C: GlvParams>(terms: usize, num_threads: usize) -> Option<usize> {
    let window_bits = default_multiexp_window_bits(terms)?;
    if num_threads != 1 || window_bits != 9 {
        return Some(window_bits);
    }

    let scalar_bits = scalar_repr_bits::<C>()?;
    let next_window_bits = window_bits.checked_add(1)?;
    let current = estimated_signed_booth_work(terms, scalar_bits, window_bits);
    let next = estimated_signed_booth_work(terms, scalar_bits, next_window_bits);
    Some(
        if matches!((current, next), (Some(current), Some(next)) if next < current) {
            next_window_bits
        } else {
            window_bits
        },
    )
}

/// Chooses GLV only when its estimated Signed-Booth work is lower.
fn should_use_glv_multiexp<C: GlvParams>(terms: usize, window_bits: usize) -> bool {
    if terms < MIN_GLV_MULTIEXP_TERMS {
        return false;
    }

    let scalar_bits = scalar_repr_bits::<C>();
    let glv_terms = terms.checked_mul(2);

    match (scalar_bits, glv_terms) {
        (Some(scalar_bits), Some(glv_terms)) => {
            match (
                estimated_signed_booth_work(terms, scalar_bits, window_bits),
                estimated_signed_booth_work(glv_terms, GLV_COMPONENT_BITS, window_bits),
            ) {
                (Some(generic), Some(glv)) => glv < generic,
                _ => false,
            }
        }
        _ => false,
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

/// Converts decomposed halves into the representation used by the
/// Signed-Booth MSM, rejecting values outside the decomposition bound.
///
/// This check must remain on the MSM path because it does not construct a
/// [`Decomposed`], whose constructor enforces the same bound. Returning
/// `None` lets the caller use the generic MSM instead of panicking. The
/// rejection boundary is covered by
/// `multiexp_component_guard_returns_none_out_of_bounds`.
fn checked_signed_magnitudes(
    (first, second): ((bool, u128), (bool, u128)),
) -> Option<(SignedMagnitude, SignedMagnitude)> {
    if first.1 >> GLV_COMPONENT_BITS == 0 && second.1 >> GLV_COMPONENT_BITS == 0 {
        Some((first.into(), second.into()))
    } else {
        None
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

#[derive(Clone, Copy)]
enum MultiexpBucket<C: GlvParams> {
    None,
    Affine(C::AffineExt),
    Projective(C),
}

impl<C: GlvParams> MultiexpBucket<C> {
    fn add_assign(&mut self, point: C::AffineExt) {
        *self = match *self {
            Self::None => Self::Affine(point),
            Self::Affine(current) => Self::Projective(current + point),
            Self::Projective(mut current) => {
                current += point;
                Self::Projective(current)
            }
        };
    }

    fn add(self, mut other: C) -> C {
        match self {
            Self::None => other,
            Self::Affine(point) => {
                other += point;
                other
            }
            Self::Projective(point) => other + point,
        }
    }
}

fn add_digit<C: GlvParams>(
    buckets: &mut [MultiexpBucket<C>],
    digit: BoothDigit,
    base: C::AffineExt,
) {
    if digit.magnitude != 0 {
        let base = if digit.negative { -base } else { base };
        buckets[digit.magnitude - 1].add_assign(base);
    }
}

fn sum_buckets<C: GlvParams>(buckets: &[MultiexpBucket<C>]) -> C {
    let mut running = C::identity();
    let mut sum = C::identity();
    for bucket in buckets.iter().rev() {
        running = bucket.add(running);
        sum += running;
    }
    sum
}

fn multiexp<C: GlvParams>(
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[C::AffineExt],
    endo_bases: &[C::AffineExt],
    window_bits: usize,
) -> C {
    debug_assert_eq!(components.len(), bases.len());
    debug_assert_eq!(components.len(), endo_bases.len());

    let window_count = GLV_COMPONENT_BITS / window_bits + 1;
    let mut buckets = alloc::vec![MultiexpBucket::<C>::None; 1 << (window_bits - 1)];
    let mut acc = C::identity();

    for window in (0..window_count).rev() {
        if window + 1 != window_count {
            for _ in 0..window_bits {
                acc = acc.double();
            }
        }

        buckets.fill(MultiexpBucket::None);
        for ((first, second), base, endo_base) in components
            .iter()
            .zip(bases)
            .zip(endo_bases)
            .map(|(((first, second), base), endo_base)| ((first, second), base, endo_base))
        {
            add_digit(
                &mut buckets,
                booth_digit(*first, window_bits, window),
                *base,
            );
            add_digit(
                &mut buckets,
                booth_digit(*second, window_bits, window),
                *endo_base,
            );
        }
        acc += sum_buckets(&buckets);
    }
    acc
}

/// Attempts a GLV Signed-Booth multiscalar multiplication for a large Pasta
/// MSM.
pub(crate) fn try_multiexp<C: GlvParams>(
    scalars: &[C::ScalarExt],
    bases: &[C::AffineExt],
) -> Option<C> {
    assert_eq!(scalars.len(), bases.len());
    let window_bits = multiexp_window_bits::<C>(scalars.len(), 1)?;
    if !should_use_glv_multiexp::<C>(scalars.len(), window_bits) {
        return None;
    }

    let components = scalars
        .iter()
        .map(decompose::<C>)
        .map(checked_signed_magnitudes)
        .collect::<Option<Vec<_>>>()?;
    let endo_bases = bases
        .iter()
        .map(|base| {
            let (x, y) = C::affine_xy(base);
            C::affine_unchecked(x * C::Base::ZETA, y, private::CrateToken(()))
        })
        .collect::<Vec<_>>();
    Some(multiexp(&components, bases, &endo_bases, window_bits))
}

/// The GLV digit window for one base point: the eight Eisenstein orbit
/// representatives $[\Delta_i]P$ in affine coordinates, with each
/// x-coordinate stored in all three $\zeta$-rotations (so applying the
/// endomorphism part of a digit is a lookup, not a multiplication) alongside
/// the shared y-coordinates. 1 KiB per table.
///
/// Build one with [`Table::new`], or many with one shared normalization via
/// [`Table::batch`].
#[derive(Clone, Copy, Debug)]
pub struct Table<C: GlvParams> {
    /// `xs[e][i]` = $\zeta^e \cdot x([\Delta_i]P)$.
    xs: [[C::Base; 8]; 3],
    /// `ys[i]` = $y([\Delta_i]P)$.
    ys: [C::Base; 8],
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

    /// The eight projective orbit representatives $[\Delta_i]P$, in orbit
    /// order. Seven full additions plus endomorphism applications (one
    /// base-field multiplication each) and negations; no inversions, so the
    /// entries ride along in the caller's shared normalization.
    ///
    /// The chain reaches every orbit through intermediate multiples (the
    /// Eisenstein multiplier of `p` is annotated); conjugate pairs like
    /// `phi_p ± m3` share their intermediates, and the trailing unit of
    /// each chain output is stripped with endomorphism rotations and
    /// negations, which cost one multiplication at most each. The
    /// `orbit_points` test checks every entry (and every stored rotation)
    /// against the native scalar multiplication.
    fn window_proj(p: &C) -> [C; 8] {
        let phi_p = p.endo(); // ω
        let d1 = *p - phi_p; // 1 - ω
        let b = d1 - d1.endo(); // (1 - ω)² = -3ω
        let b_endo = b.endo(); // -3ω²
        let m3 = b_endo.endo(); // -3
        let t3a = phi_p + m3; // -3 + ω
        let t3b = phi_p - m3; // 3 + ω
        let r3 = -b_endo; // 3ω²
        let t4a = phi_p + r3; // -3 - 2ω
        let t4b = phi_p - r3; // 3 + 4ω
        let t19 = phi_p + t4b; // 3 + 5ω
        [
            *p,                // Δ0 = 1
            d1,                // Δ1 = 1 - ω
            t4a.endo(),        // Δ2 = 2 - ω   = ω(-3 - 2ω)
            -t3b.endo(),       // Δ3 = 1 - 2ω  = -ω(3 + ω)
            -m3,               // Δ4 = 3
            -t3a,              // Δ5 = 3 - ω
            t4b.endo().endo(), // Δ6 = 1 - 3ω  = ω²(3 + 4ω)
            t19.endo().endo(), // Δ7 = 2 - 3ω  = ω²(3 + 5ω)
        ]
    }

    /// Assembles a table from one normalized 8-entry window of orbit
    /// representatives, materializing the $\zeta$-rotations of each
    /// x-coordinate (eight multiplications per table). Since $\zeta$ is a
    /// nontrivial cube root of unity, $\zeta^2x = -x - \zeta x$.
    fn from_window(w: &[C::AffineExt]) -> Self {
        let mut xs = [[C::Base::ZERO; 8]; 3];
        let mut ys = [C::Base::ZERO; 8];
        for (i, p) in w.iter().enumerate() {
            let (x, y) = C::affine_xy(p);
            let xz = x * C::Base::ZETA;
            xs[0][i] = x;
            xs[1][i] = xz;
            xs[2][i] = -x - xz;
            ys[i] = y;
        }
        Table { xs, ys }
    }

    /// Whether this is the table of the identity point. Identity windows
    /// are all-`(0, 0)`, and no valid point has `y = 0` (the group has odd
    /// prime order, hence no 2-torsion), so `y` is a reliable sentinel.
    fn is_identity(&self) -> bool {
        self.ys[0].is_zero().into()
    }

    /// The affine coordinates contributed by a nonzero digit:
    /// $\pm\phi^e([\Delta_i]P)$, one table lookup and at most one field
    /// negation.
    fn digit_coords(&self, code: u8) -> (C::Base, C::Base) {
        let (orbit, e, negate) = decode_digit(code);
        let x = self.xs[e][orbit];
        let y = if negate {
            -self.ys[orbit]
        } else {
            self.ys[orbit]
        };
        (x, y)
    }

    /// The affine point contributed by a nonzero digit.
    fn digit_point(&self, code: u8) -> C::AffineExt {
        let (x, y) = self.digit_coords(code);
        C::affine_unchecked(x, y, private::CrateToken(()))
    }

    /// The base point P (= the Δ0 orbit entry) back as a projective point.
    #[cfg(test)]
    fn point(&self) -> C {
        C::from(C::affine_unchecked(
            self.xs[0][0],
            self.ys[0],
            private::CrateToken(()),
        ))
    }

    /// `k * P` for the P encoded by this table, decomposing `k` on the spot.
    ///
    /// When one scalar meets many tables, decompose once with
    /// [`Decomposed::new`] and use [`Table::mul_decomposed`] (or
    /// [`Table::mul_decomposed_batch`]) instead.
    pub fn mul(&self, k: &C::ScalarExt) -> C {
        self.mul_decomposed(&Decomposed::new(k))
    }

    /// `k * P` for the P encoded by this table, via the shared-doubling
    /// ladder over the joint Eisenstein digit string. Identical to `P * k`
    /// (tested).
    pub fn mul_decomposed(&self, k: &Decomposed<C>) -> C {
        let mut acc = C::identity();
        for (i, &code) in k.digits[..k.len].iter().enumerate().rev() {
            // `acc` is still the identity on the first iteration; skip the
            // wasted doubling.
            if i + 1 < k.len {
                acc = acc.double();
            }
            if code != 0 {
                acc += self.digit_point(code);
            }
        }
        acc
    }

    /// One `k * P` per table, sharing the whole column schedule across the
    /// batch. Identical, table by table, to [`Table::mul_decomposed`]
    /// (tested).
    ///
    /// With at least [`BATCH_AFFINE_MIN_POINTS`] live (non-identity) tables,
    /// and for every scalar whose column schedule avoids the affine
    /// formulas' exceptional cases (checked exactly per call; random scalars
    /// fail the check with probability ~2^-124), the ladder runs on affine
    /// accumulators: each column batch-inverts its denominators via
    /// Montgomery's trick and each nonzero-digit column uses a direct affine
    /// $2P + D$ formula with one inversion batch. Otherwise every table falls
    /// back to its own per-point ladder.
    pub fn mul_decomposed_batch(tables: &[&Self], k: &Decomposed<C>) -> Vec<C> {
        if k.len == 0 {
            // k = 0: every product is the identity.
            return alloc::vec![C::identity(); tables.len()];
        }
        let live: Vec<&Self> = tables
            .iter()
            .copied()
            .filter(|t| !t.is_identity())
            .collect();
        if live.len() < BATCH_AFFINE_MIN_POINTS || !k.affine_ladder_safe {
            return tables.iter().map(|t| t.mul_decomposed(k)).collect();
        }
        let mut products = Self::batch_affine_ladder(&live, k).into_iter();
        tables
            .iter()
            .map(|t| {
                if t.is_identity() {
                    C::identity()
                } else {
                    C::from(products.next().expect("one product per live table"))
                }
            })
            .collect()
    }

    /// The synchronized batch-affine ladder. Callers guarantee: `k.len > 0`,
    /// every table is non-identity, and the schedule passed
    /// [`affine_ladder_safe`] (so no denominator below is zero and no
    /// accumulator is ever the identity).
    #[allow(clippy::needless_range_loop)]
    fn batch_affine_ladder(live: &[&Self], k: &Decomposed<C>) -> Vec<C::AffineExt> {
        let n = live.len();
        // Affine accumulators (structure-of-arrays), initialized from the
        // top digit — the ladder's first column is the digit itself.
        let mut xs = Vec::with_capacity(n);
        let mut ys = Vec::with_capacity(n);
        for t in live {
            let (x, y) = t.digit_coords(k.digits[k.len - 1]);
            xs.push(x);
            ys.push(y);
        }
        let mut scratch = alloc::vec![C::Base::ZERO; n];
        let mut h_squares = alloc::vec![C::Base::ZERO; n];
        let mut h = alloc::vec![C::Base::ZERO; n];
        let mut r = alloc::vec![C::Base::ZERO; n];
        let mut a = alloc::vec![C::Base::ZERO; n];

        for &code in k.digits[..k.len - 1].iter().rev() {
            if code == 0 {
                // Batched affine doubling: m = 3x²/(2y), x' = m² - 2x,
                // y' = m(x - x') - y. Asymptotically 5M + 2S per point
                // (2M + 2S here, 3M inside the shared inversion).
                for (a, y) in a.iter_mut().zip(&ys) {
                    *a = y.double();
                }
                #[cfg(all(
                    feature = "aarch64-asm",
                    target_arch = "aarch64",
                    target_vendor = "apple"
                ))]
                batch_invert_nonzero::<C>(&mut a, &mut scratch);
                #[cfg(not(all(
                    feature = "aarch64-asm",
                    target_arch = "aarch64",
                    target_vendor = "apple"
                )))]
                batch_invert_nonzero(&mut a, &mut scratch);
                for i in 0..n {
                    let xx = xs[i].square();
                    let m = (xx.double() + xx) * a[i];
                    let x2 = m.square() - xs[i].double();
                    ys[i] = m * (xs[i] - x2) - ys[i];
                    xs[i] = x2;
                }
            } else {
                let (orbit, e, negate) = decode_digit(code);
                // Direct affine 2P + D. Algebraically combining the two
                // dependent chord denominators leaves one inversion batch
                // and 7M + 2S of formula work per point. After Montgomery
                // batching that is 10M + 2S, one multiplication more than
                // the two-batch formula, but it removes the second pass and
                // its intermediate slope and x-coordinate vectors.
                for i in 0..n {
                    let u = live[i].xs[e][orbit];
                    let v = if negate {
                        -live[i].ys[orbit]
                    } else {
                        live[i].ys[orbit]
                    };
                    h[i] = u - xs[i];
                    r[i] = v - ys[i];
                    h_squares[i] = h[i].square();
                    a[i] = xs[i].double() + u;
                }
                C::mul_base_assign_pairs(&mut a, &h_squares, private::CrateToken(()));
                for i in 0..n {
                    a[i] -= r[i].square();
                }
                #[cfg(all(
                    feature = "aarch64-asm",
                    target_arch = "aarch64",
                    target_vendor = "apple"
                ))]
                batch_invert_nonzero::<C>(&mut a, &mut scratch);
                #[cfg(not(all(
                    feature = "aarch64-asm",
                    target_arch = "aarch64",
                    target_vendor = "apple"
                )))]
                batch_invert_nonzero(&mut a, &mut scratch);
                double_add_finish_batch::<C>(&ys, &mut h, &mut r, &mut h_squares, &mut a);
                for i in 0..n {
                    let u = live[i].xs[e][orbit];
                    xs[i] = u + h[i].double().double();
                    ys[i] = -ys[i] - a[i];
                }
            }
        }

        xs.into_iter()
            .zip(ys)
            .map(|(x, y)| C::affine_unchecked(x, y, private::CrateToken(())))
            .collect()
    }

    /// Multiplies one scalar by a contiguous batch of points, returning
    /// affine results without an intermediate projective conversion.
    fn mul_decomposed_same_scalar_affine(
        points: &[C],
        scalar: &Decomposed<C>,
    ) -> Vec<C::AffineExt> {
        if points.is_empty() {
            return Vec::new();
        }

        let tables = Self::batch(points);
        let use_affine = tables.len() >= BATCH_AFFINE_MIN_POINTS
            && tables.iter().all(|table| !table.is_identity())
            && scalar.len > 0
            && scalar.affine_ladder_safe;
        if !use_affine {
            let projective: Vec<_> = tables
                .iter()
                .map(|table| table.mul_decomposed(scalar))
                .collect();
            let mut affine = alloc::vec![C::AffineExt::identity(); projective.len()];
            C::batch_normalize(&projective, &mut affine);
            return affine;
        }

        let tables: Vec<_> = tables.iter().collect();
        Self::batch_affine_ladder(&tables, scalar)
    }

    /// One affine product for each `(point, scalar)` pair. This is the FFT
    /// counterpart to [`Table::mul_decomposed_batch`]: tables and ladder
    /// inversions are batched even though each point has a different scalar.
    fn mul_decomposed_pairs_affine(points: &[C], scalars: &[&Decomposed<C>]) -> Vec<C::AffineExt> {
        assert_eq!(points.len(), scalars.len());
        if points.is_empty() {
            return Vec::new();
        }

        let tables = Self::batch(points);
        let use_affine = tables.len() >= BATCH_AFFINE_MIN_POINTS
            && tables.iter().all(|table| !table.is_identity())
            && scalars
                .iter()
                .all(|scalar| scalar.len > 0 && scalar.affine_ladder_safe);
        if !use_affine {
            let projective: Vec<_> = tables
                .iter()
                .zip(scalars)
                .map(|(table, scalar)| table.mul_decomposed(scalar))
                .collect();
            let mut affine = alloc::vec![C::AffineExt::identity(); projective.len()];
            C::batch_normalize(&projective, &mut affine);
            return affine;
        }

        Self::batch_affine_ladder_pairs(&tables, scalars)
    }

    /// Synchronized affine Eisenstein ladders with one independently recoded
    /// scalar per table. Shorter recodings join when their top digit is
    /// reached; all live accumulators share each column's inversions.
    fn batch_affine_ladder_pairs(tables: &[Self], scalars: &[&Decomposed<C>]) -> Vec<C::AffineExt> {
        let n = tables.len();
        let max_len = scalars.iter().map(|scalar| scalar.len).max().unwrap_or(0);
        let mut xs = alloc::vec![C::Base::ZERO; n];
        let mut ys = alloc::vec![C::Base::ZERO; n];
        let mut started = alloc::vec![false; n];
        let mut denominators = Vec::with_capacity(n);
        let mut scratch = Vec::with_capacity(n);
        let mut doublings = Vec::with_capacity(n);
        let mut additions = Vec::with_capacity(n);
        let mut addition_ys = Vec::with_capacity(n);
        let mut h = Vec::with_capacity(n);
        let mut r = Vec::with_capacity(n);
        let mut h_squares = Vec::with_capacity(n);
        let mut a = Vec::with_capacity(n);

        for position in (0..max_len).rev() {
            denominators.clear();
            doublings.clear();
            additions.clear();
            for (i, (table, scalar)) in tables.iter().zip(scalars).enumerate() {
                if position >= scalar.len {
                    continue;
                }
                let code = scalar.digits[position];
                if !started[i] {
                    debug_assert_eq!(position + 1, scalar.len);
                    debug_assert_ne!(code, 0);
                    (xs[i], ys[i]) = table.digit_coords(code);
                    started[i] = true;
                } else {
                    if code == 0 {
                        doublings.push(i);
                    } else {
                        additions.push((i, code));
                    }
                }
            }

            denominators.extend(doublings.iter().map(|&i| ys[i].double()));
            let addition_offset = denominators.len();
            let addition_count = additions.len();
            addition_ys.resize(addition_count, C::Base::ZERO);
            h.resize(addition_count, C::Base::ZERO);
            r.resize(addition_count, C::Base::ZERO);
            h_squares.resize(addition_count, C::Base::ZERO);
            a.resize(addition_count, C::Base::ZERO);
            for (j, &(i, code)) in additions.iter().enumerate() {
                let (orbit, e, negate) = decode_digit(code);
                let u = tables[i].xs[e][orbit];
                let v = if negate {
                    -tables[i].ys[orbit]
                } else {
                    tables[i].ys[orbit]
                };
                addition_ys[j] = ys[i];
                h[j] = u - xs[i];
                r[j] = v - ys[i];
                h_squares[j] = h[j].square();
                a[j] = xs[i].double() + u;
            }
            if addition_count != 0 {
                C::mul_base_assign_pairs(&mut a, &h_squares, private::CrateToken(()));
                denominators.extend(
                    a.iter()
                        .zip(&r)
                        .map(|(product, difference)| *product - difference.square()),
                );
            }

            scratch.resize(denominators.len(), C::Base::ZERO);
            if !denominators.is_empty() {
                #[cfg(all(
                    feature = "aarch64-asm",
                    target_arch = "aarch64",
                    target_vendor = "apple"
                ))]
                batch_invert_nonzero::<C>(&mut denominators, &mut scratch);
                #[cfg(not(all(
                    feature = "aarch64-asm",
                    target_arch = "aarch64",
                    target_vendor = "apple"
                )))]
                batch_invert_nonzero(&mut denominators, &mut scratch);
            }

            for (&i, inverse) in doublings.iter().zip(&denominators) {
                let xx = xs[i].square();
                let slope = (xx.double() + xx) * inverse;
                let x2 = slope.square() - xs[i].double();
                ys[i] = slope * (xs[i] - x2) - ys[i];
                xs[i] = x2;
            }

            if addition_count != 0 {
                let addition_inverses = &mut denominators[addition_offset..];
                double_add_finish_batch::<C>(
                    &addition_ys,
                    &mut h,
                    &mut r,
                    &mut h_squares,
                    addition_inverses,
                );
                for (j, &(i, code)) in additions.iter().enumerate() {
                    let (orbit, e, _) = decode_digit(code);
                    let u = tables[i].xs[e][orbit];
                    xs[i] = u + h[j].double().double();
                    ys[i] = -addition_ys[j] - addition_inverses[j];
                }
            }
        }

        debug_assert!(started.iter().all(|started| *started));
        xs.into_iter()
            .zip(ys)
            .map(|(x, y)| C::affine_unchecked(x, y, private::CrateToken(())))
            .collect()
    }
}

/// Whether the column schedule of `k` avoids every exceptional case of the
/// batch-affine ladder, by tracking the scalar `s` that multiplies the base
/// point in the shared accumulator.
///
/// The top digit makes `s` nonzero (digit values are never zero: their
/// Eisenstein norms are nonzero integers of at most 75, far below the group
/// order), doubling `s` in an odd-order field preserves nonzeroness, and the
/// active-column check rules out `2s + d = 0`, so accumulators are never the
/// identity and doubling columns are always safe (no 2-torsion means
/// `2y != 0`). An active column computing `2P + D` with `P = [s]B`,
/// `D = [d]B` is exceptional iff `d = s` or `d = -2s`. These are exactly the
/// cases where the direct formula's denominator
/// `(x(D) - x(P))²(2x(P) + x(D)) - (y(D) - y(P))²` vanishes. In the latter
/// case, the column output is the identity. Unlike the previous two-step
/// formula, the direct formula handles `D = -P` without an intermediate
/// identity.
///
/// The conditions depend only on the scalar schedule, never on the points,
/// so one exact check covers the entire batch. For the `ivk`-shaped scalars
/// this path serves the conditions require a ladder prefix to collide with
/// a GLV lattice vector — probability ~2^-124 per random scalar — but
/// adversarial scalars can be constructed, hence the fallback.
fn affine_ladder_safe<C: GlvParams>(k: &Decomposed<C>) -> bool {
    debug_assert!(k.len > 0);
    let mut s = digit_scalar::<C::ScalarExt>(k.digits[k.len - 1]);
    for &code in k.digits[..k.len - 1].iter().rev() {
        if code == 0 {
            s = s.double();
        } else {
            let d = digit_scalar::<C::ScalarExt>(code);
            let s2 = s.double();
            if d == s || d == -s2 {
                return false;
            }
            s = s2 + d;
        }
    }
    true
}

/// A scalar in GLV-decomposed, jointly recoded form, ready for
/// [`Table::mul_decomposed`] and [`Table::mul_decomposed_batch`].
///
/// Building this once per scalar hoists the decomposition and digit
/// recoding out of a loop that multiplies the same scalar against many
/// tables (e.g. one viewing key against a batch of ephemeral keys).
#[derive(Clone, Debug)]
pub struct Decomposed<C: GlvParams> {
    /// Joint digit codes, lowest position first (see [`JOINT_DIGITS`]);
    /// zero at position `len` and beyond, nonzero at `len - 1` (when
    /// `len > 0`).
    digits: [u8; MAX_JOINT_DIGITS],
    /// Digit positions in use.
    len: usize,
    /// Whether every denominator in the affine ladder schedule is nonzero.
    affine_ladder_safe: bool,
    _curve: PhantomData<C>,
}

impl<C: GlvParams> Decomposed<C> {
    /// Decomposes `k` and recodes the halves as one joint width-3 NAF digit
    /// string over the Eisenstein integers.
    pub fn new(k: &C::ScalarExt) -> Self {
        let ((neg1, a1), (neg2, a2)) = decompose::<C>(k);
        // The i128 recoding coefficients and the digit-array bound rely on
        // the half-width guarantee; enforce it in every build profile.
        assert!(
            a1 >> GLV_COMPONENT_BITS == 0 && a2 >> GLV_COMPONENT_BITS == 0,
            "GLV half exceeds 127 bits"
        );
        let a = if neg1 { -(a1 as i128) } else { a1 as i128 };
        let b = if neg2 { -(a2 as i128) } else { a2 as i128 };
        let (digits, len) = joint_digits(a, b);
        let mut decomposed = Decomposed {
            digits,
            len,
            affine_ladder_safe: false,
            _curve: PhantomData,
        };
        decomposed.affine_ladder_safe = decomposed.len > 0 && affine_ladder_safe::<C>(&decomposed);
        decomposed
    }
}

/// Computes an unnormalized radix-2 FFT over public curve points.
///
/// This prototype keeps the layer state affine. It decomposes each distinct
/// twiddle once, batches the Eisenstein tables and affine ladders for all
/// nontrivial scalar multiplications in a layer, and batch-inverts the shared
/// denominator for each layer's affine butterflies.
pub(crate) fn fft_vartime<C: GlvParams>(
    input: &[C],
    output: &mut [C::AffineExt],
    omega: C::ScalarExt,
    log_n: u32,
) {
    fn bitreverse(mut value: usize, bits: usize) -> usize {
        let mut reversed = 0;
        for _ in 0..bits {
            reversed = (reversed << 1) | (value & 1);
            value >>= 1;
        }
        reversed
    }

    assert_eq!(input.len(), output.len());
    assert_eq!(input.len(), 1usize << log_n);
    C::batch_normalize(input, output);
    // If one layer starts without identities and every `x_R - x_L` is
    // nonzero, both `L + R` and `L - R` are nonidentity. Carry that invariant
    // across layers instead of checking both inputs to every butterfly.
    let mut identity_free = output.iter().all(|point| !bool::from(point.is_identity()));

    for i in 0..output.len() {
        let reversed = bitreverse(i, log_n as usize);
        if i < reversed {
            output.swap(i, reversed);
        }
    }

    let mut twiddle = C::ScalarExt::ONE;
    let twiddles: Vec<_> = (0..output.len() / 2)
        .map(|_| {
            let decomposed = Decomposed::<C>::new(&twiddle);
            twiddle *= omega;
            decomposed
        })
        .collect();

    let mut butterfly_scratch = AffineTwiddleScratch::new();
    let (mut chunk, mut twiddle_stride) = if output.len() >= 16 {
        identity_free = fft16_low_multiplication_layer::<C>(output, omega, identity_free);
        (32, output.len() / 32)
    } else if output.len() >= 8 {
        identity_free = fft8_multiplication_minimal_layer::<C>(output, omega, identity_free);
        (16, output.len() / 16)
    } else {
        (2, output.len() / 2)
    };
    while chunk <= output.len() {
        let half = chunk / 2;
        #[cfg(feature = "multicore")]
        let use_twiddle_major = maybe_rayon::current_num_threads() > 1
            && (TWIDDLE_MAJOR_MIN_CHUNK..=TWIDDLE_MAJOR_MAX_CHUNK).contains(&chunk);
        #[cfg(not(feature = "multicore"))]
        let use_twiddle_major = false;
        // Transpose the point-major pairs into one contiguous batch per
        // twiddle. This shares the scalar schedule and exposes each twiddle
        // batch as an independent Rayon task. With one worker, the repeated
        // table normalizations cost more than the transpose saves.
        if use_twiddle_major {
            #[cfg(feature = "multicore")]
            let products: Vec<Vec<_>> = (1..half)
                .into_par_iter()
                .map(|j| {
                    let points: Vec<_> = output
                        .chunks(chunk)
                        .map(|block| C::from(block[half + j]))
                        .collect();
                    Table::<C>::mul_decomposed_same_scalar_affine(
                        &points,
                        &twiddles[j * twiddle_stride],
                    )
                })
                .collect();
            #[cfg(not(feature = "multicore"))]
            let products: Vec<Vec<_>> = (1..half)
                .map(|j| {
                    let points: Vec<_> = output
                        .chunks(chunk)
                        .map(|block| C::from(block[half + j]))
                        .collect();
                    Table::<C>::mul_decomposed_same_scalar_affine(
                        &points,
                        &twiddles[j * twiddle_stride],
                    )
                })
                .collect();

            let blocks = output.len() / chunk;
            let mut right_scaled = Vec::with_capacity(output.len() / 2);
            for (block_index, block) in output.chunks(chunk).enumerate() {
                right_scaled.push(block[half]);
                right_scaled.extend(products.iter().map(|products| products[block_index]));
            }
            debug_assert_eq!(blocks, products.first().map_or(0, Vec::len));
            identity_free = affine_twiddle_add_sub_layer::<C>(
                output,
                &right_scaled,
                chunk,
                &mut butterfly_scratch,
                identity_free,
            );
            chunk *= 2;
            twiddle_stride /= 2;
            continue;
        }

        let nontrivial = output.len() / 2 - output.len() / chunk;
        let mut points = Vec::with_capacity(nontrivial);
        let mut scalars = Vec::with_capacity(nontrivial);
        for block in output.chunks(chunk) {
            for j in 1..half {
                points.push(C::from(block[half + j]));
                scalars.push(&twiddles[j * twiddle_stride]);
            }
        }

        #[cfg(feature = "multicore")]
        let products = {
            let threads = maybe_rayon::current_num_threads();
            let batch_len = points.len().div_ceil(threads).max(BATCH_AFFINE_MIN_POINTS);
            let batches: Vec<Vec<_>> = points
                .par_chunks(batch_len)
                .zip(scalars.par_chunks(batch_len))
                .map(|(points, scalars)| Table::<C>::mul_decomposed_pairs_affine(points, scalars))
                .collect();
            batches.into_iter().flatten().collect::<Vec<_>>()
        };
        #[cfg(not(feature = "multicore"))]
        let products = Table::<C>::mul_decomposed_pairs_affine(&points, &scalars);
        let mut products = products.into_iter();
        let mut right_scaled = Vec::with_capacity(output.len() / 2);
        for block in output.chunks(chunk) {
            right_scaled.push(block[half]);
            right_scaled.extend((1..half).map(|_| {
                products
                    .next()
                    .expect("one product per nontrivial butterfly")
            }));
        }
        assert!(products.next().is_none());

        identity_free = affine_twiddle_add_sub_layer::<C>(
            output,
            &right_scaled,
            chunk,
            &mut butterfly_scratch,
            identity_free,
        );
        chunk *= 2;
        twiddle_stride /= 2;
    }
}

/// Replaces four radix-2 layers with a 16-point codelet that uses 14 scalar
/// multiplications instead of 15. Its DFT8 and two odd-root DFT4
/// subtransforms share their affine stages and repeated eighth-root scalar
/// schedules.
fn fft16_low_multiplication_layer<C: GlvParams>(
    points: &mut [C::AffineExt],
    omega: C::ScalarExt,
    mut identity_free: bool,
) -> bool {
    debug_assert_eq!(points.len() % 16, 0);
    let blocks = points.len() / 16;
    let weighted_blocks = blocks * 2;
    let mut scratch = AffineTwiddleScratch::new();
    let mut left = Vec::with_capacity(points.len() / 2);
    let mut right = Vec::with_capacity(points.len() / 2);

    // The global bit reversal puts (q_j, q_{j + 8}) next to each other.
    for block in points.chunks(16) {
        for pair in block.chunks(2) {
            left.push(pair[0]);
            right.push(pair[1]);
        }
    }
    let mut even_inputs = alloc::vec![C::AffineExt::identity(); points.len() / 2];
    let mut odd_inputs = alloc::vec![C::AffineExt::identity(); points.len() / 2];
    identity_free = affine_add_sub_pairs::<C>(
        &left,
        &right,
        &mut even_inputs,
        &mut odd_inputs,
        &mut scratch,
        identity_free,
    );

    let root16 = omega.pow_vartime([(points.len() / 16) as u64]);
    let root8 = root16.square();
    let root8_squared = root8.square();
    let root8_cubed = root8_squared * root8;
    let c = (root8 + root8_cubed) * C::ScalarExt::TWO_INV;
    let d = (root8 - root8_cubed) * C::ScalarExt::TWO_INV;
    let shared_scalars = [
        Decomposed::<C>::new(&root8_squared),
        Decomposed::<C>::new(&c),
        Decomposed::<C>::new(&d),
    ];

    // Start the DFT8 on the sums and both odd-root DFT4s on the
    // differences in one inversion batch.
    left.clear();
    right.clear();
    left.reserve(blocks * 6);
    right.reserve(blocks * 6);
    for block in even_inputs.chunks(8) {
        for pair in block.chunks(2) {
            left.push(pair[0]);
            right.push(pair[1]);
        }
    }
    for block in odd_inputs.chunks(4) {
        left.push(block[2]);
        right.push(block[3]);
    }
    let mut stage1_sum = alloc::vec![C::AffineExt::identity(); blocks * 6];
    let mut stage1_difference = alloc::vec![C::AffineExt::identity(); blocks * 6];
    identity_free = affine_add_sub_pairs::<C>(
        &left,
        &right,
        &mut stage1_sum,
        &mut stage1_difference,
        &mut scratch,
        identity_free,
    );

    // Finish the additions needed before the DFT8 scalar multiplications.
    left.clear();
    right.clear();
    left.reserve(blocks * 3);
    right.reserve(blocks * 3);
    for block in 0..blocks {
        let offset = block * 4;
        left.extend_from_slice(&[
            stage1_sum[offset],
            stage1_sum[offset + 2],
            stage1_difference[offset + 2],
        ]);
        right.extend_from_slice(&[
            stage1_sum[offset + 1],
            stage1_sum[offset + 3],
            stage1_difference[offset + 3],
        ]);
    }
    let mut stage2_sum = alloc::vec![C::AffineExt::identity(); blocks * 3];
    let mut stage2_difference = alloc::vec![C::AffineExt::identity(); blocks * 3];
    identity_free = affine_add_sub_pairs::<C>(
        &left,
        &right,
        &mut stage2_sum,
        &mut stage2_difference,
        &mut scratch,
        identity_free,
    );

    // Both transforms use the same i, c, and d constants. Build one affine
    // ladder batch per constant.
    let odd_stage1_offset = blocks * 4;
    let mut scalar_inputs = [
        Vec::with_capacity(blocks * 4),
        Vec::with_capacity(blocks * 3),
        Vec::with_capacity(blocks * 3),
    ];
    for block in 0..blocks {
        let stage1 = block * 4;
        let stage2 = block * 3;
        scalar_inputs[0].extend_from_slice(&[
            C::from(stage2_difference[stage2 + 1]),
            C::from(stage1_difference[stage1 + 1]),
        ]);
        scalar_inputs[1].push(C::from(stage2_sum[stage2 + 2]));
        scalar_inputs[2].push(C::from(stage2_difference[stage2 + 2]));
    }
    for block in 0..weighted_blocks {
        scalar_inputs[0].push(C::from(odd_inputs[block * 4 + 1]));
        scalar_inputs[1].push(C::from(stage1_sum[odd_stage1_offset + block]));
        scalar_inputs[2].push(C::from(stage1_difference[odd_stage1_offset + block]));
    }
    let products = mul_same_scalars_affine::<C>(scalar_inputs.into(), &shared_scalars);

    // Complete the next DFT8 stage and the middle odd-root DFT4 stage in
    // one denominator batch.
    left.clear();
    right.clear();
    left.reserve(blocks * 8);
    right.reserve(blocks * 8);
    for block in 0..blocks {
        let stage1 = block * 4;
        let stage2 = block * 3;
        let root8_squared_offset = block * 2;
        left.extend_from_slice(&[
            stage2_sum[stage2],
            stage2_difference[stage2],
            stage1_difference[stage1],
            products[1][block],
        ]);
        right.extend_from_slice(&[
            stage2_sum[stage2 + 1],
            products[0][root8_squared_offset],
            products[0][root8_squared_offset + 1],
            products[2][block],
        ]);
    }
    for block in 0..weighted_blocks {
        let scalar_offset = blocks + block;
        left.extend_from_slice(&[odd_inputs[block * 4], products[1][scalar_offset]]);
        right.extend_from_slice(&[products[0][blocks * 2 + block], products[2][scalar_offset]]);
    }
    let mut stage3_sum = alloc::vec![C::AffineExt::identity(); blocks * 8];
    let mut stage3_difference = alloc::vec![C::AffineExt::identity(); blocks * 8];
    identity_free = affine_add_sub_pairs::<C>(
        &left,
        &right,
        &mut stage3_sum,
        &mut stage3_difference,
        &mut scratch,
        identity_free,
    );

    // Finish the DFT8 and both odd-root DFT4s together.
    left.clear();
    right.clear();
    left.reserve(blocks * 6);
    right.reserve(blocks * 6);
    for block in 0..blocks {
        let offset = block * 4;
        left.extend_from_slice(&[stage3_sum[offset + 2], stage3_difference[offset + 2]]);
        right.extend_from_slice(&[stage3_sum[offset + 3], stage3_difference[offset + 3]]);
    }
    let odd_stage3_offset = blocks * 4;
    for block in 0..weighted_blocks {
        let offset = odd_stage3_offset + block * 2;
        left.extend_from_slice(&[stage3_sum[offset], stage3_difference[offset]]);
        right.extend_from_slice(&[stage3_sum[offset + 1], stage3_difference[offset + 1]]);
    }
    let mut stage4_sum = alloc::vec![C::AffineExt::identity(); blocks * 6];
    let mut stage4_difference = alloc::vec![C::AffineExt::identity(); blocks * 6];
    identity_free = affine_add_sub_pairs::<C>(
        &left,
        &right,
        &mut stage4_sum,
        &mut stage4_difference,
        &mut scratch,
        identity_free,
    );

    let mut even_outputs = alloc::vec![C::AffineExt::identity(); blocks * 8];
    for block in 0..blocks {
        let stage3 = block * 4;
        let stage4 = block * 2;
        let output = &mut even_outputs[block * 8..][..8];
        output[0] = stage3_sum[stage3];
        output[4] = stage3_difference[stage3];
        output[2] = stage3_sum[stage3 + 1];
        output[6] = stage3_difference[stage3 + 1];
        output[1] = stage4_sum[stage4];
        output[5] = stage4_difference[stage4];
        output[3] = stage4_sum[stage4 + 1];
        output[7] = stage4_difference[stage4 + 1];
    }

    let odd_stage4_offset = blocks * 2;
    let mut odd_roots = alloc::vec![C::AffineExt::identity(); blocks * 8];
    for block in 0..weighted_blocks {
        let stage4 = odd_stage4_offset + block * 2;
        let output = &mut odd_roots[block * 4..][..4];
        output[0] = stage4_sum[stage4];
        output[1] = stage4_sum[stage4 + 1];
        output[2] = stage4_difference[stage4];
        output[3] = stage4_difference[stage4 + 1];
    }

    let root16_squared = root16.square();
    let mut odd_root = root16;
    let odd_scalars: Vec<_> = (0..4)
        .map(|_| {
            let decomposed = Decomposed::<C>::new(&odd_root);
            odd_root *= root16_squared;
            decomposed
        })
        .collect();
    let mut scalar_inputs: Vec<Vec<C>> = (0..4).map(|_| Vec::with_capacity(blocks)).collect();
    for block in odd_roots.chunks(8) {
        for (input, point) in scalar_inputs.iter_mut().zip(&block[4..]) {
            input.push(C::from(*point));
        }
    }
    let products = mul_same_scalars_affine::<C>(scalar_inputs, &odd_scalars);

    left.clear();
    right.clear();
    left.reserve(blocks * 4);
    right.reserve(blocks * 4);
    for (block_index, block) in odd_roots.chunks(8).enumerate() {
        left.extend_from_slice(&block[..4]);
        right.extend(products.iter().map(|products| products[block_index]));
    }
    let mut odd_low = alloc::vec![C::AffineExt::identity(); blocks * 4];
    let mut odd_high = alloc::vec![C::AffineExt::identity(); blocks * 4];
    identity_free = affine_add_sub_pairs::<C>(
        &left,
        &right,
        &mut odd_low,
        &mut odd_high,
        &mut scratch,
        identity_free,
    );

    for (block_index, output) in points.chunks_mut(16).enumerate() {
        let even = &even_outputs[block_index * 8..][..8];
        let odd_low = &odd_low[block_index * 4..][..4];
        let odd_high = &odd_high[block_index * 4..][..4];
        for i in 0..4 {
            output[i * 2] = even[i];
            output[i * 2 + 1] = odd_low[i];
            output[i * 2 + 8] = even[i + 4];
            output[i * 2 + 9] = odd_high[i];
        }
    }
    identity_free
}

/// Replaces the bottom three radix-2 layers with an eight-point codelet.
/// Each block uses four constant scalar multiplications instead of five,
/// at the cost of two additional group additions.
fn fft8_multiplication_minimal_layer<C: GlvParams>(
    points: &mut [C::AffineExt],
    omega: C::ScalarExt,
    mut identity_free: bool,
) -> bool {
    debug_assert_eq!(points.len() % 8, 0);
    let root8 = omega.pow_vartime([(points.len() / 8) as u64]);
    let root8_squared = root8.square();
    let root8_cubed = root8_squared * root8;
    let c = (root8 + root8_cubed) * C::ScalarExt::TWO_INV;
    let d = (root8 - root8_cubed) * C::ScalarExt::TWO_INV;
    let scalars = [
        Decomposed::<C>::new(&root8_squared),
        Decomposed::<C>::new(&c),
        Decomposed::<C>::new(&d),
    ];

    let blocks = points.len() / 8;
    let mut scratch = AffineTwiddleScratch::new();
    let mut left = Vec::with_capacity(blocks * 4);
    let mut right = Vec::with_capacity(blocks * 4);
    for block in points.chunks(8) {
        // The enclosing FFT has already bit-reversed the input. Undo the
        // local three-bit reversal by pairing adjacent entries as
        // (q0, q4), (q2, q6), (q1, q5), and (q3, q7).
        for pair in block.chunks(2) {
            left.push(pair[0]);
            right.push(pair[1]);
        }
    }
    let mut stage1_sum = alloc::vec![C::AffineExt::identity(); blocks * 4];
    let mut stage1_difference = alloc::vec![C::AffineExt::identity(); blocks * 4];
    identity_free = affine_add_sub_pairs::<C>(
        &left,
        &right,
        &mut stage1_sum,
        &mut stage1_difference,
        &mut scratch,
        identity_free,
    );

    left.clear();
    right.clear();
    left.reserve(blocks * 3);
    right.reserve(blocks * 3);
    for block in 0..blocks {
        let offset = block * 4;
        left.extend_from_slice(&[
            stage1_sum[offset],
            stage1_sum[offset + 2],
            stage1_difference[offset + 2],
        ]);
        right.extend_from_slice(&[
            stage1_sum[offset + 1],
            stage1_sum[offset + 3],
            stage1_difference[offset + 3],
        ]);
    }
    let mut stage2_sum = alloc::vec![C::AffineExt::identity(); blocks * 3];
    let mut stage2_difference = alloc::vec![C::AffineExt::identity(); blocks * 3];
    identity_free = affine_add_sub_pairs::<C>(
        &left,
        &right,
        &mut stage2_sum,
        &mut stage2_difference,
        &mut scratch,
        identity_free,
    );

    let mut scalar_inputs: [Vec<C>; 3] = [
        Vec::with_capacity(blocks * 2),
        Vec::with_capacity(blocks),
        Vec::with_capacity(blocks),
    ];
    for block in 0..blocks {
        let stage1 = block * 4;
        let stage2 = block * 3;
        scalar_inputs[0].extend_from_slice(&[
            C::from(stage2_difference[stage2 + 1]),
            C::from(stage1_difference[stage1 + 1]),
        ]);
        scalar_inputs[1].push(C::from(stage2_sum[stage2 + 2]));
        scalar_inputs[2].push(C::from(stage2_difference[stage2 + 2]));
    }

    let products = mul_same_scalars_affine::<C>(scalar_inputs.into(), &scalars);

    left.clear();
    right.clear();
    left.reserve(blocks * 4);
    right.reserve(blocks * 4);
    for block in 0..blocks {
        let stage1 = block * 4;
        let stage2 = block * 3;
        let root8_squared_offset = block * 2;
        left.extend_from_slice(&[
            stage2_sum[stage2],
            stage2_difference[stage2],
            stage1_difference[stage1],
            products[1][block],
        ]);
        right.extend_from_slice(&[
            stage2_sum[stage2 + 1],
            products[0][root8_squared_offset],
            products[0][root8_squared_offset + 1],
            products[2][block],
        ]);
    }
    let mut stage3_sum = alloc::vec![C::AffineExt::identity(); blocks * 4];
    let mut stage3_difference = alloc::vec![C::AffineExt::identity(); blocks * 4];
    identity_free = affine_add_sub_pairs::<C>(
        &left,
        &right,
        &mut stage3_sum,
        &mut stage3_difference,
        &mut scratch,
        identity_free,
    );

    left.clear();
    right.clear();
    left.reserve(blocks * 2);
    right.reserve(blocks * 2);
    for block in 0..blocks {
        let offset = block * 4;
        left.extend_from_slice(&[stage3_sum[offset + 2], stage3_difference[offset + 2]]);
        right.extend_from_slice(&[stage3_sum[offset + 3], stage3_difference[offset + 3]]);
    }
    let mut stage4_sum = alloc::vec![C::AffineExt::identity(); blocks * 2];
    let mut stage4_difference = alloc::vec![C::AffineExt::identity(); blocks * 2];
    identity_free = affine_add_sub_pairs::<C>(
        &left,
        &right,
        &mut stage4_sum,
        &mut stage4_difference,
        &mut scratch,
        identity_free,
    );

    for (block, output) in points.chunks_mut(8).enumerate() {
        let stage3 = block * 4;
        let stage4 = block * 2;
        output[0] = stage3_sum[stage3];
        output[4] = stage3_difference[stage3];
        output[2] = stage3_sum[stage3 + 1];
        output[6] = stage3_difference[stage3 + 1];
        output[1] = stage4_sum[stage4];
        output[5] = stage4_difference[stage4];
        output[3] = stage4_sum[stage4 + 1];
        output[7] = stage4_difference[stage4 + 1];
    }
    identity_free
}

fn mul_same_scalars_affine<C: GlvParams>(
    scalar_inputs: Vec<Vec<C>>,
    scalars: &[Decomposed<C>],
) -> Vec<Vec<C::AffineExt>> {
    assert_eq!(scalar_inputs.len(), scalars.len());
    #[cfg(feature = "multicore")]
    {
        scalar_inputs
            .into_par_iter()
            .zip(scalars.par_iter())
            .map(|(points, scalar)| {
                let threads = maybe_rayon::current_num_threads();
                let batch_len = points.len().div_ceil(threads).max(BATCH_AFFINE_MIN_POINTS);
                let batches: Vec<Vec<_>> = points
                    .par_chunks(batch_len)
                    .map(|points| Table::<C>::mul_decomposed_same_scalar_affine(points, scalar))
                    .collect();
                batches.into_iter().flatten().collect()
            })
            .collect()
    }
    #[cfg(not(feature = "multicore"))]
    {
        scalar_inputs
            .into_iter()
            .zip(scalars)
            .map(|(points, scalar)| Table::<C>::mul_decomposed_same_scalar_affine(&points, scalar))
            .collect()
    }
}

/// Computes arbitrary affine `L + R` and `L - R` pairs with one shared
/// inversion. This is the non-layer-shaped counterpart to
/// [`affine_twiddle_add_sub_layer`].
fn affine_add_sub_pairs<C: GlvParams>(
    left: &[C::AffineExt],
    right: &[C::AffineExt],
    sums: &mut [C::AffineExt],
    differences: &mut [C::AffineExt],
    scratch: &mut AffineTwiddleScratch<C::Base>,
    identity_free: bool,
) -> bool {
    assert_eq!(left.len(), right.len());
    assert_eq!(left.len(), sums.len());
    assert_eq!(left.len(), differences.len());

    if !identity_free
        && left
            .iter()
            .zip(right)
            .any(|(left, right)| bool::from(left.is_identity()) || bool::from(right.is_identity()))
    {
        projective_add_sub_pairs::<C>(left, right, sums, differences);
        return false;
    }

    scratch.denominators.resize(left.len(), C::Base::ZERO);
    scratch.prefixes.resize(left.len(), C::Base::ZERO);
    let mut acc = C::Base::ONE;
    for (((left, right), denominator), prefix) in left
        .iter()
        .zip(right)
        .zip(scratch.denominators.iter_mut())
        .zip(scratch.prefixes.iter_mut())
    {
        let (left_x, _) = C::affine_xy(left);
        let (right_x, _) = C::affine_xy(right);
        *denominator = right_x - left_x;
        *prefix = acc;
        acc *= *denominator;
    }

    let inverse = acc.invert();
    if !bool::from(inverse.is_some()) {
        projective_add_sub_pairs::<C>(left, right, sums, differences);
        return false;
    }
    acc = inverse.unwrap();
    sums.copy_from_slice(left);
    for i in (0..left.len()).rev() {
        let denominator_inverse = acc * scratch.prefixes[i];
        acc *= scratch.denominators[i];
        apply_affine_twiddle::<C>(
            &mut sums[i],
            &mut differences[i],
            &right[i],
            denominator_inverse,
        );
    }
    // A codelet can retain intermediates that are not part of this batch and
    // feed them into a later batch. A successful batch therefore cannot
    // strengthen the invariant for the entire codelet after an earlier
    // exceptional fallback made it false.
    identity_free
}

fn projective_add_sub_pairs<C: GlvParams>(
    left: &[C::AffineExt],
    right: &[C::AffineExt],
    sums: &mut [C::AffineExt],
    differences: &mut [C::AffineExt],
) {
    let mut projective = Vec::with_capacity(left.len() * 2);
    for (left, right) in left.iter().zip(right) {
        let left = C::from(*left);
        let right = C::from(*right);
        projective.extend_from_slice(&[left + right, left - right]);
    }
    let mut affine = alloc::vec![C::AffineExt::identity(); projective.len()];
    C::batch_normalize(&projective, &mut affine);
    for (i, pair) in affine.chunks(2).enumerate() {
        sums[i] = pair[0];
        differences[i] = pair[1];
    }
}

#[inline(always)]
fn apply_affine_twiddle<C: GlvParams>(
    left: &mut C::AffineExt,
    output: &mut C::AffineExt,
    right: &C::AffineExt,
    inverse: C::Base,
) {
    let (left_x, left_y) = C::affine_xy(left);
    let (right_x, right_y) = C::affine_xy(right);

    let plus_slope = (right_y - left_y) * inverse;
    let minus_slope = (-right_y - left_y) * inverse;
    let plus_x = plus_slope.square() - left_x - right_x;
    let minus_x = minus_slope.square() - left_x - right_x;
    let plus_y = plus_slope * (left_x - plus_x) - left_y;
    let minus_y = minus_slope * (left_x - minus_x) - left_y;

    *left = C::affine_unchecked(plus_x, plus_y, private::CrateToken(()));
    *output = C::affine_unchecked(minus_x, minus_y, private::CrateToken(()));
}

struct AffineTwiddleScratch<F> {
    denominators: Vec<F>,
    prefixes: Vec<F>,
}

impl<F> AffineTwiddleScratch<F> {
    fn new() -> Self {
        Self {
            denominators: Vec::new(),
            prefixes: Vec::new(),
        }
    }
}

/// Computes every `L + R` and `L - R` pair in one FFT layer. Both affine
/// chords share `x_R - x_L`, so each inverse is consumed directly during
/// batch-inversion back-substitution.
fn affine_twiddle_add_sub_layer<C: GlvParams>(
    points: &mut [C::AffineExt],
    right_scaled: &[C::AffineExt],
    chunk: usize,
    scratch: &mut AffineTwiddleScratch<C::Base>,
    identity_free: bool,
) -> bool {
    let half = chunk / 2;
    assert_eq!(right_scaled.len(), points.len() / 2);

    if !identity_free
        && points
            .chunks(chunk)
            .zip(right_scaled.chunks(half))
            .any(|(block, scaled)| {
                block[..half].iter().zip(scaled).any(|(left, right)| {
                    bool::from(left.is_identity()) || bool::from(right.is_identity())
                })
            })
    {
        projective_twiddle_add_sub_layer::<C>(points, right_scaled, chunk);
        return false;
    }

    scratch
        .denominators
        .resize(right_scaled.len(), C::Base::ZERO);
    scratch.prefixes.resize(right_scaled.len(), C::Base::ZERO);
    let mut acc = C::Base::ONE;
    let mut slots = scratch
        .denominators
        .iter_mut()
        .zip(scratch.prefixes.iter_mut());
    for (block, scaled) in points.chunks(chunk).zip(right_scaled.chunks(half)) {
        for (left, right) in block[..half].iter().zip(scaled) {
            let (left_x, _) = C::affine_xy(left);
            let (right_x, _) = C::affine_xy(right);
            let denominator = right_x - left_x;
            let (denominator_slot, prefix_slot) =
                slots.next().expect("one scratch slot per butterfly");
            *denominator_slot = denominator;
            *prefix_slot = acc;
            acc *= denominator;
        }
    }
    assert!(slots.next().is_none());

    // One failed inversion detects every `x_L == x_R` exceptional case.
    let inverse = acc.invert();
    if !bool::from(inverse.is_some()) {
        projective_twiddle_add_sub_layer::<C>(points, right_scaled, chunk);
        return false;
    }
    acc = inverse.unwrap();
    let mut inversion_scratch = scratch
        .denominators
        .iter()
        .zip(scratch.prefixes.iter())
        .rev();
    for (block, scaled) in points
        .chunks_mut(chunk)
        .zip(right_scaled.chunks(half))
        .rev()
    {
        let (left, output) = block.split_at_mut(half);
        for ((left, output), right) in left.iter_mut().zip(output).zip(scaled).rev() {
            let (denominator, prefix) = inversion_scratch
                .next()
                .expect("one scratch slot per butterfly");
            let denominator_inverse = acc * prefix;
            acc *= denominator;
            apply_affine_twiddle::<C>(left, output, right, denominator_inverse);
        }
    }
    assert!(inversion_scratch.next().is_none());
    true
}

fn projective_twiddle_add_sub_layer<C: GlvParams>(
    points: &mut [C::AffineExt],
    right_scaled: &[C::AffineExt],
    chunk: usize,
) {
    let half = chunk / 2;
    let mut projective = alloc::vec![C::identity(); points.len()];
    for ((block, output), scaled) in points
        .chunks(chunk)
        .zip(projective.chunks_mut(chunk))
        .zip(right_scaled.chunks(half))
    {
        for j in 0..half {
            let left = C::from(block[j]);
            let right = C::from(scaled[j]);
            output[j] = left + right;
            output[half + j] = left - right;
        }
    }
    C::batch_normalize(&projective, points);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::adc;
    use ff::Field;

    #[test]
    fn multiexp_backend_selection() {
        assert_eq!(default_multiexp_window_bits(31), Some(3));
        assert_eq!(default_multiexp_window_bits(32), Some(4));
        assert_eq!(default_multiexp_window_bits(54), Some(4));
        assert_eq!(default_multiexp_window_bits(55), Some(5));
        assert_eq!(default_multiexp_window_bits(2_980), Some(8));
        assert_eq!(default_multiexp_window_bits(2_981), Some(9));
        assert_eq!(default_multiexp_window_bits(8_103), Some(9));
        assert_eq!(default_multiexp_window_bits(8_104), Some(10));
        assert_eq!(default_multiexp_window_bits(u32::MAX as usize), Some(23));

        assert_eq!(estimated_signed_booth_work(2_150, 256, 8), Some(79_654));
        assert_eq!(
            estimated_signed_booth_work(4_300, GLV_COMPONENT_BITS, 8),
            Some(73_016)
        );
        assert_eq!(estimated_signed_booth_work(5_678, 256, 9), Some(179_762));
        assert_eq!(
            estimated_signed_booth_work(11_356, GLV_COMPONENT_BITS, 9),
            Some(178_146)
        );

        assert_eq!(multiexp_window_bits::<pallas::Point>(2_150, 1), Some(8));
        assert_eq!(multiexp_window_bits::<pallas::Point>(2_990, 1), Some(9));
        assert_eq!(multiexp_window_bits::<pallas::Point>(3_924, 1), Some(9));
        assert_eq!(multiexp_window_bits::<pallas::Point>(3_925, 1), Some(10));
        assert_eq!(multiexp_window_bits::<pallas::Point>(5_678, 1), Some(10));
        assert_eq!(multiexp_window_bits::<pallas::Point>(5_678, 8), Some(9));

        assert!(!should_use_glv_multiexp::<pallas::Point>(255, 8));
        assert!(should_use_glv_multiexp::<pallas::Point>(2_150, 8));
        assert!(should_use_glv_multiexp::<vesta::Point>(5_678, 10));

        // At sufficiently large sizes, doubling the term count outweighs the
        // shorter components for this unchanged window width.
        assert!(!should_use_glv_multiexp::<pallas::Point>(1_000_000, 14));
        assert!(!should_use_glv_multiexp::<pallas::Point>(usize::MAX, 14));
    }

    #[test]
    fn multiexp_component_guard_returns_none_out_of_bounds() {
        let in_bounds = GLV_COMPONENT_BITS - 1;
        let out_of_bounds = 1u128 << GLV_COMPONENT_BITS;

        assert!(checked_signed_magnitudes(((false, 0), (true, 1))).is_some());
        assert!(checked_signed_magnitudes(((false, 1u128 << in_bounds), (false, 0))).is_some());
        assert!(checked_signed_magnitudes(((false, out_of_bounds), (false, 0))).is_none());
        assert!(checked_signed_magnitudes(((false, 0), (true, out_of_bounds))).is_none());
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

    #[test]
    fn joint_digit_table_matches_first_principles() {
        // Eisenstein multiplication on coefficient pairs:
        // (a + bω)(c + dω) = (ac - bd) + (ad + bc - bd)ω.
        fn emul(x: (i32, i32), y: (i32, i32)) -> (i32, i32) {
            (x.0 * y.0 - x.1 * y.1, x.0 * y.1 + x.1 * y.0 - x.1 * y.1)
        }
        // The units in code order [+1, -1, +ω, -ω, +ω², -ω²]
        // (ω² = -1 - ω).
        let units = [(1, 0), (-1, 0), (0, 1), (0, -1), (-1, -1), (1, 1)];
        let mut rebuilt = [(0i8, 0i8, 0u8); 64];
        let mut seen = [false; 64];
        for (orbit, &(da, db)) in DELTA.iter().enumerate() {
            for (unit, &u) in units.iter().enumerate() {
                let d = emul(u, (i32::from(da), i32::from(db)));
                assert!(d.0.abs() <= 5 && d.1.abs() <= 5, "digit coefficient > 5");
                assert!(
                    d.0.rem_euclid(2) == 1 || d.1.rem_euclid(2) == 1,
                    "digit divisible by 2"
                );
                let idx = ((d.0.rem_euclid(8) << 3) | d.1.rem_euclid(8)) as usize;
                assert!(!seen[idx], "digit classes must be distinct");
                seen[idx] = true;
                let code = (1 + 6 * orbit + unit) as u8;
                rebuilt[idx] = (d.0 as i8, d.1 as i8, code);
                // Decode and coefficient reconstruction round-trip.
                assert_eq!(decode_digit(code), (orbit, unit >> 1, unit & 1 == 1));
                assert_eq!(digit_coeffs(code), (d.0 as i8, d.1 as i8));
            }
        }
        // U·Δ covers exactly the 48 residue classes not divisible by 2.
        assert_eq!(seen.iter().filter(|&&s| s).count(), 48);
        for (idx, &entry) in JOINT_DIGITS.iter().enumerate() {
            if seen[idx] {
                assert_eq!(entry, rebuilt[idx], "table entry {idx}");
            } else {
                assert_eq!(entry, (0, 0, 0), "class {idx} must be a zero digit");
                assert!(
                    (idx >> 3) & 1 == 0 && idx & 1 == 0,
                    "only even classes may hold zero digits"
                );
            }
        }
    }

    #[test]
    fn tail_bound_exhaustive() {
        // The recoding coefficients reach max(|a|, |b|) <= 5 within 127
        // steps (each step maps r to at most (r + 5)/2 <= r for r >= 5, and
        // below 2^(127-j) + 5 after j steps); this exhaustively bounds the
        // remaining tail over the closed box |a|, |b| <= 6, proving both
        // MAX_JOINT_DIGITS and termination.
        use alloc::collections::BTreeMap;
        fn tail(a: i128, b: i128, memo: &mut BTreeMap<(i128, i128), Option<usize>>) -> usize {
            if a == 0 && b == 0 {
                return 0;
            }
            match memo.get(&(a, b)) {
                Some(Some(t)) => return *t,
                Some(None) => panic!("recoding cycle at ({a}, {b})"),
                None => {}
            }
            memo.insert((a, b), None);
            let (da, db, _) = JOINT_DIGITS[(((a & 7) << 3) | (b & 7)) as usize];
            let t = 1 + tail(
                (a >> 1) - (i128::from(da) >> 1),
                (b >> 1) - (i128::from(db) >> 1),
                memo,
            );
            memo.insert((a, b), Some(t));
            t
        }
        let mut memo = BTreeMap::new();
        let mut max_tail = 0;
        for a in -6..=6 {
            for b in -6..=6 {
                max_tail = max_tail.max(tail(a, b, &mut memo));
            }
        }
        assert_eq!(max_tail, MAX_JOINT_DIGITS - GLV_COMPONENT_BITS);
        // The box is closed under recoding: every reached state stays in it.
        for &(a, b) in memo.keys() {
            assert!(a.abs() <= 6 && b.abs() <= 6, "recoding escaped the box");
        }
    }

    #[test]
    fn joint_recoding_small_reconstruction() {
        // Componentwise exactness on i128-safe magnitudes plus structure;
        // full-width inputs are covered by the per-curve `joint_recoding`
        // tests, which fold the digits in the scalar field instead.
        let mut state = 0x9E37_79B9_7F4A_7C15_u128;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut cases: Vec<(i128, i128)> = alloc::vec![
            (0, 0),
            (1, 0),
            (0, 1),
            (-1, -1),
            (5, -5),
            ((1 << 119) - 1, -((1 << 119) - 1)),
        ];
        for _ in 0..200 {
            let a = (next() & ((1 << 119) - 1)) as i128 - (1i128 << 118);
            let b = (next() & ((1 << 119) - 1)) as i128 - (1i128 << 118);
            cases.push((a, b));
        }
        for (a, b) in cases {
            let (digits, len) = joint_digits(a, b);
            assert!(len <= MAX_JOINT_DIGITS);
            let (mut ra, mut rb) = (0i128, 0i128);
            for &code in digits[..len].iter().rev() {
                ra *= 2;
                rb *= 2;
                if code != 0 {
                    let (da, db) = digit_coeffs(code);
                    ra += i128::from(da);
                    rb += i128::from(db);
                }
            }
            assert_eq!((ra, rb), (a, b), "digits must reconstruct the input");
            if len > 0 {
                assert_ne!(digits[len - 1], 0, "top digit must be nonzero");
            }
            for &tail in digits[len..].iter() {
                assert_eq!(tail, 0, "digits beyond len must be zero");
            }
        }
        // Full-magnitude structural checks (componentwise reconstruction of
        // these would overflow i128).
        for (a, b) in [
            (i128::MAX, -i128::MAX),
            (i128::MAX, i128::MAX),
            (-i128::MAX, 1),
        ] {
            let (digits, len) = joint_digits(a, b);
            assert!(len <= MAX_JOINT_DIGITS);
            assert_ne!(digits[len - 1], 0);
        }
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
            assert!(a1 >> GLV_COMPONENT_BITS == 0, "k1 exceeds 127 bits");
            assert!(a2 >> GLV_COMPONENT_BITS == 0, "k2 exceeds 127 bits");
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

    /// The joint Eisenstein recoding folds back to `k` in the scalar field
    /// (mirroring, digit for digit, what the ladder does in the group), has
    /// a nonzero top digit, respects the width-3 zero-run property, and
    /// stays within the length and density bounds.
    fn joint_recoding_reconstructs<C: GlvParams>() {
        let lambda = C::ScalarExt::ZETA;
        let check = |k: C::ScalarExt| {
            let d = Decomposed::<C>::new(&k);
            let mut acc = C::ScalarExt::ZERO;
            for &code in d.digits[..d.len].iter().rev() {
                acc = acc.double();
                if code != 0 {
                    acc += digit_scalar::<C::ScalarExt>(code);
                }
            }
            assert_eq!(acc, k, "joint digits must reconstruct k");
            assert!(d.len <= MAX_JOINT_DIGITS);
            if d.len > 0 {
                assert_ne!(d.digits[d.len - 1], 0, "top digit must be nonzero");
            }
            for (i, &code) in d.digits[..d.len].iter().enumerate() {
                if code != 0 {
                    for j in i + 1..(i + 3).min(d.len) {
                        assert_eq!(d.digits[j], 0, "width-3 property violated");
                    }
                }
            }
            assert!(
                d.digits[..d.len].iter().filter(|&&c| c != 0).count() <= 44,
                "more than ceil(132/3) nonzero digits"
            );
        };
        check(C::ScalarExt::ZERO);
        check(C::ScalarExt::ONE);
        check(-C::ScalarExt::ONE);
        check(lambda);
        check(-lambda);
        check(lambda + C::ScalarExt::ONE);
        for k in scalars::<C::ScalarExt>(500) {
            check(k);
        }
    }

    /// Every stored digit orbit (and every ζ-rotation and negation of it)
    /// equals the native scalar multiplication by its digit value.
    fn orbit_points_match_native<C: GlvParams>() {
        let g = C::generator();
        for k in scalars::<C::ScalarExt>(8) {
            let p = g * (k + C::ScalarExt::ONE);
            let table = Table::new(&p);
            for code in 1..=48u8 {
                assert_eq!(
                    C::from(table.digit_point(code)),
                    p * digit_scalar::<C::ScalarExt>(code),
                    "digit {code} must equal [a + b*lambda]P"
                );
            }
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

    /// The batched ladder equals the per-table ladder and the native `Mul`,
    /// across batch sizes straddling the affine crossover, with an identity
    /// point mixed in, for edge-case and full-width scalars. Sizes at or
    /// above [`BATCH_AFFINE_MIN_POINTS`] exercise the batch-affine kernel;
    /// the rest exercise the fallback.
    fn batch_mul_matches_per_table<C: GlvParams>() {
        let g = C::generator();
        let lambda = C::ScalarExt::ZETA;
        // At BATCH_AFFINE_MIN_POINTS the injected identity drops the live
        // count just below the threshold, exercising the live-counting
        // boundary of the fallback; the +33 size runs the kernel with the
        // identity mixed in.
        let sizes = [1, 3, BATCH_AFFINE_MIN_POINTS, BATCH_AFFINE_MIN_POINTS + 33];
        let ks = [
            C::ScalarExt::ZERO,
            C::ScalarExt::ONE,
            -C::ScalarExt::ONE,
            C::ScalarExt::from(2),
            lambda,
            -lambda,
            lambda + C::ScalarExt::ONE,
            C::ScalarExt::from_u128((1u128 << GLV_COMPONENT_BITS) - 1),
            scalars::<C::ScalarExt>(1).next().unwrap(),
        ];
        for size in sizes {
            let points: Vec<C> = (0..size)
                .map(|i| {
                    if size > 2 && i == size / 2 {
                        C::identity()
                    } else {
                        g * (C::ScalarExt::from(i as u64 + 1) + lambda)
                    }
                })
                .collect();
            let tables = Table::batch(&points);
            let refs: Vec<&Table<C>> = tables.iter().collect();
            for k in ks {
                let d = Decomposed::<C>::new(&k);
                let batched = Table::mul_decomposed_batch(&refs, &d);
                assert_eq!(batched.len(), points.len());
                for ((p, t), out) in points.iter().zip(&tables).zip(&batched) {
                    assert_eq!(*out, t.mul_decomposed(&d), "batch != per-table");
                    assert_eq!(*out, *p * k, "batch != native");
                }
            }
        }
    }

    /// Hand-crafted digit strings whose column schedules hit the affine
    /// ladder's exceptional cases: the batch entry must detect them and take
    /// the per-point fallback, keeping results exact. (Real recodings reach
    /// these states only through ~2^-124 lattice collisions, so the strings
    /// are constructed directly; a same-shape safe schedule keeps the kernel
    /// itself covered.)
    fn exceptional_schedules_fall_back<C: GlvParams>() {
        let craft = |positions: &[u8]| {
            let mut digits = [0u8; MAX_JOINT_DIGITS];
            digits[..positions.len()].copy_from_slice(positions);
            let mut value = C::ScalarExt::ZERO;
            for &code in positions.iter().rev() {
                value = value.double();
                if code != 0 {
                    value += digit_scalar::<C::ScalarExt>(code);
                }
            }
            let mut decomposed = Decomposed::<C> {
                digits,
                len: positions.len(),
                affine_ladder_safe: false,
                _curve: PhantomData,
            };
            decomposed.affine_ladder_safe = affine_ladder_safe::<C>(&decomposed);
            (decomposed, value)
        };

        // Digit strings are lowest position first; code 1 = +1, code 2 = -1.
        // d == s: top digit +1 (s = 1), then an active column with d = +1,
        // i.e. 2P + P — the direct formula's denominator vanishes.
        let d_eq_s = craft(&[1, 1]);
        // d == -s: 2P + (-P) = P. The direct formula handles this even
        // though the previous two-step formula's intermediate was identity.
        let d_eq_neg_s = craft(&[2, 1]);

        // d == -2s needs a mod-n lattice wraparound. Let L = v1 be the
        // first GLV lattice vector and D its unique joint digit mod 8. Then
        // S = (L - D)/2 is integral, and the schedule D || recode(S) reaches
        // the final active column with 2s + d = L = 0 in the scalar field.
        let lattice_a = i128::try_from(C::V1A).expect("v1.a fits i128");
        let lattice_b = -i128::try_from(C::V1B_NEG).expect("v1.b fits i128");
        let (da, db, code) = JOINT_DIGITS[(((lattice_a & 7) << 3) | (lattice_b & 7)) as usize];
        assert_ne!(code, 0, "v1 must be odd");
        let (prefix, prefix_len) = joint_digits(
            (lattice_a - i128::from(da)) / 2,
            (lattice_b - i128::from(db)) / 2,
        );
        assert!(prefix_len < MAX_JOINT_DIGITS);
        let mut positions = [0u8; MAX_JOINT_DIGITS];
        positions[0] = code;
        positions[1..prefix_len + 1].copy_from_slice(&prefix[..prefix_len]);
        let d_eq_neg_2s = craft(&positions[..prefix_len + 1]);
        assert_eq!(
            d_eq_neg_2s.1,
            C::ScalarExt::ZERO,
            "v1 schedule must fold to zero"
        );

        // Same shape, but safe (s = 2, d = -1): the kernel must handle it.
        let safe = craft(&[2, 0, 1]);

        assert!(!affine_ladder_safe::<C>(&d_eq_s.0));
        assert!(affine_ladder_safe::<C>(&d_eq_neg_s.0));
        assert!(!affine_ladder_safe::<C>(&d_eq_neg_2s.0));
        assert!(affine_ladder_safe::<C>(&safe.0));

        let g = C::generator();
        let points: Vec<C> = (0..BATCH_AFFINE_MIN_POINTS + 3)
            .map(|i| g * C::ScalarExt::from(i as u64 + 1))
            .collect();
        let tables = Table::batch(&points);
        let refs: Vec<&Table<C>> = tables.iter().collect();
        for (d, value) in [d_eq_s, d_eq_neg_s, d_eq_neg_2s, safe] {
            let batched = Table::mul_decomposed_batch(&refs, &d);
            for (p, out) in points.iter().zip(&batched) {
                assert_eq!(*out, *p * value, "crafted schedule must stay exact");
            }
        }
    }

    /// The affine FFT matches a direct projective radix-2 implementation,
    /// including inputs that force the affine butterfly fallback.
    fn affine_fft_matches_projective<C: GlvParams>() {
        fn reference<C: GlvParams>(points: &mut [C], omega: C::ScalarExt, log_n: u32) {
            fn bitreverse(mut value: usize, bits: usize) -> usize {
                let mut reversed = 0;
                for _ in 0..bits {
                    reversed = (reversed << 1) | (value & 1);
                    value >>= 1;
                }
                reversed
            }

            for i in 0..points.len() {
                let reversed = bitreverse(i, log_n as usize);
                if i < reversed {
                    points.swap(i, reversed);
                }
            }

            let mut chunk = 2;
            let mut twiddle_stride = points.len() / 2;
            while chunk <= points.len() {
                let twiddle_step = omega.pow_vartime([twiddle_stride as u64]);
                for block in points.chunks_mut(chunk) {
                    let (left, right) = block.split_at_mut(chunk / 2);
                    let mut twiddle = C::ScalarExt::ONE;
                    for (left, right) in left.iter_mut().zip(right) {
                        let scaled = *right * twiddle;
                        let old_left = *left;
                        *left = old_left + scaled;
                        *right = old_left - scaled;
                        twiddle *= twiddle_step;
                    }
                }
                chunk *= 2;
                twiddle_stride /= 2;
            }
        }

        for log_n in 1..=7 {
            let n = 1usize << log_n;
            let mut omega = C::ScalarExt::ROOT_OF_UNITY_INV;
            for _ in log_n..C::ScalarExt::S {
                omega = omega.square();
            }

            let generator = C::generator();
            let regular: Vec<C> = (0..n)
                .map(|i| generator * C::ScalarExt::from(i as u64 + 1))
                .collect();
            let exceptional: Vec<C> = (0..n)
                .map(|i| match i % 4 {
                    0 => C::identity(),
                    1 => generator,
                    2 => -generator,
                    _ => generator.double(),
                })
                .collect();
            let hash_to_curve = C::hash_to_curve("z.cash:test-affine-fft");
            let hashed: Vec<C> = (0..n)
                .map(|i| hash_to_curve(&(i as u64).to_le_bytes()))
                .collect();

            let mut inputs = alloc::vec![regular, exceptional, hashed];
            if log_n == 3 {
                // The first radix-2 stage produces an identity difference,
                // which the fused FFT8 codelet retains while it processes a
                // separate, identity-free branch. This checks that the clean
                // branch does not incorrectly strengthen the invariant for
                // the retained identity before the branches rejoin.
                inputs.push(
                    [1, 4, 2, 7, 1, 6, 3, 10]
                        .map(|multiple| generator * C::ScalarExt::from(multiple))
                        .into(),
                );
            }
            if log_n == 4 {
                // Exercise the analogous branch-and-rejoin path in the fused
                // FFT16 codelet. The equal points at indices zero and eight
                // produce an identity that the even-input branch omits.
                inputs.push(
                    [
                        398_522, 248_420, 840_455, 798_528, 624_324, 663_377, 434_118, 357_938,
                        398_522, 7_942, 752_351, 727_850, 16_691, 106_822, 861_757, 814_544,
                    ]
                    .map(|multiple| generator * C::ScalarExt::from(multiple))
                    .into(),
                );
            }

            for input in inputs {
                let mut expected = input.clone();
                reference(&mut expected, omega, log_n);
                let mut actual = alloc::vec![C::AffineExt::identity(); n];
                fft_vartime(&input, &mut actual, omega, log_n);
                assert!(actual
                    .iter()
                    .zip(expected)
                    .all(|(actual, expected)| C::from(*actual) == expected));
            }
        }
    }

    /// The specialized back-substitution covers tiny, odd, even, and FFT-size
    /// batches and agrees with independent field inversions.
    fn batch_inversion_matches_individual<C: GlvParams>() {
        for len in [
            1,
            2,
            3,
            4,
            31,
            32,
            33,
            127,
            128,
            129,
            TWIDDLE_MAJOR_MAX_CHUNK,
        ] {
            let mut current = C::Base::ONE;
            let mut values = Vec::with_capacity(len);
            for _ in 0..len {
                current += C::Base::ONE;
                values.push(current);
            }
            let expected: Vec<_> = values.iter().map(|value| value.invert().unwrap()).collect();
            let mut scratch = alloc::vec![C::Base::ZERO; len];
            #[cfg(all(
                feature = "aarch64-asm",
                target_arch = "aarch64",
                target_vendor = "apple"
            ))]
            batch_invert_nonzero::<C>(&mut values, &mut scratch);
            #[cfg(not(all(
                feature = "aarch64-asm",
                target_arch = "aarch64",
                target_vendor = "apple"
            )))]
            batch_invert_nonzero(&mut values, &mut scratch);
            assert_eq!(values, expected);
        }
    }

    /// Exact-alias paired multiplication covers odd, even, and FFT-size
    /// batches and agrees with independent field multiplications.
    fn paired_mul_assign_matches_individual<C: GlvParams>() {
        for len in [1, 2, 3, 31, 32, 33, 127, 128, 129, TWIDDLE_MAJOR_MAX_CHUNK] {
            let mut lhs_value = C::Base::ONE;
            let mut rhs_value = C::Base::ONE.double();
            let mut lhs = Vec::with_capacity(len);
            let mut rhs = Vec::with_capacity(len);
            for _ in 0..len {
                lhs_value += C::Base::ONE;
                rhs_value += C::Base::ONE;
                lhs.push(lhs_value);
                rhs.push(rhs_value);
            }
            let expected: Vec<_> = lhs.iter().zip(&rhs).map(|(lhs, rhs)| *lhs * rhs).collect();
            C::mul_base_assign_pairs(&mut lhs, &rhs, private::CrateToken(()));
            assert_eq!(lhs, expected);
        }
    }

    /// The direct one-inversion formula agrees with native group arithmetic
    /// whenever its denominator is nonzero.
    fn direct_double_add_matches_group<C: GlvParams>() {
        let generator = C::generator();
        let mut checked = 0;
        for p_scalar in 1..=16 {
            let p = generator * C::ScalarExt::from(p_scalar);
            for q_scalar in 1..=16 {
                let q = generator * C::ScalarExt::from(q_scalar);
                let mut affine = [C::AffineExt::identity(); 2];
                C::batch_normalize(&[p, q], &mut affine);
                let (x, y) = C::affine_xy(&affine[0]);
                let (u, v) = C::affine_xy(&affine[1]);
                let (denominator, h_squared) = double_add_denominator(x, y, u, v);
                let inverse = denominator.invert();
                if bool::from(inverse.is_none()) {
                    continue;
                }
                let (out_x, out_y) = double_add_finish(x, y, u, v, h_squared, inverse.unwrap());
                let actual = C::from(C::affine_unchecked(out_x, out_y, private::CrateToken(())));
                assert_eq!(actual, p.double() + q);
                checked += 1;
            }
        }
        assert!(checked > 200);

        let p = generator * C::ScalarExt::from(17);
        let q = -p;
        let mut affine = [C::AffineExt::identity(); 2];
        C::batch_normalize(&[p, q], &mut affine);
        let (x, y) = C::affine_xy(&affine[0]);
        let (u, v) = C::affine_xy(&affine[1]);
        let (denominator, h_squared) = double_add_denominator(x, y, u, v);
        let (out_x, out_y) =
            double_add_finish(x, y, u, v, h_squared, denominator.invert().unwrap());
        let actual = C::from(C::affine_unchecked(out_x, out_y, private::CrateToken(())));
        assert_eq!(actual, p);

        let q = p;
        C::batch_normalize(&[p, q], &mut affine);
        let (u, v) = C::affine_xy(&affine[1]);
        assert!(bool::from(double_add_denominator(x, y, u, v).0.is_zero()));

        let q = -p.double();
        C::batch_normalize(&[p, q], &mut affine);
        let (u, v) = C::affine_xy(&affine[1]);
        assert!(bool::from(double_add_denominator(x, y, u, v).0.is_zero()));
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
                fn joint_recoding() {
                    joint_recoding_reconstructs::<$curve>();
                }
                #[test]
                fn orbit_points() {
                    orbit_points_match_native::<$curve>();
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
                fn batch_mul() {
                    batch_mul_matches_per_table::<$curve>();
                }
                #[test]
                fn exceptional_fallback() {
                    exceptional_schedules_fall_back::<$curve>();
                }
                #[test]
                fn affine_fft() {
                    affine_fft_matches_projective::<$curve>();
                }
                #[test]
                fn batch_inversion() {
                    batch_inversion_matches_individual::<$curve>();
                }
                #[test]
                fn paired_mul_assign() {
                    paired_mul_assign_matches_individual::<$curve>();
                }
                #[test]
                fn direct_double_add() {
                    direct_double_add_matches_group::<$curve>();
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
            C::ScalarExt::from_u128((1u128 << GLV_COMPONENT_BITS) - 1),
            C::ScalarExt::from_u128(1u128 << GLV_COMPONENT_BITS),
            C::ScalarExt::from_u128((1u128 << GLV_COMPONENT_BITS) + 1),
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
    /// and pushes `|k2|` past the half-width bound that the joint
    /// recoding's i128 coefficients and `MAX_JOINT_DIGITS` rely on.
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
            a1 >> GLV_COMPONENT_BITS == 0 && a2 >> GLV_COMPONENT_BITS == 0,
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
            mag >> GLV_COMPONENT_BITS == 1,
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
    /// 2^127 bound and the pipeline rejects it on [`Decomposed::new`]'s
    /// bound assertion — in every build profile, since the joint recoding's
    /// i128 coefficients make the bound load-bearing. On the
    /// pre-`babai_coefficient_verify` code, this test alone detects the
    /// flip; nothing else in that suite did.
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
                            prop_assert!(a1 >> GLV_COMPONENT_BITS == 0);
                            prop_assert!(a2 >> GLV_COMPONENT_BITS == 0);
                            let s1 = Scalar::from_u128(a1);
                            let s1 = if neg1 { -s1 } else { s1 };
                            let s2 = Scalar::from_u128(a2);
                            let s2 = if neg2 { -s2 } else { s2 };
                            prop_assert_eq!(s1 + s2 * Scalar::ZETA, k);
                        }

                        /// For all k: the joint digits fold back to k in the
                        /// scalar field.
                        #[test]
                        fn joint_recoding_reconstructs(k in scalar_strategy::<Scalar>()) {
                            let d = Decomposed::<$curve>::new(&k);
                            let mut acc = Scalar::ZERO;
                            for &code in d.digits[..d.len].iter().rev() {
                                acc = acc.double();
                                if code != 0 {
                                    acc += digit_scalar::<Scalar>(code);
                                }
                            }
                            prop_assert_eq!(acc, k);
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
