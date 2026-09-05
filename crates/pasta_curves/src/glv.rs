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
//! Montgomery's trick, and every nonzero-digit column is evaluated as a
//! fused affine $2P + D$ (eliminating the intermediate y-coordinate and one
//! multiplication/squaring pair relative to double-then-add). Exceptional
//! column schedules — those that would hand an affine formula a zero
//! denominator — depend only on the scalar, are checked exactly per batch,
//! and fall back to the per-point ladder.
//!
//! Small arbitrary-scalar MSMs (`try_multiexp`, reached through
//! `CurveExt::try_multiexp_vartime`) use a GLV-Strauss ladder over the same
//! joint digits and [`Table`]s, sharing the ~127 doublings across every term.
//! Larger MSMs plan between two GLV bucket backends with `plan_multiexp`: the
//! Signed-Booth backend here, which windows the two decomposition halves
//! independently, and the Eisenstein-orbit backend in the `orbit` submodule,
//! which windows the joint value $k_1 + k_2\omega$ over
//! $\mathbf{Z}[\omega]$, quotients every digit by the six units (so a window
//! stores one bucket per unit *orbit* and visits each scalar once), and
//! integrates buckets with a hexagonal spanning-tree reducer. Both fill their
//! buckets through the shared batched-affine tree reduction below
//! (`reduce_affine_buckets`, one fused inversion-and-completion pass per tree
//! level). The orbit backend, its planning step, and the public `zero`
//! submodule are gated behind the `orbits` feature. Without it,
//! large MSMs use the Signed-Booth backend alone. Multicore builds still
//! compile the prepared evaluator privately for fixed-base callers through
//! [`CurveExt::try_prepare_zero_check`].
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
//! - [`Table`]: per *point*. For sufficiently large inputs, [`Table::batch`]
//!   builds many tables with a small sequence of batched affine additions,
//!   sharing each inversion across the batch.
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

use crate::arithmetic::{CurveExt, mac, sbb};
use crate::{pallas, vesta};

#[cfg(any(feature = "multicore", feature = "orbits"))]
mod orbit;
#[cfg(feature = "orbits")]
#[cfg_attr(docsrs, doc(cfg(feature = "orbits")))]
pub mod zero;
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
mod zero;

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

        /// Constructs a projective (Jacobian) point directly from raw
        /// coordinates, with no on-curve check in release builds; `z = 0`
        /// is the identity. The effective-affine machinery uses this to
        /// restore a table's omitted denominator into an ordinary point of
        /// the original curve without an inversion — the coordinates must
        /// satisfy $y^2 = x^3 + bz^6$, which the underlying constructor
        /// `debug_assert!`s.
        fn projective_unchecked(
            x: Self::Base,
            y: Self::Base,
            z: Self::Base,
            token: CrateToken,
        ) -> Self;
    }

    impl Sealed for crate::pallas::Point {
        fn affine_unchecked(x: Self::Base, y: Self::Base, _: CrateToken) -> Self::AffineExt {
            crate::pallas::Affine::from_xy_unchecked(x, y)
        }

        fn affine_xy(p: &Self::AffineExt) -> (Self::Base, Self::Base) {
            p.raw_xy()
        }

        fn projective_unchecked(
            x: Self::Base,
            y: Self::Base,
            z: Self::Base,
            _: CrateToken,
        ) -> Self {
            use crate::arithmetic::CurveExtUnchecked as _;
            Self::new_jacobian_unchecked(x, y, z)
        }
    }

    impl Sealed for crate::vesta::Point {
        fn affine_unchecked(x: Self::Base, y: Self::Base, _: CrateToken) -> Self::AffineExt {
            crate::vesta::Affine::from_xy_unchecked(x, y)
        }

        fn affine_xy(p: &Self::AffineExt) -> (Self::Base, Self::Base) {
            p.raw_xy()
        }

        fn projective_unchecked(
            x: Self::Base,
            y: Self::Base,
            z: Self::Base,
            _: CrateToken,
        ) -> Self {
            use crate::arithmetic::CurveExtUnchecked as _;
            Self::new_jacobian_unchecked(x, y, z)
        }
    }
}

#[cfg(any(feature = "multicore", feature = "orbits"))]
pub(super) fn prepare_zero_check<C: GlvParams>(
    bases: &[C::AffineExt],
) -> Option<alloc::boxed::Box<dyn crate::arithmetic::PreparedZeroCheck<C>>> {
    // `prepare` declines when no codebook mode fits its 13 MiB
    // accounted-footprint budget.
    zero::PreparedZeroMsm::<C>::prepare(bases).map(|prepared| {
        alloc::boxed::Box::new(prepared)
            as alloc::boxed::Box<dyn crate::arithmetic::PreparedZeroCheck<C>>
    })
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
        if v < 0 { -m } else { m }
    };
    signed(da) + signed(db) * F::ZETA
}

/// The effective-affine table builder's fixed addition chain, derived and
/// proved minimal by `sage/effective_affine_chain.sage` and re-derived from
/// first principles by the `effective_chain_derivation` test: starting from
/// $q_0 = P$, each step adds $D = 2P$ with an incomplete mixed addition and
/// then applies an Eisenstein unit,
///
/// $q_{i+1} = u_i(q_i + 2)$,
///
/// so the eight stored points visit the eight [`DELTA`] unit orbits exactly
/// once and no pre-addition state is $\pm 2$ (the incomplete formula's
/// exceptional case). Units are encoded like the [`JOINT_DIGITS`] unit
/// index — `[+1, -1, +ω, -ω, +ω², -ω²]`, `unit >> 1` the rotation exponent
/// and `unit & 1` the negation. Four of the seven units have a nontrivial
/// rotation (one x-coordinate multiplication each in the builder), the
/// exhaustive-search minimum: of the 54 valid seven-step chains, four
/// attain it, and this is the lexicographically least code sequence.
const EFFECTIVE_CHAIN_UNITS: [u8; 7] = [2, 0, 5, 2, 4, 0, 0];

/// How each chain path point relates to its canonical orbit representative:
/// `(slot, rotation, negate)` means
/// $q_i = \pm\omega^{\text{rotation}}\Delta_{\text{slot}}$ (`negate` for the
/// minus sign). The path visits every slot exactly once, so scattering the
/// chain into a table is a permutation:
/// `xs[e][slot] = ζ^((e - rotation) mod 3) · x(q_i)` and
/// `ys[slot] = ±y(q_i)`.
const EFFECTIVE_CHAIN_RELATIONS: [(u8, u8, bool); 8] = [
    (0, 0, false),
    (4, 1, false),
    (3, 1, false),
    (5, 1, false),
    (6, 2, false),
    (1, 1, false),
    (2, 2, true),
    (7, 2, true),
];

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
/// Minimum live inputs needed to amortize the table builder's five batched
/// affine inversions over its projective builder.
const TABLE_BATCH_AFFINE_MIN_POINTS: usize = 8;
// This range is tuned for the k = 11 parameter generation used by Orchard.
// Larger domains retain the point-major schedule above the measured range.
#[cfg(feature = "multicore")]
const TWIDDLE_MAJOR_MIN_CHUNK: usize = 16;
#[cfg(feature = "multicore")]
const TWIDDLE_MAJOR_MAX_CHUNK: usize = 2048;

/// Montgomery-batched inversion for provably nonzero values: prefix products
/// after each lane's head go into `scratch`, followed by one shared field
/// inversion and back-substitution. The ladder's denominators are nonzero by
/// [`affine_ladder_safe`], so unlike `ff::BatchInverter` this skips the
/// per-element zero handling (one extra multiplication and two conditional
/// selects per element), which is a measurable share of each ladder column.
/// Twin implementation: `batch_invert_multi` in
/// `halo2_proofs/src/arithmetic.rs` is the same even/odd two-lane walk with
/// `ff`-style (variable-time) zero skipping and internally allocated
/// scratch; `Curve::batch_normalize` in `src/curves.rs` fuses the walk with
/// the Jacobian-to-affine conversion. Keep the three in step when changing
/// any of them.
fn batch_invert_nonzero<F: Field>(values: &mut [F], scratch: &mut [F]) {
    assert_eq!(values.len(), scratch.len());
    let Some((first, values)) = values.split_first_mut() else {
        return;
    };

    debug_assert!(!first.is_zero_vartime());
    if values.is_empty() {
        *first = first.invert().unwrap();
        return;
    }

    let (second, values) = values.split_first_mut().unwrap();
    debug_assert!(!second.is_zero_vartime());
    let scratch = &mut scratch[2..];

    // Two accumulator chains, stepped in (even, odd) pairs: the classic
    // single-chain walk runs both passes at the field multiplication's
    // dependency latency, while independent even/odd chains run at its
    // throughput, for a fixed overhead of three extra multiplications per
    // call (one join before the shared inversion, two lane-seed recoveries
    // after). The hot ladder calls this with `BATCH_AFFINE_MIN_POINTS` or
    // more live lanes; auxiliary prepared-point paths can pass smaller
    // batches, including the singleton handled above. A trailing element
    // (odd length) has an even index and belongs to the first chain.
    // Seed each lane from its first value. Besides removing the initial
    // multiplication by one, this lets the backward pass assign the first
    // two inverses directly and omit its final multiplication in each lane.
    let mut acc0 = *first;
    let mut acc1 = *second;
    for (pair, slots) in values.chunks_exact(2).zip(scratch.chunks_exact_mut(2)) {
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
    *first = acc0;
    *second = acc1;
}

/// Small MSMs do not amortize GLV decomposition, affine endomorphism mapping,
/// and the two temporary vectors.
const MIN_GLV_MULTIEXP_TERMS: usize = 256;

/// Largest serial leaf in the GLV-Strauss backend. The crossover is
/// benchmark-tuned against halo2's generic Signed-Booth fallback at the
/// power-of-two sizes reached by the late IPA rounds.
const STRAUSS_LEAF_TERMS: usize = 16;

/// Smallest MSM worth splitting across an IPA side's worker budget.
#[cfg(feature = "multicore")]
const MIN_PARALLEL_STRAUSS_TERMS: usize = 3;

/// Largest parallel MSM split into [`STRAUSS_LEAF_TERMS`]-or-smaller Strauss
/// leaves. This includes a 64-term late IPA half plus its two auxiliary terms.
/// Above this, the generic or GLV bucket backends amortize their bucket setup
/// and use the worker pool more efficiently.
#[cfg(feature = "multicore")]
const MAX_PARALLEL_STRAUSS_TERMS: usize = 66;

/// Each GLV decomposition component has magnitude strictly below `2^127`.
const GLV_COMPONENT_BITS: usize = 127;

/// Estimates a Signed-Booth MSM's costs as a `(work, traffic)` pair: the
/// dominant group work, and the total point/window visits plus bucket
/// additions — the traffic the planner's shared-bandwidth floor scales,
/// since a wide pool cannot divide it away (see `plan_multiexp`).
///
/// The serial work model counts total point/window visits, bucket additions,
/// and accumulator doublings. The parallel model estimates the corresponding
/// critical-worker cost when windows have independent accumulators. Both omit
/// GLV setup costs; [`MIN_GLV_MULTIEXP_TERMS`] handles their small-MSM
/// amortization separately.
fn estimated_signed_booth_costs(
    terms: usize,
    scalar_bits: usize,
    window_bits: usize,
    num_threads: usize,
) -> Option<(usize, usize)> {
    let windows = scalar_bits.checked_div(window_bits)?.checked_add(1)?;
    let bucket_shift = u32::try_from(window_bits.checked_sub(1)?).ok()?;
    let buckets = 1usize.checked_shl(bucket_shift)?;
    let point_visits = terms.checked_mul(windows)?;
    let bucket_additions = buckets.checked_mul(windows)?.checked_mul(2)?;
    let traffic = point_visits.checked_add(bucket_additions)?;

    if num_threads <= 1 {
        let doublings = window_bits.checked_mul(windows.checked_sub(1)?)?;
        return Some((traffic.checked_add(doublings)?, traffic));
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
    Some((
        per_window
            .checked_mul(waves)?
            .checked_add(shift_doublings)?,
        traffic,
    ))
}

/// Test convenience: the work component of [`estimated_signed_booth_costs`].
#[cfg(test)]
fn estimated_signed_booth_work(
    terms: usize,
    scalar_bits: usize,
    window_bits: usize,
    num_threads: usize,
) -> Option<usize> {
    estimated_signed_booth_costs(terms, scalar_bits, window_bits, num_threads).map(|(work, _)| work)
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
    let current = estimated_signed_booth_costs(terms, scalar_bits, window_bits, num_threads)
        .map(|(work, _)| work);
    let next = estimated_signed_booth_costs(terms, scalar_bits, next_window_bits, num_threads)
        .map(|(work, _)| work);
    Some(
        if matches!((current, next), (Some(current), Some(next)) if next < current) {
            next_window_bits
        } else {
            window_bits
        },
    )
}

/// Plans a GLV multiscalar multiplication: the window width the GLV ladder
/// should use for `terms` on `num_threads` workers, or `None` when the
/// generic MSM is estimated to be cheaper.
///
/// The generic MSM runs at the default width `w` from
/// [`multiexp_window_bits`]. The GLV ladder is evaluated at both `w` and
/// `w + 1` and takes the cheaper; it is chosen when that beats the generic
/// estimate. GLV has about half as many windows as the generic ladder
/// (127-bit components), so the parallel model's wave count — windows
/// divided by workers, rounded up — is much more sensitive to the width for
/// GLV than for the generic ladder, and comparing the two at a single width
/// chosen for the generic ladder mispredicts: e.g. 8,192 terms on 3 workers
/// puts 13 GLV windows into 5 waves at `w = 10` but 12 windows into exactly
/// 4 waves at `w = 11`. Measured on Apple M4 (asm backend) and EPYC
/// (portable) across 1–16 workers and 2,150–65,536 terms, this choice
/// selected the faster backend in every one of 46 cells, where the
/// single-width comparison was wrong in 8 (M4) and 5 (EPYC) — all cases
/// where GLV was faster by 4–27% but not chosen. The width is only ever
/// widened: a narrower GLV window never measured a meaningful gain.
/// (Under the `orbits` feature, production planning goes through
/// `plan_multiexp`, which extends this Booth-versus-generic comparison with
/// the orbit backend and this becomes test-only — the measured-cell
/// contract for the Booth half of that decision, pinned by
/// `glv_multiexp_plan_matches_measured_cells`. Without the feature this is
/// the production planner, as before.)
#[cfg(any(test, not(feature = "orbits")))]
fn glv_multiexp_window_bits<C: GlvParams>(terms: usize, num_threads: usize) -> Option<usize> {
    if terms < MIN_GLV_MULTIEXP_TERMS {
        return None;
    }
    let (generic, _) = estimated_generic_costs::<C>(terms, num_threads)?;
    let (glv, glv_window_bits) = booth_multiexp_estimate::<C>(terms, num_threads)?;
    (glv < generic).then_some(glv_window_bits)
}

/// The generic Signed-Booth MSM's estimated `(work, traffic)` costs at its
/// default width (see [`estimated_signed_booth_costs`]).
fn estimated_generic_costs<C: GlvParams>(
    terms: usize,
    num_threads: usize,
) -> Option<(usize, usize)> {
    let window_bits = multiexp_window_bits::<C>(terms, num_threads)?;
    let scalar_bits = scalar_repr_bits::<C>()?;
    estimated_signed_booth_costs(terms, scalar_bits, window_bits, num_threads)
}

/// The Signed-Booth GLV backend's cheapest `(work, window width)` over the
/// candidate widths `w` and `w + 1` (see [`glv_multiexp_window_bits`]).
#[cfg(any(test, not(feature = "orbits")))]
fn booth_multiexp_estimate<C: GlvParams>(
    terms: usize,
    num_threads: usize,
) -> Option<(usize, usize)> {
    let window_bits = multiexp_window_bits::<C>(terms, num_threads)?;
    let glv_terms = terms.checked_mul(2)?;
    let mut best: Option<(usize, usize)> = None;
    for candidate in window_bits..=window_bits.checked_add(1)? {
        if let Some((work, _)) =
            estimated_signed_booth_costs(glv_terms, GLV_COMPONENT_BITS, candidate, num_threads)
            && best.is_none_or(|(best_work, _)| work < best_work)
        {
            best = Some((work, candidate));
        }
    }
    best
}

/// The shared-memory-bandwidth floor on the parallel backend estimates, as
/// a percentage of the estimate's total group-operation count: wide pools
/// divide per-worker work but not total traffic, so past the saturation
/// point the estimate may not fall below this fraction of the total. The
/// value is fit from the 2026-08-26 interleaved `msm_backend_timings`
/// grids (x86-64, portable and assembly field arithmetic), where 8% more
/// than halved the planner's summed cell losses on both; by construction
/// it binds only above ~12 workers (below that, per-worker work exceeds
/// it).
#[cfg(feature = "orbits")]
const PARALLEL_TRAFFIC_FLOOR_PERCENT: usize = 8;

/// The worker count above which the floor also enters the
/// backend-versus-backend comparison (it always shapes the orbit width
/// choice). At 16 workers the mid-size Booth/orbit boundary measures in
/// *opposite* directions on the two production hosts (see
/// [`plan_multiexp`]), so the comparison stays unfloored there — though
/// the orbit side still enters it at its floor-picked width.
#[cfg(feature = "orbits")]
const TRAFFIC_FLOOR_COMPARISON_THREADS: usize = 16;

/// [`PARALLEL_TRAFFIC_FLOOR_PERCENT`] of an estimate's total.
#[cfg(feature = "orbits")]
fn traffic_floor(traffic: usize) -> Option<usize> {
    Some(traffic.checked_mul(PARALLEL_TRAFFIC_FLOOR_PERCENT)? / 100)
}

/// The bit length of a decomposition half's magnitude.
#[cfg(feature = "orbits")]
fn bit_length(magnitude: u128) -> usize {
    (u128::BITS - magnitude.leading_zeros()) as usize
}

/// Magnitude profile of a decomposed MSM input: suffix counts of component
/// and per-scalar (joint) magnitude bit lengths, so the backend models can
/// price only the windows each scalar actually reaches.
///
/// Real proving workloads are far from uniformly full-width: halo2 witness
/// commitments mix boolean columns, small decompositions, and zero padding
/// rows between full-width values, and both bucket backends skip a scalar's
/// empty windows. Pricing by term count alone mistakes those MSMs for
/// full-width ones; measured on serial Orchard proving — whose commitment
/// MSMs range from all-full-width to `2040 of 2049 zero` — count-only
/// planning sent sparse MSMs to the orbit backend, whose radix-2^c joint
/// recoding spreads a small magnitude over ~9/5 as many windows as the
/// Booth halves, costing ~4% of total proving time.
#[cfg(feature = "orbits")]
pub(crate) struct MagnitudeProfile {
    terms: usize,
    /// `component_live[b]`: decomposition halves with magnitude above `b`
    /// bits.
    component_live: [usize; 129],
    /// `scalar_live[b]`: scalars either of whose halves is above `b` bits.
    scalar_live: [usize; 129],
}

#[cfg(feature = "orbits")]
impl MagnitudeProfile {
    fn new(components: &[(SignedMagnitude, SignedMagnitude)]) -> Self {
        let mut component_hist = [0usize; 129];
        let mut scalar_hist = [0usize; 129];
        for (first, second) in components {
            let first = bit_length(first.magnitude);
            let second = bit_length(second.magnitude);
            component_hist[first] += 1;
            component_hist[second] += 1;
            scalar_hist[first.max(second)] += 1;
        }
        let mut component_live = [0usize; 129];
        let mut scalar_live = [0usize; 129];
        for bits in (0..128).rev() {
            component_live[bits] = component_live[bits + 1] + component_hist[bits + 1];
            scalar_live[bits] = scalar_live[bits + 1] + scalar_hist[bits + 1];
        }
        MagnitudeProfile {
            terms: components.len(),
            component_live,
            scalar_live,
        }
    }

    /// Decomposition halves whose magnitude exceeds `bits` bits.
    fn component_live(&self, bits: usize) -> usize {
        self.component_live[bits.min(128)]
    }

    /// Scalars either of whose halves' magnitude exceeds `bits` bits.
    pub(super) fn scalar_live(&self, bits: usize) -> usize {
        self.scalar_live[bits.min(128)]
    }
}

/// The Signed-Booth backend's estimated `(work, traffic)` costs for a
/// profiled input at one width, in [`estimated_signed_booth_costs`]'s
/// structure and units, but visiting only the windows each decomposition
/// half's magnitude reaches and integrating buckets only for windows some
/// half reaches. Doublings are unchanged — the ladder Horner-shifts through
/// empty windows too — and count toward the work but not the traffic (the
/// visits plus bucket additions the planner's bandwidth floor scales). On
/// uniformly full-width inputs this degenerates to (just under) the
/// count-based model.
#[cfg(feature = "orbits")]
fn booth_profiled_costs(
    profile: &MagnitudeProfile,
    window_bits: usize,
    num_threads: usize,
) -> Option<(usize, usize)> {
    let windows = GLV_COMPONENT_BITS
        .checked_div(window_bits)?
        .checked_add(1)?;
    let bucket_shift = u32::try_from(window_bits.checked_sub(1)?).ok()?;
    let buckets = 1usize.checked_shl(bucket_shift)?;

    let mut visits = 0usize;
    let mut active_windows = 0usize;
    for window in 0..windows {
        let live = profile.component_live(window.checked_mul(window_bits)?);
        if live > 0 {
            visits = visits.checked_add(live)?;
            active_windows = window + 1;
        }
    }
    let bucket_additions = buckets.checked_mul(active_windows)?.checked_mul(2)?;
    let traffic = visits.checked_add(bucket_additions)?;

    if num_threads <= 1 {
        let doublings = window_bits.checked_mul(windows.checked_sub(1)?)?;
        return Some((traffic.checked_add(doublings)?, traffic));
    }

    // As in the count-based parallel model: whole waves of the per-window
    // average, plus the critical worker's strided shift doublings.
    let workers = num_threads.min(windows);
    let waves = windows.div_ceil(workers);
    let per_window = traffic.div_ceil(windows);
    let mut shift_doublings = 0usize;
    let mut window = windows.checked_sub(1)?;
    for _ in 0..waves {
        shift_doublings = shift_doublings.checked_add(window_bits.checked_mul(window)?)?;
        match window.checked_sub(workers) {
            Some(next) => window = next,
            None => break,
        }
    }
    Some((
        per_window
            .checked_mul(waves)?
            .checked_add(shift_doublings)?,
        traffic,
    ))
}

/// A backend and window width selected by [`plan_multiexp`].
#[cfg(feature = "orbits")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MultiexpPlan {
    /// The Signed-Booth backend over the two decomposition halves.
    Booth { window_bits: usize },
    /// The Eisenstein-orbit backend over the joint value (see [`orbit`]).
    Orbit { window_bits: usize },
}

/// Plans a GLV multiscalar multiplication across both bucket backends: the
/// cheapest of the Signed-Booth widths `w`/`w + 1` (as in
/// `glv_multiexp_window_bits`) and the Eisenstein-orbit widths 4..=6,
/// or `None` when the generic MSM is estimated to be cheaper than both.
///
/// All three estimates share [`estimated_signed_booth_costs`]'s units (the
/// orbit model carries its own measured calibration constants; see
/// [`orbit::estimated_costs`]), and the two GLV backends are priced from the
/// input's [`MagnitudeProfile`], since their relative cost depends strongly
/// on scalar magnitudes, not just the term count. Ties keep the Signed-Booth
/// backend (candidates are compared strictly, Booth first).
///
/// Measured on 32-core x86-64 (see `multiexp_plan_selection`), for
/// full-width scalars the orbit backend runs serial MSMs at parity with
/// Booth (within ±2% at 512–8,192 terms, +4–5% ahead at 16,384 — the
/// model's serial orbit preference is harmless there), takes mid-to-large
/// parallel MSMs (+10..+41% at 4–16 workers), and everything on saturated
/// pools, where its 22–33 windows keep workers fed that Booth's 10–16
/// cannot (+30..+54% at 32); Booth keeps small parallel MSMs, and takes
/// over as scalars shrink (halo2 witness commitments mix boolean,
/// byte-sized, and zero scalars), where its half-columns reach far fewer
/// windows than the joint radix-$2^c$ recoding.
///
/// **Shared-bandwidth floor (2026-08-26 re-fit):** the per-worker parallel
/// estimates alone let wide pools divide away total memory traffic, which
/// hardware does not: past the point where every window has a worker, the
/// backends become bandwidth-bound and total traffic — not per-worker
/// work — sets the wall time. Each parallel estimate is therefore floored
/// at [`PARALLEL_TRAFFIC_FLOOR_PERCENT`] of its total group-operation
/// count. The floor shapes the orbit backend's *width* choice on any
/// parallel pool (it is what knows that wider windows move less data: it
/// fixes the measured c5-over-c6 mispick at 65,536 terms on 16 and 32
/// workers, +5–13% on both grids and both curves, and the c5-over-c4
/// mispicks at 512–2,048 terms on 32 workers, up to +28%; on 16 workers
/// the width-5/6 boundary lands near 28,672 terms, and flipping the
/// k = 15 verifier's 32,770-term check to width 6 measured end to end on
/// M4 Max as that verifier's ~5% orbit loss becoming parity), but joins
/// the backend-versus-backend comparison only past
/// [`TRAFFIC_FLOOR_COMPARISON_THREADS`] workers: at 16 workers the
/// mid-size backend boundary is measured *opposite* on the two production
/// hosts (orbit ahead on 16-core/SMT x86, Booth ahead on M4 Max), so
/// below that the comparison deliberately stays between unfloored work
/// values — with the orbit side evaluated at its floor-picked width, which
/// can differ from the unfloored minimum where the floor changes the
/// width. Fit on interleaved `msm_backend_timings` medians (x86-64,
/// portable and assembly field grids, 2026-08-26); the floor is inert at
/// eight or fewer workers, where per-worker work exceeds it by
/// construction.
///
/// **Calibration staleness (2026-08-24, updated 2026-08-26):** the visit
/// constants above were fit before the Signed-Booth base-coordinate
/// caching and window pairing; the 2026-08-26 grids show the *serial* and
/// low-worker selections still match every reproducible measured winner
/// (the corrected serial picture is the parity above; the harness's
/// first-curve serial Booth inflation persists — trust the second curve's
/// serial Booth column). Known remaining gaps, deliberately left at the
/// current boundary pending per-architecture calibration: the 16-worker
/// mid-size conflict above, witness-shaped under-selection at 8–16
/// workers on x86 (+6–10% forgone, opposite sign on M4), and small
/// (≤5%) over-selections at 4 workers.
#[cfg(feature = "orbits")]
fn plan_multiexp<C: GlvParams>(
    profile: &MagnitudeProfile,
    num_threads: usize,
) -> Option<MultiexpPlan> {
    let terms = profile.terms;
    if terms < MIN_GLV_MULTIEXP_TERMS {
        return None;
    }
    let comparison_floored = num_threads > TRAFFIC_FLOOR_COMPARISON_THREADS;

    let generic = {
        let (base, traffic) = estimated_generic_costs::<C>(terms, num_threads)?;
        if comparison_floored {
            base.max(traffic_floor(traffic)?)
        } else {
            base
        }
    };

    let mut best: Option<(usize, MultiexpPlan)> = None;
    let window_bits = multiexp_window_bits::<C>(terms, num_threads)?;
    for candidate in window_bits..=window_bits.checked_add(1)? {
        if let Some((work, traffic)) = booth_profiled_costs(profile, candidate, num_threads) {
            let metric = if comparison_floored {
                work.max(traffic_floor(traffic)?)
            } else {
                work
            };
            if best.is_none_or(|(best_work, _)| metric < best_work) {
                best = Some((
                    metric,
                    MultiexpPlan::Booth {
                        window_bits: candidate,
                    },
                ));
            }
        }
    }

    // The orbit width is picked by the floored estimate on any parallel
    // pool — total traffic is what distinguishes the widths once workers
    // stop being the constraint — while the value entered into the
    // backend comparison honors `comparison_floored` like the others.
    let mut orbit_pick: Option<(usize, usize, usize)> = None;
    for candidate in orbit::PLAN_MIN_WINDOW_BITS..=orbit::MAX_WINDOW_BITS {
        if let Some((work, traffic)) = orbit::estimated_costs(profile, candidate, num_threads) {
            let width_metric = if num_threads > 1 {
                work.max(traffic_floor(traffic)?)
            } else {
                work
            };
            if orbit_pick.is_none_or(|(best_metric, _, _)| width_metric < best_metric) {
                orbit_pick = Some((width_metric, work, candidate));
            }
        }
    }
    if let Some((width_metric, work, candidate)) = orbit_pick {
        let metric = if comparison_floored {
            width_metric
        } else {
            work
        };
        if best.is_none_or(|(best_work, _)| metric < best_work) {
            best = Some((
                metric,
                MultiexpPlan::Orbit {
                    window_bits: candidate,
                },
            ));
        }
    }

    let (work, plan) = best?;
    (work < generic).then_some(plan)
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

/// A small MSM through one shared doubling ladder over jointly recoded GLV
/// scalars. Each point's eight orbit representatives are batch-normalized with
/// every other table, then each nonzero digit contributes one mixed addition.
///
/// This is Strauss' algorithm with the existing joint width-3 Eisenstein NAF
/// in place of two independent integer wNAFs. It retains the ~127-column GLV
/// ladder while averaging fewer additions and one table per input point.
fn strauss_multiexp<C: GlvParams>(scalars: &[C::ScalarExt], bases: &[C::AffineExt]) -> C {
    debug_assert_eq!(scalars.len(), bases.len());

    let mut decomposed = Vec::with_capacity(scalars.len());
    let mut points = Vec::with_capacity(bases.len());
    for (scalar, base) in scalars.iter().zip(bases) {
        let scalar = Decomposed::<C>::new(scalar);
        if scalar.len == 0 || bool::from(base.is_identity()) {
            continue;
        }
        decomposed.push(scalar);
        points.push(base.to_curve());
    }
    if decomposed.is_empty() {
        return C::identity();
    }

    let tables = Table::batch(&points);
    let columns = decomposed
        .iter()
        .map(|scalar| scalar.len)
        .max()
        .expect("at least one nonzero scalar");
    let mut acc = C::identity();
    for column in (0..columns).rev() {
        if column + 1 < columns {
            acc = acc.double();
        }
        for (scalar, table) in decomposed.iter().zip(&tables) {
            let code = scalar.digits[column];
            if code != 0 {
                acc += table.digit_point(code);
            }
        }
    }
    acc
}

#[cfg(feature = "multicore")]
fn strauss_multiexp_leaves<C: GlvParams>(scalars: &[C::ScalarExt], bases: &[C::AffineExt]) -> C {
    scalars
        .chunks(STRAUSS_LEAF_TERMS)
        .zip(bases.chunks(STRAUSS_LEAF_TERMS))
        .map(|(scalars, bases)| strauss_multiexp::<C>(scalars, bases))
        .fold(C::identity(), |left, right| left + right)
}

fn planned_strauss_multiexp<C: GlvParams>(
    scalars: &[C::ScalarExt],
    bases: &[C::AffineExt],
    num_threads: usize,
) -> Option<C> {
    #[cfg(feature = "multicore")]
    if (MIN_PARALLEL_STRAUSS_TERMS..=MAX_PARALLEL_STRAUSS_TERMS).contains(&scalars.len())
        && num_threads > 1
    {
        // Late IPA evaluates L and R together. Give this side at most half the
        // pool, so both commitments make progress at once. Each worker retains
        // the measured leaf crossover internally rather than building one wide
        // table for its entire share.
        let worker_jobs = num_threads.div_ceil(2).min(scalars.len());
        if worker_jobs == 1 {
            return Some(strauss_multiexp_leaves::<C>(scalars, bases));
        }
        return Some(
            (0..worker_jobs)
                .into_par_iter()
                .map(|job| {
                    let start = scalars.len() * job / worker_jobs;
                    let end = scalars.len() * (job + 1) / worker_jobs;
                    strauss_multiexp_leaves::<C>(&scalars[start..end], &bases[start..end])
                })
                .reduce(C::identity, |left, right| left + right),
        );
    }

    if scalars.len() <= STRAUSS_LEAF_TERMS {
        return Some(strauss_multiexp::<C>(scalars, bases));
    }

    #[cfg(not(feature = "multicore"))]
    let _ = num_threads;
    None
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

#[derive(Clone, Copy)]
struct WindowAssignment {
    component: usize,
    signed_bucket: isize,
}

#[derive(Clone, Copy)]
struct MultiexpBase<F> {
    x: F,
    endo_x: F,
    y: F,
    identity: bool,
}

impl WindowAssignment {
    fn bucket(self) -> usize {
        self.signed_bucket.unsigned_abs() - 1
    }

    fn negative(self) -> bool {
        self.signed_bucket < 0
    }
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
struct AffinePoint<F> {
    x: F,
    y: F,
}

// This is deliberately a correctness-first staging representation: keeping the
// chord terms and batch-inversion scratch together makes their association easy
// to audit. The left operand now lives in its `points[output]` result slot,
// which already reduces memory traffic while preserving that relationship.
// This is faster than projective bucket reduction; the intended end state
// removes the remaining record to save more memory traffic.
struct PendingAffineAddition<F> {
    output: usize,
    x_sum: F,
    numerator: F,
    denominator: F,
    inversion_scratch: F,
}

/// Independent multiplication lanes used by batch inversion.
const BATCH_INVERSION_LANES: usize = 2;

/// Batch-inverts affine denominators and immediately finishes the additions.
///
/// Each `output` identifies the slot containing the addition's left operand.
/// The outputs must be distinct. Returns `None` if the product of the
/// denominators is zero. In that case, this function has not written to
/// `points`: the prefix pass changes only disposable inversion scratch, and
/// the output pass starts only after the product is successfully inverted.
/// [`reduce_affine_buckets`] combines this failure-atomic behavior with
/// separate level staging before it retries an exceptional level.
fn batch_invert_and_add<F: Field>(
    additions: &mut [PendingAffineAddition<F>],
    points: &mut [AffinePoint<F>],
) -> Option<()> {
    let Some((first, additions)) = additions.split_first_mut() else {
        return Some(());
    };

    if additions.is_empty() {
        let denominator_inverse = Option::<F>::from(first.denominator.invert())?;
        let left = points[first.output];
        let slope = first.numerator * denominator_inverse;
        let x = slope.square() - first.x_sum;
        let y = slope * (left.x - x) - left.y;
        points[first.output] = AffinePoint { x, y };
        return Some(());
    }

    let (second, additions) = additions.split_first_mut().unwrap();

    // Compute two prefix lanes in lockstep. This retains one field inversion
    // for the entire batch while exposing independent multiplication chains.
    // Seeding from the first denominator in each lane removes the initial
    // multiplication by one and lets the backward pass assign those two
    // inverses directly, without a scratch multiplication or dead update.
    let mut lane_products = [first.denominator, second.denominator];
    for pair in additions.chunks_mut(BATCH_INVERSION_LANES) {
        for (addition, product) in pair.iter_mut().zip(&mut lane_products) {
            addition.inversion_scratch = *product;
            *product *= addition.denominator;
        }
    }

    // Invert both lane products with one inversion. A field has no zero
    // divisors, so this product is zero exactly when at least one affine
    // denominator is zero. No output point has been written yet; `?` therefore
    // makes failure atomic with respect to `points`. Writes to
    // `inversion_scratch` are discarded by the caller on failure.
    let product = lane_products[0] * lane_products[1];
    // This MSM is already variable-time with respect to scalar digits; batch
    // inversion does not provide a constant-time guarantee.
    let product_inverse = Option::<F>::from(product.invert())?;
    let mut lane_inverses = [
        lane_products[1] * product_inverse,
        lane_products[0] * product_inverse,
    ];

    // If the last pair is incomplete, consume its first lane before walking
    // the complete pairs backward.
    let complete_pairs = additions.len() / BATCH_INVERSION_LANES;
    if additions.len() % BATCH_INVERSION_LANES != 0 {
        let addition = &additions[additions.len() - 1];
        let denominator = addition.denominator;
        let denominator_inverse = addition.inversion_scratch * lane_inverses[0];
        lane_inverses[0] *= denominator;

        let left = points[addition.output];
        let slope = addition.numerator * denominator_inverse;
        let x = slope.square() - addition.x_sum;
        let y = slope * (left.x - x) - left.y;
        points[addition.output] = AffinePoint { x, y };
    }
    for pair in additions[..complete_pairs * BATCH_INVERSION_LANES]
        .chunks(BATCH_INVERSION_LANES)
        .rev()
    {
        let first = &pair[0];
        let second = &pair[1];
        let first_inverse = first.inversion_scratch * lane_inverses[0];
        let second_inverse = second.inversion_scratch * lane_inverses[1];
        lane_inverses[0] *= first.denominator;
        lane_inverses[1] *= second.denominator;

        // Complete each affine chord addition while its pending record is
        // already resident. Keep two independent field-operation lanes.
        let first_left = points[first.output];
        let second_left = points[second.output];
        let first_slope = first.numerator * first_inverse;
        let second_slope = second.numerator * second_inverse;
        let first_x = first_slope.square() - first.x_sum;
        let second_x = second_slope.square() - second.x_sum;
        let first_y = first_slope * (first_left.x - first_x) - first_left.y;
        let second_y = second_slope * (second_left.x - second_x) - second_left.y;
        points[first.output] = AffinePoint {
            x: first_x,
            y: first_y,
        };
        points[second.output] = AffinePoint {
            x: second_x,
            y: second_y,
        };
    }

    let first_left = points[first.output];
    let second_left = points[second.output];
    let first_slope = first.numerator * lane_inverses[0];
    let second_slope = second.numerator * lane_inverses[1];
    let first_x = first_slope.square() - first.x_sum;
    let second_x = second_slope.square() - second.x_sum;
    let first_y = first_slope * (first_left.x - first_x) - first_left.y;
    let second_y = second_slope * (second_left.x - second_x) - second_left.y;
    points[first.output] = AffinePoint {
        x: first_x,
        y: first_y,
    };
    points[second.output] = AffinePoint {
        x: second_x,
        y: second_y,
    };
    Some(())
}

/// Collects the nonzero signed points assigned to one Booth window.
fn window_assignments<C>(
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[MultiexpBase<C::Base>],
    window_bits: usize,
    window: usize,
) -> (Vec<WindowAssignment>, Vec<usize>)
where
    C: GlvParams,
{
    let bucket_count = 1 << (window_bits - 1);
    let mut assignments = Vec::with_capacity(bases.len().saturating_mul(2));
    let mut counts = alloc::vec![0usize; bucket_count];

    for (base_index, ((first, second), base)) in components.iter().zip(bases).enumerate() {
        if base.identity {
            continue;
        }
        for (component_offset, component) in [*first, *second].into_iter().enumerate() {
            let digit = booth_digit(component, window_bits, window);
            if digit.magnitude != 0 {
                let bucket = digit.magnitude - 1;
                let magnitude =
                    isize::try_from(digit.magnitude).expect("Booth digit magnitude fits in isize");
                assignments.push(WindowAssignment {
                    component: base_index * 2 + component_offset,
                    signed_bucket: if digit.negative {
                        -magnitude
                    } else {
                        magnitude
                    },
                });
                counts[bucket] += 1;
            }
        }
    }

    (assignments, counts)
}

/// Reduces every affine bucket through shared Montgomery batch inversions.
///
/// `offsets` partitions `points` into one contiguous range per bucket. At
/// each tree level, all independent additions share one inversion. The normal
/// route uses incomplete chord additions without per-pair coordinate checks;
/// a zero batch product restarts that level with complete handling for
/// identity, doubling, and inverse pairs.
///
/// For valid points on a short-Weierstrass curve over an odd-prime field,
/// equal x-coordinates imply equal or opposite y-coordinates. Thus the only
/// zero-denominator cases omitted by the incomplete chord formula are a
/// doubling and an inverse pair. The latter includes the y = 0 overlap, which
/// is a point of order two and sums with itself to the identity.
///
/// Each level is built in `next_points` and `next_offsets`, while `points` and
/// `offsets` continue to hold its unchanged inputs. The vectors are swapped
/// only after every addition succeeds. An exceptional incomplete level can
/// therefore discard its staging and safely retry the same inputs with the
/// complete formulas.
///
/// # Invariants
///
/// - Every coordinate in `points` represents a valid, non-identity point on
///   the same short-Weierstrass curve with `a = 0`. The doubling numerator is
///   therefore `3x^2`, with no `+ a` term.
/// - `offsets` begins at zero, is non-decreasing, and ends at `points.len()`.
///   Its consecutive entries partition `points` into buckets.
///
/// The callers in this module establish these invariants by sourcing points
/// from a single Pasta curve and skipping identity inputs before building the
/// buckets. The function is generic over the field only for reuse between
/// [`crate::Fp`] and [`crate::Fq`].
fn reduce_affine_buckets<F: Field>(
    points: Vec<AffinePoint<F>>,
    offsets: Vec<usize>,
) -> Option<Vec<Option<AffinePoint<F>>>> {
    reduce_affine_buckets_inner::<F, false>(points, offsets)
}

/// Destructively compacts every incomplete affine reduction level into its
/// input buffer. This is for callers that can reconstruct the original points
/// if a zero denominator declines the incomplete formulas.
#[cfg(any(test, feature = "multicore", feature = "orbits"))]
// The multicore-only caller is enabled by the dependent no-orbits backend.
#[cfg_attr(all(feature = "multicore", not(feature = "orbits")), allow(dead_code))]
fn reduce_affine_buckets_in_place<F: Field>(
    mut points: Vec<AffinePoint<F>>,
    mut offsets: Vec<usize>,
) -> Option<Vec<Option<AffinePoint<F>>>> {
    debug_assert!(!offsets.is_empty());
    let bucket_count = offsets.len() - 1;
    let mut next_offsets = Vec::with_capacity(offsets.len());
    let mut pending = Vec::with_capacity(points.len() / 2);

    while offsets.windows(2).any(|range| range[1] - range[0] > 1) {
        next_offsets.clear();
        pending.clear();
        next_offsets.push(0);
        let mut output = 0;

        for range in offsets.windows(2) {
            let mut input = range[0];
            while input + 1 < range[1] {
                let left = points[input];
                let right = points[input + 1];
                points[output] = left;
                pending.push(PendingAffineAddition {
                    output,
                    x_sum: left.x + right.x,
                    numerator: right.y - left.y,
                    denominator: right.x - left.x,
                    inversion_scratch: F::ZERO,
                });
                input += 2;
                output += 1;
            }
            if input < range[1] {
                points[output] = points[input];
                output += 1;
            }
            next_offsets.push(output);
        }

        batch_invert_and_add(&mut pending, &mut points)?;
        points.truncate(output);
        core::mem::swap(&mut offsets, &mut next_offsets);
    }

    let mut buckets = alloc::vec![None; bucket_count];
    for (bucket, range) in buckets.iter_mut().zip(offsets.windows(2)) {
        if range[0] != range[1] {
            debug_assert_eq!(range[1] - range[0], 1);
            *bucket = Some(points[range[0]]);
        }
    }
    Some(buckets)
}

fn reduce_affine_buckets_inner<F: Field, const COMPLETE: bool>(
    mut points: Vec<AffinePoint<F>>,
    mut offsets: Vec<usize>,
) -> Option<Vec<Option<AffinePoint<F>>>> {
    debug_assert!(!offsets.is_empty());
    let bucket_count = offsets.len() - 1;
    let mut next_points = Vec::with_capacity((points.len() + bucket_count) / 2);
    let mut next_offsets = Vec::with_capacity(offsets.len());
    let mut pending = Vec::with_capacity(points.len() / 2);

    while offsets.windows(2).any(|range| range[1] - range[0] > 1) {
        next_points.clear();
        next_offsets.clear();
        pending.clear();
        next_offsets.push(0);

        for range in offsets.windows(2) {
            let bucket = &points[range[0]..range[1]];
            for pair in bucket.chunks_exact(2) {
                let left = pair[0];
                let right = pair[1];

                let dx = right.x - left.x;
                let (numerator, denominator) = if COMPLETE && dx.is_zero_vartime() {
                    // Valid curve points with the same x-coordinate have the
                    // same or opposite y-coordinate. Handle both branches
                    // before asking the batch inverter to divide.
                    if !(right.y - left.y).is_zero_vartime() || left.y.is_zero_vartime() {
                        // The points are inverses, or this is a point of order
                        // two. Their sum is the identity, which is omitted.
                        continue;
                    }
                    let x_squared = left.x.square();
                    (x_squared.double() + x_squared, left.y.double())
                } else {
                    (right.y - left.y, dx)
                };

                let output = next_points.len();
                // Preserve the left input in its result slot until the batch
                // inversion completes. This avoids duplicating its coordinates
                // in every pending addition.
                next_points.push(left);
                pending.push(PendingAffineAddition {
                    output,
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

        if batch_invert_and_add(&mut pending, &mut next_points).is_none() {
            if !COMPLETE {
                // At least one incomplete chord had equal x-coordinates. The
                // failed batch has not overwritten any staged point, and the
                // source vectors are not swapped until success, so `points`
                // and `offsets` are still the exact inputs to this level.
                // Retry them and keep complete formulas enabled for every
                // remaining level; this prevents a later exceptional pair
                // from entering an incomplete formula too.
                return reduce_affine_buckets_inner::<F, true>(points, offsets);
            }
            // Complete formulas cannot produce a zero denominator under the
            // invariants above. If the guard nevertheless fails, propagate
            // `None` so the verifier caller uses the generic MSM instead of a
            // potentially incomplete result.
            return None;
        }

        core::mem::swap(&mut points, &mut next_points);
        core::mem::swap(&mut offsets, &mut next_offsets);
    }

    let mut buckets = alloc::vec![None; bucket_count];
    for (bucket, range) in buckets.iter_mut().zip(offsets.windows(2)) {
        if range[0] != range[1] {
            debug_assert_eq!(range[1] - range[0], 1);
            *bucket = Some(points[range[0]]);
        }
    }
    Some(buckets)
}

fn sum_buckets<C: GlvParams>(buckets: &[Option<AffinePoint<C::Base>>]) -> C {
    let mut running = C::identity();
    let mut sum = C::identity();
    for bucket in buckets.iter().rev() {
        if let Some(point) = bucket {
            running += C::affine_unchecked(point.x, point.y, private::CrateToken(()));
        }
        sum += running;
    }
    sum
}

fn fill_window<C: GlvParams>(
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[MultiexpBase<C::Base>],
    window_bits: usize,
    window: usize,
) -> Option<Vec<Option<AffinePoint<C::Base>>>> {
    let bucket_count = 1 << (window_bits - 1);
    let (assignments, counts) = window_assignments::<C>(components, bases, window_bits, window);

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
    for assignment in assignments {
        let base_index = assignment.component / 2;
        let base = bases[base_index];
        let x = if assignment.component & 1 == 0 {
            base.x
        } else {
            base.endo_x
        };
        let bucket = assignment.bucket();
        let position = positions[bucket];
        points[position] = AffinePoint {
            x,
            y: if assignment.negative() {
                -base.y
            } else {
                base.y
            },
        };
        positions[bucket] += 1;
    }

    reduce_affine_buckets(points, offsets)
}

fn multiexp_serial<C: GlvParams>(
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[MultiexpBase<C::Base>],
    window_bits: usize,
) -> Option<C> {
    let window_count = GLV_COMPONENT_BITS / window_bits + 1;
    let mut acc = C::identity();

    for window in (0..window_count).rev() {
        if window + 1 != window_count {
            for _ in 0..window_bits {
                acc = acc.double();
            }
        }

        let buckets = fill_window::<C>(components, bases, window_bits, window)?;
        acc += sum_buckets::<C>(&buckets);
    }
    Some(acc)
}

/// $\sum_{w < \text{windows}} B^w C_w$ for $C_w$ = `window_sum(w)`, with
/// windows combined through a balanced tree. Every window remains an
/// independent Rayon task. Each merge shifts only its upper subtree,
/// sharing the shift across all of that subtree's windows. This needs
/// O(windows log windows) doublings instead of independently shifting
/// every pair to its absolute position. `None` from
/// `window_sum` (an arithmetic guard) propagates out. Shared by the
/// Eisenstein-orbit backend and the prepared
/// zero-check's main-window and tail drivers.
#[cfg(feature = "multicore")]
fn balanced_windows_sum<C: GlvParams>(
    windows: usize,
    window_bits: usize,
    window_sum: impl Fn(usize) -> Option<C> + Sync,
) -> Option<C> {
    fn sum_range<C: GlvParams>(
        start: usize,
        windows: usize,
        window_bits: usize,
        window_sum: &(impl Fn(usize) -> Option<C> + Sync),
    ) -> Option<C> {
        match windows {
            0 => Some(C::identity()),
            1 => window_sum(start),
            _ => {
                let half = windows / 2;
                let (low, high) = maybe_rayon::join(
                    || sum_range(start, half, window_bits, window_sum),
                    || sum_range(start + half, windows - half, window_bits, window_sum),
                );
                let mut high = high?;
                for _ in 0..window_bits * half {
                    high = high.double();
                }
                Some(low? + high)
            }
        }
    }

    sum_range(0, windows, window_bits, &window_sum)
}

/// Evaluates each Signed-Booth window independently through Rayon, then
/// combines the ordered sums with one Horner fold. This keeps the expensive
/// window reductions parallel without duplicating the shift chain.
#[cfg(feature = "multicore")]
fn parallel_windows_sum<C: GlvParams>(
    windows: usize,
    window_bits: usize,
    window_sum: impl Fn(usize) -> Option<C> + Sync,
) -> Option<C> {
    let window_sums: Option<Vec<C>> = (0..windows).into_par_iter().map(&window_sum).collect();
    let window_sums = window_sums?;
    let mut acc = C::identity();
    for (window, sum) in window_sums.into_iter().enumerate().rev() {
        if window + 1 != windows {
            for _ in 0..window_bits {
                acc = acc.double();
            }
        }
        acc += sum;
    }
    Some(acc)
}

#[cfg(feature = "multicore")]
fn multiexp_parallel<C: GlvParams>(
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[MultiexpBase<C::Base>],
    window_bits: usize,
) -> Option<C> {
    let window_count = GLV_COMPONENT_BITS / window_bits + 1;
    parallel_windows_sum::<C>(window_count, window_bits, |window| {
        let buckets = fill_window::<C>(components, bases, window_bits, window)?;
        Some(sum_buckets::<C>(&buckets))
    })
}

fn multiexp<C: GlvParams>(
    components: &[(SignedMagnitude, SignedMagnitude)],
    bases: &[MultiexpBase<C::Base>],
    window_bits: usize,
    num_threads: usize,
) -> Option<C> {
    debug_assert_eq!(components.len(), bases.len());

    #[cfg(not(feature = "multicore"))]
    let _ = num_threads;
    #[cfg(feature = "multicore")]
    let acc = if num_threads > 1 {
        multiexp_parallel::<C>(components, bases, window_bits)
    } else {
        multiexp_serial::<C>(components, bases, window_bits)
    };
    #[cfg(not(feature = "multicore"))]
    let acc = multiexp_serial::<C>(components, bases, window_bits);
    acc
}

fn multiexp_bases<C: GlvParams>(bases: &[C::AffineExt]) -> Vec<MultiexpBase<C::Base>> {
    bases
        .iter()
        .map(|base| {
            let (x, y) = C::affine_xy(base);
            MultiexpBase {
                x,
                endo_x: x * C::Base::ZETA,
                y,
                identity: bool::from(base.is_identity()),
            }
        })
        .collect()
}

/// Attempts a GLV bucket multiscalar multiplication for a large Pasta MSM,
/// through whichever backend `plan_multiexp` selects (with the `orbits`
/// feature disabled, the Signed-Booth backend at
/// `glv_multiexp_window_bits`'s width).
///
/// Returns `None` when the cost model selects the generic MSM or when an
/// internal arithmetic guard fails, allowing verifier callers to use the
/// generic implementation instead of panicking.
pub(crate) fn try_multiexp<C: GlvParams>(
    scalars: &[C::ScalarExt],
    bases: &[C::AffineExt],
) -> Option<C> {
    assert_eq!(scalars.len(), bases.len());
    let num_threads = current_num_threads();
    if let Some(result) = planned_strauss_multiexp::<C>(scalars, bases, num_threads) {
        return Some(result);
    }

    #[cfg(feature = "orbits")]
    {
        if scalars.len() < MIN_GLV_MULTIEXP_TERMS {
            return None;
        }

        // Decompose before planning: both backends consume the components,
        // and the planner prices them by their actual magnitudes.
        let components = scalars
            .iter()
            .map(decompose::<C>)
            .map(checked_signed_magnitudes)
            .collect::<Option<Vec<_>>>()?;
        let profile = MagnitudeProfile::new(&components);
        let plan = plan_multiexp::<C>(&profile, num_threads)?;
        match plan {
            MultiexpPlan::Booth { window_bits } => {
                let bases = multiexp_bases::<C>(bases);
                multiexp(&components, &bases, window_bits, num_threads)
            }
            MultiexpPlan::Orbit { window_bits } => {
                orbit::multiexp::<C>(&components, bases, window_bits, num_threads)
            }
        }
    }

    #[cfg(not(feature = "orbits"))]
    {
        let window_bits = glv_multiexp_window_bits::<C>(scalars.len(), num_threads)?;
        let components = scalars
            .iter()
            .map(decompose::<C>)
            .map(checked_signed_magnitudes)
            .collect::<Option<Vec<_>>>()?;
        let bases = multiexp_bases::<C>(bases);
        multiexp(&components, &bases, window_bits, num_threads)
    }
}

/// The GLV digit window for one base point: the eight Eisenstein orbit
/// representatives $[\Delta_i]P$ in affine coordinates, with each
/// x-coordinate stored in all three $\zeta$-rotations (so applying the
/// endomorphism part of a digit is a lookup, not a multiplication) alongside
/// the shared y-coordinates. 1 KiB per table.
///
/// Build one with [`Table::new`], or many with batched affine additions via
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

    /// Builds [`Table`]s for a batch of points. Large batches use affine
    /// addition layers that share one inversion across their non-identity
    /// inputs, avoiding the seven full projective additions used by
    /// [`Table::new`]. Small batches retain the projective construction.
    ///
    /// Identity inputs produce identity tables and may be mixed with
    /// non-identity points in the same batch.
    pub fn batch(points: &[C]) -> Vec<Table<C>> {
        let n = points.len();
        if n == 0 {
            return Vec::new();
        }
        if n < TABLE_BATCH_AFFINE_MIN_POINTS {
            return Self::batch_projective(points);
        }

        let mut live_indices = Vec::with_capacity(n);
        let mut live_points = Vec::with_capacity(n);
        for (i, point) in points.iter().enumerate() {
            if !bool::from(point.is_identity()) {
                live_indices.push(i);
                live_points.push(*point);
            }
        }
        if live_points.is_empty() {
            let identity_window = [C::AffineExt::identity(); 8];
            return alloc::vec![Self::from_window(&identity_window); n];
        }
        if live_points.len() < TABLE_BATCH_AFFINE_MIN_POINTS {
            return Self::batch_projective(points);
        }

        // Normalize the live inputs once, then keep the complete window chain
        // in affine form. Identity lanes are omitted because affine chord
        // formulas do not handle them; their output tables stay identities.
        let identity_window = [C::AffineExt::identity(); 8];
        let mut tables = alloc::vec![Self::from_window(&identity_window); n];
        let mut p = alloc::vec![C::AffineExt::identity(); live_points.len()];
        C::batch_normalize(&live_points, &mut p);

        let len = p.len();
        let phi_p: Vec<_> = p.iter().map(Self::affine_endo).collect();
        let mut spare = alloc::vec![C::AffineExt::identity(); len];
        let mut d1 = alloc::vec![C::AffineExt::identity(); len];
        let mut scratch = AffineTwiddleScratch::new();
        let mut identity_free = true;

        identity_free =
            affine_add_sub_pairs::<C>(&p, &phi_p, &mut spare, &mut d1, &mut scratch, identity_free);
        let d1_endo: Vec<_> = d1.iter().map(Self::affine_endo).collect();
        let mut b = alloc::vec![C::AffineExt::identity(); len];
        identity_free = affine_add_sub_pairs::<C>(
            &d1,
            &d1_endo,
            &mut spare,
            &mut b,
            &mut scratch,
            identity_free,
        );

        let b_endo: Vec<_> = b.iter().map(Self::affine_endo).collect();
        let m3: Vec<_> = b_endo.iter().map(Self::affine_endo).collect();
        let mut t3a = alloc::vec![C::AffineExt::identity(); len];
        let mut t3b = alloc::vec![C::AffineExt::identity(); len];
        identity_free =
            affine_add_sub_pairs::<C>(&phi_p, &m3, &mut t3a, &mut t3b, &mut scratch, identity_free);

        let r3: Vec<_> = b_endo.iter().map(|point| -*point).collect();
        let mut t4a = alloc::vec![C::AffineExt::identity(); len];
        let mut t4b = alloc::vec![C::AffineExt::identity(); len];
        identity_free =
            affine_add_sub_pairs::<C>(&phi_p, &r3, &mut t4a, &mut t4b, &mut scratch, identity_free);

        let mut t19 = alloc::vec![C::AffineExt::identity(); len];
        affine_add_sub_pairs::<C>(
            &phi_p,
            &t4b,
            &mut t19,
            &mut spare,
            &mut scratch,
            identity_free,
        );

        for (lane, table_index) in live_indices.into_iter().enumerate() {
            let window = [
                p[lane],
                d1[lane],
                Self::affine_endo(&t4a[lane]),
                -Self::affine_endo(&t3b[lane]),
                -m3[lane],
                -t3a[lane],
                Self::affine_endo(&Self::affine_endo(&t4b[lane])),
                Self::affine_endo(&Self::affine_endo(&t19[lane])),
            ];
            tables[table_index] = Self::from_window(&window);
        }
        tables
    }

    fn batch_projective(points: &[C]) -> Vec<Table<C>> {
        let mut projective = Vec::with_capacity(points.len() * 8);
        for point in points {
            projective.extend_from_slice(&Self::window_proj(point));
        }
        let mut affine = alloc::vec![C::AffineExt::identity(); projective.len()];
        C::batch_normalize(&projective, &mut affine);
        affine.chunks_exact(8).map(Self::from_window).collect()
    }

    #[inline(always)]
    fn affine_endo(p: &C::AffineExt) -> C::AffineExt {
        let (x, y) = C::affine_xy(p);
        C::affine_unchecked(x * C::Base::ZETA, y, private::CrateToken(()))
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
        WindowCoords::window_digit_coords(self, code)
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
    /// Montgomery's trick and each nonzero-digit column is a fused affine
    /// $2P + D$. Otherwise every table falls back to its own per-point
    /// ladder.
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
    fn batch_affine_ladder(live: &[&Self], k: &Decomposed<C>) -> Vec<C::AffineExt> {
        let (xs, ys) = batch_affine_ladder_raw(live, k);
        xs.into_iter()
            .zip(ys)
            .map(|(x, y)| C::affine_unchecked(x, y, private::CrateToken(())))
            .collect()
    }

    /// Multiplies one scalar by a contiguous batch of points, returning
    /// affine results.
    ///
    /// Large identity-free batches with a safe schedule build *effective*
    /// tables (no inversion, no `8n`-entry table normalization), run the
    /// ladder kernel, and batch-normalize only the `n` final products;
    /// everything else takes the normalized route.
    fn mul_decomposed_same_scalar_affine(
        points: &[C],
        scalar: &Decomposed<C>,
    ) -> Vec<C::AffineExt> {
        if points.is_empty() {
            return Vec::new();
        }

        let use_affine = points.len() >= BATCH_AFFINE_MIN_POINTS
            && points.iter().all(|point| !bool::from(point.is_identity()))
            && scalar.len > 0
            && scalar.affine_ladder_safe;
        if !use_affine {
            return Self::mul_decomposed_same_scalar_affine_normalized(points, scalar);
        }

        let tables = EffectiveTable::batch(points);
        let refs: Vec<&EffectiveTable<C>> = tables.iter().collect();
        let (xs, ys) = batch_affine_ladder_raw(&refs, scalar);
        restore_and_normalize(xs, ys, &tables)
    }

    /// The normalized same-scalar route: batched affine table construction,
    /// then the affine ladder (which needs no output conversion) or, off the
    /// gate, per-table ladders plus one output normalization. Retained as the
    /// sub-gate fallback and as the forced benchmark backend.
    fn mul_decomposed_same_scalar_affine_normalized(
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
    /// inversions are batched even though each point has a different
    /// scalar. Routed like [`Table::mul_decomposed_same_scalar_affine`].
    fn mul_decomposed_pairs_affine(points: &[C], scalars: &[&Decomposed<C>]) -> Vec<C::AffineExt> {
        assert_eq!(points.len(), scalars.len());
        if points.is_empty() {
            return Vec::new();
        }

        let use_affine = points.len() >= BATCH_AFFINE_MIN_POINTS
            && points.iter().all(|point| !bool::from(point.is_identity()))
            && scalars
                .iter()
                .all(|scalar| scalar.len > 0 && scalar.affine_ladder_safe);
        if !use_affine {
            return Self::mul_decomposed_pairs_affine_normalized(points, scalars);
        }

        let tables = EffectiveTable::batch(points);
        let (xs, ys) = batch_affine_ladder_pairs_raw(&tables, scalars);
        restore_and_normalize(xs, ys, &tables)
    }

    /// The normalized pairs route (see
    /// [`Table::mul_decomposed_same_scalar_affine_normalized`]).
    fn mul_decomposed_pairs_affine_normalized(
        points: &[C],
        scalars: &[&Decomposed<C>],
    ) -> Vec<C::AffineExt> {
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

        let (xs, ys) = batch_affine_ladder_pairs_raw(&tables, scalars);
        xs.into_iter()
            .zip(ys)
            .map(|(x, y)| C::affine_unchecked(x, y, private::CrateToken(())))
            .collect()
    }
}

/// Synchronized affine Eisenstein ladders with one independently recoded
/// scalar per window. Shorter recodings join when their top digit is
/// reached; all live accumulators share each column's inversions. Like
/// [`batch_affine_ladder_raw`], this is the raw kernel: callers finalize
/// the returned accumulator coordinates for their window representation.
fn batch_affine_ladder_pairs_raw<C: GlvParams, W: WindowCoords<C>>(
    tables: &[W],
    scalars: &[&Decomposed<C>],
) -> (Vec<C::Base>, Vec<C::Base>) {
    let n = tables.len();
    let max_len = scalars.iter().map(|scalar| scalar.len).max().unwrap_or(0);
    let mut xs = alloc::vec![C::Base::ZERO; n];
    let mut ys = alloc::vec![C::Base::ZERO; n];
    let mut started = alloc::vec![false; n];
    let mut slopes = alloc::vec![C::Base::ZERO; n];
    let mut x1s = alloc::vec![C::Base::ZERO; n];
    let mut denominators = Vec::with_capacity(n);
    let mut scratch = Vec::with_capacity(n);
    let mut operations = Vec::with_capacity(n);
    let mut additions = Vec::with_capacity(n);

    for position in (0..max_len).rev() {
        denominators.clear();
        operations.clear();
        for (i, (table, scalar)) in tables.iter().zip(scalars).enumerate() {
            if position >= scalar.len {
                continue;
            }
            let code = scalar.digits[position];
            if !started[i] {
                debug_assert_eq!(position + 1, scalar.len);
                debug_assert_ne!(code, 0);
                (xs[i], ys[i]) = table.window_digit_coords(code);
                started[i] = true;
            } else {
                let denominator = if code == 0 {
                    ys[i].double()
                } else {
                    let (orbit, e, _) = decode_digit(code);
                    table.window_xs()[e][orbit] - xs[i]
                };
                operations.push((i, code));
                denominators.push(denominator);
            }
        }

        scratch.resize(denominators.len(), C::Base::ZERO);
        if !denominators.is_empty() {
            batch_invert_nonzero(&mut denominators, &mut scratch);
        }

        additions.clear();
        let mut second_denominators = Vec::with_capacity(operations.len());
        for ((i, code), inverse) in operations.iter().copied().zip(&denominators) {
            if code == 0 {
                let xx = xs[i].square();
                let slope = (xx.double() + xx) * inverse;
                let x2 = slope.square() - xs[i].double();
                ys[i] = slope * (xs[i] - x2) - ys[i];
                xs[i] = x2;
            } else {
                let (orbit, e, negate) = decode_digit(code);
                let u = tables[i].window_xs()[e][orbit];
                let v = if negate {
                    -tables[i].window_ys()[orbit]
                } else {
                    tables[i].window_ys()[orbit]
                };
                let slope = (v - ys[i]) * inverse;
                x1s[i] = slope.square() - xs[i] - u;
                slopes[i] = slope;
                additions.push(i);
                second_denominators.push(x1s[i] - xs[i]);
            }
        }

        scratch.resize(second_denominators.len(), C::Base::ZERO);
        if !second_denominators.is_empty() {
            batch_invert_nonzero(&mut second_denominators, &mut scratch);
        }
        for (i, inverse) in additions.iter().copied().zip(second_denominators) {
            let slope = -(slopes[i] + ys[i].double() * inverse);
            let x2 = slope.square() - xs[i] - x1s[i];
            ys[i] = slope * (xs[i] - x2) - ys[i];
            xs[i] = x2;
        }
    }

    debug_assert!(started.iter().all(|started| *started));
    (xs, ys)
}

/// Raw digit-window coordinate access shared by [`Table`] and
/// [`EffectiveTable`]: the batch-affine ladder kernel
/// ([`batch_affine_ladder_raw`]) is generic over it, since the two
/// representations differ only in how results leave the ladder
/// (`affine_unchecked` versus omitted-denominator restoration).
trait WindowCoords<C: GlvParams> {
    /// `xs[e][i]` = $\zeta^e \cdot x([\Delta_i]P)$ in the window's
    /// coordinate system.
    fn window_xs(&self) -> &[[C::Base; 8]; 3];

    /// `ys[i]` = $y([\Delta_i]P)$ in the window's coordinate system.
    fn window_ys(&self) -> &[C::Base; 8];

    /// The raw coordinates contributed by a nonzero digit:
    /// $\pm\phi^e([\Delta_i]P)$, one lookup and at most one negation.
    fn window_digit_coords(&self, code: u8) -> (C::Base, C::Base) {
        let (orbit, e, negate) = decode_digit(code);
        let x = self.window_xs()[e][orbit];
        let y = if negate {
            -self.window_ys()[orbit]
        } else {
            self.window_ys()[orbit]
        };
        (x, y)
    }
}

impl<C: GlvParams> WindowCoords<C> for Table<C> {
    fn window_xs(&self) -> &[[C::Base; 8]; 3] {
        &self.xs
    }

    fn window_ys(&self) -> &[C::Base; 8] {
        &self.ys
    }
}

impl<C: GlvParams> WindowCoords<C> for EffectiveTable<C> {
    fn window_xs(&self) -> &[[C::Base; 8]; 3] {
        &self.xs
    }

    fn window_ys(&self) -> &[C::Base; 8] {
        &self.ys
    }
}

/// The synchronized batch-affine ladder kernel over raw window
/// coordinates, returning the raw accumulator coordinates; the callers
/// finalize ([`Table::batch_affine_ladder`] into affine points of the
/// original curve, [`effective_batch_affine_ladder`] into projective
/// points by restoring each lane's omitted denominator — with effective
/// windows the accumulators live on per-lane effective curves, which mix
/// freely here because the a = 0 affine formulas never read the curve
/// constant and lanes only share the batched inversions).
///
/// Callers guarantee: `k.len > 0`, every window is non-identity, and the
/// schedule passed [`affine_ladder_safe`] (so no denominator below is
/// zero and no accumulator is ever the identity).
#[allow(clippy::needless_range_loop)]
fn batch_affine_ladder_raw<C: GlvParams, W: WindowCoords<C>>(
    live: &[&W],
    k: &Decomposed<C>,
) -> (Vec<C::Base>, Vec<C::Base>) {
    let n = live.len();
    // Affine accumulators (structure-of-arrays), initialized from the
    // top digit — the ladder's first column is the digit itself.
    let mut xs = Vec::with_capacity(n);
    let mut ys = Vec::with_capacity(n);
    for t in live {
        let (x, y) = t.window_digit_coords(k.digits[k.len - 1]);
        xs.push(x);
        ys.push(y);
    }
    let mut den = alloc::vec![C::Base::ZERO; n];
    let mut scratch = alloc::vec![C::Base::ZERO; n];
    let mut slopes = alloc::vec![C::Base::ZERO; n];
    let mut x1s = alloc::vec![C::Base::ZERO; n];

    for &code in k.digits[..k.len - 1].iter().rev() {
        if code == 0 {
            // Batched affine doubling: m = 3x²/(2y), x' = m² - 2x,
            // y' = m(x - x') - y. Asymptotically 5M + 2S per point
            // (2M + 2S here, 3M inside the shared inversion).
            for (den, y) in den.iter_mut().zip(&ys) {
                *den = y.double();
            }
            batch_invert_nonzero(&mut den, &mut scratch);
            for i in 0..n {
                let xx = xs[i].square();
                let m = (xx.double() + xx) * den[i];
                let x2 = m.square() - xs[i].double();
                ys[i] = m * (xs[i] - x2) - ys[i];
                xs[i] = x2;
            }
        } else {
            let (orbit, e, negate) = decode_digit(code);
            // Fused affine 2P + D (Eisenträger–Lauter–Montgomery): the
            // y-coordinate of the intermediate P + D is never
            // materialized. Asymptotically 9M + 2S per point, versus
            // 10M + 3S for a separate doubling and addition.
            //
            // Phase 1: s = (v - y)/(u - x), x1 = x(P + D) = s² - x - u.
            for (den, (x, t)) in den.iter_mut().zip(xs.iter().zip(live)) {
                *den = t.window_xs()[e][orbit] - x;
            }
            batch_invert_nonzero(&mut den, &mut scratch);
            for i in 0..n {
                let u = live[i].window_xs()[e][orbit];
                let v = if negate {
                    -live[i].window_ys()[orbit]
                } else {
                    live[i].window_ys()[orbit]
                };
                let s = (v - ys[i]) * den[i];
                x1s[i] = s.square() - xs[i] - u;
                slopes[i] = s;
            }
            // Phase 2: t = -s - 2y/(x1 - x), x2 = t² - x - x1,
            // y2 = t(x - x2) - y.
            for (den, (x, x1)) in den.iter_mut().zip(xs.iter().zip(&x1s)) {
                *den = *x1 - x;
            }
            batch_invert_nonzero(&mut den, &mut scratch);
            for i in 0..n {
                let t = -(slopes[i] + ys[i].double() * den[i]);
                let x2 = t.square() - xs[i] - x1s[i];
                ys[i] = t * (xs[i] - x2) - ys[i];
                xs[i] = x2;
            }
        }
    }

    (xs, ys)
}

/// The effective-affine counterpart of [`Table`]: the same eight-orbit
/// digit window, but over raw coordinates sharing one *omitted* Jacobian
/// denominator `z` relative to the original curve — every entry satisfies
/// $y_i^2 = x_i^3 + bz^6$, equivalently $(x_i, y_i, z)$ is the ordinary
/// projective orbit point. Building one costs a projective doubling, an
/// isomorphism map, seven incomplete mixed additions, and one backward
/// ratio pass — no inversion, unlike [`Table::batch`].
///
/// The batch-affine ladder consumes these directly; results return to the
/// original curve through [`private::Sealed::projective_unchecked`], never
/// through `affine_unchecked` — effective coordinates are *not* points of
/// the original curve until the denominator is restored.
#[derive(Clone, Copy, Debug)]
struct EffectiveTable<C: GlvParams> {
    /// `xs[e][i]` = $\zeta^e \cdot x_{\text{eff}}([\Delta_i]P)$.
    xs: [[C::Base; 8]; 3],
    /// `ys[i]` = $y_{\text{eff}}([\Delta_i]P)$.
    ys: [C::Base; 8],
    /// The common omitted Jacobian denominator relative to the original
    /// curve; zero iff the table represents the identity (whose window is
    /// all-zero).
    z: C::Base,
}

impl<C: GlvParams> EffectiveTable<C> {
    /// Builds the window for a single point with no inversion, from any
    /// projective representation (`Z != 1` included). Identity inputs
    /// produce the all-zero table with `z = 0`.
    fn new(p: &C) -> Self {
        if bool::from(p.is_identity()) {
            return EffectiveTable {
                xs: [[C::Base::ZERO; 8]; 3],
                ys: [C::Base::ZERO; 8],
                z: C::Base::ZERO,
            };
        }
        // D = 2P is nonidentity (odd prime order), so c = Z(D) != 0. On
        // the effective curve y² = x³ + b·c⁶, D is affine as it stands,
        // and P maps to (c²·X_P, c³·Y_P, Z_P).
        let (dx, dy, c) = p.double().jacobian_coordinates();
        let d = EffectiveAffine { x: dx, y: dy };
        let (px, py, pz) = p.jacobian_coordinates();
        let c2 = c.square();
        let mut q = RawJacobian {
            x: px * c2,
            y: py * (c2 * c),
            z: pz,
        };

        // The fixed chain: seven incomplete mixed additions by D, each
        // followed by a unit (nonexceptional by the chain derivation),
        // recording the Z-ratios for the backward global-Z pass.
        let mut path = [q; 8];
        let mut ratios = [C::Base::ONE; 7];
        for (&unit, (ratio, stored)) in EFFECTIVE_CHAIN_UNITS
            .iter()
            .zip(ratios.iter_mut().zip(path[1..].iter_mut()))
        {
            let (sum, zr) = add_mixed_with_ratio_nonexceptional(&q, &d);
            q = apply_chain_unit(sum, unit);
            *ratio = zr;
            *stored = q;
        }
        let global = path[7].z;
        globalize_z(&mut path, &ratios);

        // Scatter the path into canonical orbit slots: for
        // q_i = ±ω^r·Δ_slot, xs[e][slot] = ζ^((e - r) mod 3)·x(q_i) and
        // ys[slot] = ±y(q_i) — one ζ multiplication per entry, exactly as
        // in [`Table::from_window`].
        let mut xs = [[C::Base::ZERO; 8]; 3];
        let mut ys = [C::Base::ZERO; 8];
        for (q, &(slot, rotation, negate)) in path.iter().zip(&EFFECTIVE_CHAIN_RELATIONS) {
            let xz = q.x * C::Base::ZETA;
            let rotations = [q.x, xz, -q.x - xz];
            let (slot, rotation) = (usize::from(slot), usize::from(rotation));
            xs[0][slot] = rotations[(3 - rotation) % 3];
            xs[1][slot] = rotations[(4 - rotation) % 3];
            xs[2][slot] = rotations[(5 - rotation) % 3];
            ys[slot] = if negate { -q.y } else { q.y };
        }
        EffectiveTable {
            xs,
            ys,
            z: c * global,
        }
    }

    /// Effective tables for a batch of points. Unlike [`Table::batch`], each
    /// table is built independently without batched inversions.
    fn batch(points: &[C]) -> Vec<EffectiveTable<C>> {
        points.iter().map(Self::new).collect()
    }

    /// Whether this is the table of the identity point.
    fn is_identity(&self) -> bool {
        self.z.is_zero().into()
    }
}

/// The batch-affine ladder over effective tables: one projective product
/// per live table, restoring each lane's omitted denominator into the
/// final Z with no inversion and no normalization. Caller guarantees are
/// those of [`batch_affine_ladder_raw`].
fn effective_batch_affine_ladder<C: GlvParams>(
    live: &[&EffectiveTable<C>],
    k: &Decomposed<C>,
) -> Vec<C> {
    let (xs, ys) = batch_affine_ladder_raw(live, k);
    xs.into_iter()
        .zip(ys)
        .zip(live)
        .map(|((x, y), t)| C::projective_unchecked(x, y, t.z, private::CrateToken(())))
        .collect()
}

/// Restores each ladder lane's omitted denominator into an ordinary
/// projective point and batch-normalizes the `n` final products — the
/// effective FFT route's only normalization, versus the `8n` table
/// entries the normalized route converts up front.
fn restore_and_normalize<C: GlvParams>(
    xs: Vec<C::Base>,
    ys: Vec<C::Base>,
    tables: &[EffectiveTable<C>],
) -> Vec<C::AffineExt> {
    let projective: Vec<C> = xs
        .into_iter()
        .zip(ys)
        .zip(tables)
        .map(|((x, y), t)| C::projective_unchecked(x, y, t.z, private::CrateToken(())))
        .collect();
    let mut affine = alloc::vec![C::AffineExt::identity(); projective.len()];
    C::batch_normalize(&projective, &mut affine);
    affine
}

/// Serves a same-scalar batch through the effective-affine sidecar when
/// the batch-affine ladder's own gate is met — at least
/// [`BATCH_AFFINE_MIN_POINTS`] live points and a safe column schedule —
/// writing the products over the input points in `output` and leaving
/// identity lanes untouched (`k·O = O`). Returns `false`, with `output`
/// unmodified, when the gate is not met.
///
/// Compared with the normalized route this builds each live point's
/// window with no inversion and no `8n`-entry normalization, runs the
/// same ladder kernel, and restores each lane's omitted denominator
/// directly into the projective output.
fn try_batch_mul_same_scalar_effective<C: GlvParams>(k: &Decomposed<C>, output: &mut [C]) -> bool {
    if k.len == 0 || !k.affine_ladder_safe {
        return false;
    }
    let live = |p: &&C| !bool::from(p.is_identity());
    if output.iter().filter(live).count() < BATCH_AFFINE_MIN_POINTS {
        return false;
    }
    let tables: Vec<EffectiveTable<C>> = output
        .iter()
        .filter(live)
        .map(EffectiveTable::new)
        .collect();
    let refs: Vec<&EffectiveTable<C>> = tables.iter().collect();
    let mut products = effective_batch_affine_ladder(&refs, k).into_iter();
    for lane in output.iter_mut() {
        if !bool::from(lane.is_identity()) {
            *lane = products.next().expect("one product per live lane");
        }
    }
    debug_assert!(products.next().is_none());
    true
}

/// The GLV implementation behind `CurveExt::batch_mul_same_scalar_vartime`
/// (see `impl_batch_mul_same_scalar_vartime!` in `curves.rs`): multiplies
/// every point in `output` by `k`, in place. Batches that would run the
/// batch-affine ladder take the effective-affine sidecar; everything else
/// (small or exceptional-schedule batches, `k = 0`) takes the normalized
/// tables and [`Table::mul_decomposed_batch`], whose own gate then falls
/// back to per-point ladders.
pub(crate) fn batch_mul_same_scalar_in_place<C: GlvParams>(output: &mut [C], k: &C::ScalarExt) {
    let k = Decomposed::<C>::new(k);
    if try_batch_mul_same_scalar_effective(&k, output) {
        return;
    }
    batch_mul_same_scalar_normalized(output, &k);
}

/// The normalized same-scalar route: batched table build with one shared
/// normalization, then [`Table::mul_decomposed_batch`] (whose own gate
/// falls back to per-point ladders on small or exceptional batches).
fn batch_mul_same_scalar_normalized<C: GlvParams>(output: &mut [C], k: &Decomposed<C>) {
    let tables = Table::batch(output);
    let tables: Vec<&Table<C>> = tables.iter().collect();
    for (output, product) in output
        .iter_mut()
        .zip(Table::mul_decomposed_batch(&tables, k))
    {
        *output = product;
    }
}

/// Benchmark-only hooks for the effective-affine experiment: forced
/// construction and multiplication through each backend inside one build,
/// so comparisons cannot be confounded by unrelated codegen or dependency
/// differences (see `benches/glv_table.rs` and `benches/glv.rs`).
///
/// Hidden and unstable — not a public API.
#[doc(hidden)]
pub mod bench_internals {
    use super::*;

    /// Opaque handle over the crate-private effective table.
    #[derive(Clone, Copy, Debug)]
    pub struct BenchEffectiveTable<C: GlvParams>(EffectiveTable<C>);

    /// Forced effective-table construction for a batch of points.
    pub fn effective_table_batch<C: GlvParams>(points: &[C]) -> Vec<BenchEffectiveTable<C>> {
        EffectiveTable::batch(points)
            .into_iter()
            .map(BenchEffectiveTable)
            .collect()
    }

    /// Forced effective batch-affine ladder: one projective product per
    /// table.
    ///
    /// # Panics
    ///
    /// Panics if any table is the identity or the scalar's column schedule
    /// is not affine-ladder safe; benchmark inputs must satisfy both.
    pub fn effective_mul_decomposed_batch<C: GlvParams>(
        tables: &[BenchEffectiveTable<C>],
        k: &Decomposed<C>,
    ) -> Vec<C> {
        assert!(
            k.len > 0 && k.affine_ladder_safe,
            "benchmark schedule must be affine-ladder safe"
        );
        let live: Vec<&EffectiveTable<C>> = tables
            .iter()
            .map(|table| {
                assert!(!table.0.is_identity(), "benchmark tables must be live");
                &table.0
            })
            .collect();
        effective_batch_affine_ladder(&live, k)
    }

    /// The normalized (pre-sidecar) same-scalar route, forced.
    pub fn batch_mul_same_scalar_normalized<C: GlvParams>(output: &mut [C], k: &C::ScalarExt) {
        super::batch_mul_same_scalar_normalized(output, &Decomposed::new(k));
    }

    /// The effective-affine same-scalar sidecar, forced.
    ///
    /// # Panics
    ///
    /// Panics if the sidecar's gate declines the batch; benchmark inputs
    /// must be large, live, and affine-ladder safe.
    pub fn batch_mul_same_scalar_effective<C: GlvParams>(output: &mut [C], k: &C::ScalarExt) {
        assert!(
            super::try_batch_mul_same_scalar_effective(&Decomposed::new(k), output),
            "the sidecar gate declined this benchmark batch"
        );
    }

    /// The FFT same-scalar multiplication layer, forced through the
    /// normalized backend (8n-entry table normalization, ladder output
    /// used directly as affine).
    pub fn fft_mul_layer_normalized<C: GlvParams>(
        points: &[C],
        k: &Decomposed<C>,
    ) -> Vec<C::AffineExt> {
        Table::mul_decomposed_same_scalar_affine_normalized(points, k)
    }

    /// The FFT same-scalar multiplication layer as routed (on gate-met
    /// batches: effective tables, ladder, one n-point normalization).
    pub fn fft_mul_layer_routed<C: GlvParams>(
        points: &[C],
        k: &Decomposed<C>,
    ) -> Vec<C::AffineExt> {
        Table::mul_decomposed_same_scalar_affine(points, k)
    }
}

/// Raw affine coordinates on an *effective* curve $y^2 = x^3 + bZ^6$ for
/// some omitted Jacobian denominator $Z$ tracked by the caller. Deliberately
/// distinct from `C::AffineExt`, which asserts membership of the original
/// curve ($Z = 1$): never convert one into the other without restoring the
/// denominator.
#[derive(Clone, Copy, Debug)]
struct EffectiveAffine<F> {
    x: F,
    y: F,
}

/// Raw Jacobian coordinates, on an effective curve tracked by the caller.
/// `z` here is *relative* to that curve's omitted denominator: the point on
/// the original curve is $(x, y, Z_{\text{omitted}} \cdot z)$.
#[derive(Clone, Copy, Debug)]
struct RawJacobian<F> {
    x: F,
    y: F,
    z: F,
}

/// Incomplete mixed addition `q + d` on one effective curve (the a = 0
/// affine/Jacobian formulas never read the curve constant, so any common
/// omitted denominator works), returning the sum and the Z-*ratio*
/// `Z(sum)/Z(q) = 2H`: the sum's Z is computed as $Z_3 = Z_1 \cdot 2H$
/// (one multiplication instead of the squaring in `curves.rs`'s
/// $(Z_1 + H)^2 - Z_1^2 - H^2$), which is exactly what the backward
/// global-Z pass consumes. 8M + 3S.
///
/// Incomplete *by design*: the caller must guarantee `q` is nonidentity and
/// `x(q) != x(d)` (i.e. `q != ±d`) — for the table chain the
/// `effective_chain_derivation` test proves both for every step. Keep this
/// private and out of general group arithmetic.
fn add_mixed_with_ratio_nonexceptional<F: Field>(
    q: &RawJacobian<F>,
    d: &EffectiveAffine<F>,
) -> (RawJacobian<F>, F) {
    let z1z1 = q.z.square();
    let u2 = d.x * z1z1;
    let s2 = d.y * z1z1 * q.z;
    let h = u2 - q.x;
    let hh = h.square();
    let i = hh.double().double();
    let j = h * i;
    let r = (s2 - q.y).double();
    let v = q.x * i;
    let x3 = r.square() - j - v.double();
    let y3 = r * (v - x3) - (q.y * j).double();
    let zr = h.double();
    let z3 = q.z * zr;
    (
        RawJacobian {
            x: x3,
            y: y3,
            z: z3,
        },
        zr,
    )
}

/// Applies an Eisenstein unit (encoded as in [`JOINT_DIGITS`]: `unit >> 1`
/// the ζ-rotation exponent, `unit & 1` the negation) to raw Jacobian
/// coordinates: rotation multiplies x by $\zeta^e$ (with
/// $\zeta^2 x = -x - \zeta x$), negation flips y, and z never changes.
fn apply_chain_unit<F: WithSmallOrderMulGroup<3>>(
    mut p: RawJacobian<F>,
    unit: u8,
) -> RawJacobian<F> {
    match unit >> 1 {
        0 => {}
        1 => p.x *= F::ZETA,
        _ => {
            let xz = p.x * F::ZETA;
            p.x = -p.x - xz;
        }
    }
    if unit & 1 == 1 {
        p.y = -p.y;
    }
    p
}

/// Rescales every earlier chain point to the last one's Jacobian
/// denominator ("global Z"), inversion-free: given
/// `Z(path[i + 1]) = Z(path[i]) * ratios[i]`, walks backward maintaining
/// the cumulative product `s_i = Z(path.last())/Z(path[i])` and scales
/// $(x_i, y_i) \mapsto (s_i^2 x_i, s_i^3 y_i)$. The `z` fields are left
/// untouched (they become meaningless; the caller keeps only the shared
/// final denominator).
fn globalize_z<F: Field>(path: &mut [RawJacobian<F>], ratios: &[F]) {
    debug_assert_eq!(path.len(), ratios.len() + 1);
    let global = path[ratios.len()].z;
    let mut scale = F::ONE;
    for (p, ratio) in path.iter_mut().zip(ratios).rev() {
        scale *= *ratio;
        debug_assert_eq!(p.z * scale, global, "inconsistent chain ratios");
        let scale2 = scale.square();
        p.x *= scale2;
        p.y *= scale2 * scale;
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
/// `D = [d]B` is exceptional iff
///
/// - `d = ±s`: the first denominator `x(D) - x(P)` vanishes (this includes
///   `D = -P`, where `P + D` is the identity), or
/// - `d = -2s`: the second denominator `x(P + D) - x(P)` vanishes
///   (`D = -2P`), which is also exactly when the column's output would be
///   the identity.
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
            if d == s || d == -s || d == -s2 {
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
            "GLV half exceeds {GLV_COMPONENT_BITS} bits"
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

/// Deterministic input builders shared by this module's tests and the
/// [`orbit`] backend's tests.
#[cfg(test)]
pub(super) mod testutil {
    use super::GlvParams;
    use alloc::vec::Vec;
    use ff::{Field, PrimeField, WithSmallOrderMulGroup};

    /// Deterministic full-width scalars for known-answer tests.
    pub(crate) fn scalars<F: PrimeField>(n: u64) -> impl Iterator<Item = F> {
        (0..n).map(|i| {
            (F::from(0x9E37_79B9_7F4A_7C15u64 + i).square() + F::from(0x0123_4567_89AB_CDEFu64))
                .square()
                + F::from(i)
        })
    }

    /// Builds deterministic MSM inputs with known discrete logarithms.
    ///
    /// Each input includes identity, duplicate, and inverse bases, along with
    /// zero, unit, endomorphism, and dense scalars. This exercises the complete
    /// optimized MSM without computing the reference result through a second
    /// multiscalar-multiplication implementation.
    pub(crate) fn verifier_multiexp_inputs<C: GlvParams>(
        terms: usize,
    ) -> (Vec<C::ScalarExt>, Vec<C::AffineExt>, C) {
        let generator = C::generator();
        let identity = C::identity().to_affine();
        let positive = generator.to_affine();
        let negative = (-generator).to_affine();
        let mut next_point = generator;
        let mut next_weight = C::ScalarExt::ONE;
        let mut scalar_state = C::ScalarExt::from(0x6a09_e667_f3bc_c909);
        let mut expected_scalar = C::ScalarExt::ZERO;
        let mut scalars = Vec::with_capacity(terms);
        let mut bases = Vec::with_capacity(terms);

        for index in 0..terms {
            scalar_state =
                scalar_state.square() + C::ScalarExt::from(u64::try_from(index + 1).unwrap());
            let scalar = match index % 16 {
                0 => C::ScalarExt::ZERO,
                1 => C::ScalarExt::ONE,
                2 => -C::ScalarExt::ONE,
                3 => C::ScalarExt::ZETA,
                4 => -C::ScalarExt::ZETA,
                5 => -scalar_state,
                _ => scalar_state,
            };
            let (base, weight) = match index % 64 {
                0 => (identity, C::ScalarExt::ZERO),
                1 | 2 => (positive, C::ScalarExt::ONE),
                3 => (negative, -C::ScalarExt::ONE),
                _ => {
                    next_point += generator;
                    next_weight += C::ScalarExt::ONE;
                    (next_point.to_affine(), next_weight)
                }
            };

            expected_scalar += weight * scalar;
            scalars.push(scalar);
            bases.push(base);
        }

        (scalars, bases, generator * expected_scalar)
    }
}

#[cfg(test)]
mod tests {
    use super::testutil::{scalars, verifier_multiexp_inputs};
    use super::*;
    use crate::arithmetic::adc;
    use ff::Field;

    const VERIFIER_MULTIEXP_SIZES: [usize; 3] = [2_150, 2_990, 5_678];

    #[cfg(feature = "multicore")]
    fn parallel_windows_match_weighted_sum<C: GlvParams>() {
        for windows in [0, 1, 2, 3, 5, 20, 21, 33] {
            let points: Vec<_> = (0..windows)
                .map(|index| match index % 5 {
                    0 => C::identity(),
                    1 => C::generator(),
                    2 => -C::generator(),
                    _ => C::generator() * C::ScalarExt::from(index as u64),
                })
                .collect();
            for bits in [1, 4, 7] {
                let radix = C::ScalarExt::from(1 << bits);
                let mut power = C::ScalarExt::ONE;
                let mut expected = C::identity();
                for point in &points {
                    expected += *point * power;
                    power *= radix;
                }
                assert_eq!(
                    balanced_windows_sum::<C>(windows, bits, |index| Some(points[index])),
                    Some(expected),
                    "windows={windows}, bits={bits}",
                );
                for failure in 0..windows {
                    assert!(
                        balanced_windows_sum::<C>(windows, bits, |index| {
                            (index != failure).then_some(points[index])
                        })
                        .is_none()
                    );
                }
            }
        }
    }

    #[test]
    #[cfg(feature = "multicore")]
    fn parallel_windows_match_weighted_sum_on_both_curves() {
        parallel_windows_match_weighted_sum::<crate::pallas::Point>();
        parallel_windows_match_weighted_sum::<crate::vesta::Point>();
    }

    fn batch_invert_nonzero_matches_individual<F>()
    where
        F: Field + From<u64>,
    {
        for length in [0usize, 1, 2, 3, 31, 32, 33, 64, 257] {
            let mut values = (1..=length)
                .map(|value| F::from(u64::try_from(value).unwrap()))
                .collect::<Vec<_>>();
            let expected = values
                .iter()
                .map(|value| value.invert().unwrap())
                .collect::<Vec<_>>();
            let mut scratch = vec![F::ZERO; length];

            batch_invert_nonzero(&mut values, &mut scratch);

            assert_eq!(values, expected, "length {length}");
        }
    }

    #[test]
    fn batch_invert_nonzero_handles_boundaries() {
        batch_invert_nonzero_matches_individual::<crate::Fp>();
        batch_invert_nonzero_matches_individual::<crate::Fq>();
    }

    fn batch_invert_and_add_two_lanes_matches_individual<F>()
    where
        F: Field + From<u64>,
    {
        const LENGTHS: [usize; 13] = [0, 1, 2, 3, 31, 32, 33, 63, 64, 65, 255, 256, 257];

        for length in LENGTHS {
            let mut additions = (0..length)
                .map(|index| PendingAffineAddition {
                    output: index,
                    x_sum: F::from(u64::try_from(index + 3).unwrap()),
                    numerator: F::from(u64::try_from(index + 2).unwrap()),
                    denominator: F::from(u64::try_from(index + 1).unwrap()),
                    inversion_scratch: F::ZERO,
                })
                .collect::<Vec<_>>();
            let mut points = (0..length)
                .map(|index| AffinePoint {
                    x: F::from(u64::try_from(index + 5).unwrap()),
                    y: F::from(u64::try_from(index + 7).unwrap()),
                })
                .collect::<Vec<_>>();
            let expected = additions
                .iter()
                .zip(&points)
                .map(|(addition, left)| {
                    let slope = addition.numerator * addition.denominator.invert().unwrap();
                    let x = slope.square() - addition.x_sum;
                    let y = slope * (left.x - x) - left.y;
                    AffinePoint { x, y }
                })
                .collect::<Vec<_>>();

            batch_invert_and_add(&mut additions, &mut points)
                .expect("nonzero denominators must be invertible");
            for (index, (actual, expected)) in points.iter().zip(expected).enumerate() {
                assert_eq!(
                    actual.x, expected.x,
                    "two-lane affine x mismatch at length {length}, index {index}"
                );
                assert_eq!(
                    actual.y, expected.y,
                    "two-lane affine y mismatch at length {length}, index {index}"
                );
            }
        }
    }

    #[test]
    fn batch_invert_and_add_two_lanes() {
        batch_invert_and_add_two_lanes_matches_individual::<crate::Fp>();
        batch_invert_and_add_two_lanes_matches_individual::<crate::Fq>();
    }

    fn optimized_multiexp_matches_expected<C: GlvParams>() {
        let num_threads = current_num_threads();
        let mut selected = 0;
        for terms in VERIFIER_MULTIEXP_SIZES {
            let (scalars, bases, expected) = verifier_multiexp_inputs::<C>(terms);
            if let Some(actual) = try_multiexp::<C>(&scalars, &bases) {
                assert_eq!(
                    actual, expected,
                    "GLV MSM mismatch at {terms} terms with {num_threads} threads"
                );
                selected += 1;
            }
        }
        assert!(
            selected > 0,
            "GLV must be selected for at least one verifier-sized MSM with \
             {num_threads} threads"
        );
    }

    fn duplicate_base_multiexp_matches_expected<C: GlvParams>() {
        let terms = VERIFIER_MULTIEXP_SIZES[0];
        let scalar = scalars::<C::ScalarExt>(1)
            .next()
            .expect("the deterministic scalar corpus is nonempty");
        let msm_scalars = alloc::vec![scalar; terms];
        let bases = alloc::vec![C::generator().to_affine(); terms];
        let expected =
            C::generator() * (scalar * C::ScalarExt::from(u64::try_from(terms).unwrap()));

        let actual = try_multiexp::<C>(&msm_scalars, &bases)
            .expect("a verifier-sized duplicate-base MSM must use the optimized path");
        assert_eq!(actual, expected);
    }

    fn strauss_multiexp_matches_expected<C: GlvParams>() {
        const TERM_COUNTS: [usize; 10] = [0, 1, 2, 3, 8, 16, 32, 64, 66, 256];

        for terms in TERM_COUNTS {
            let (scalars, bases, expected) = verifier_multiexp_inputs::<C>(terms);
            assert_eq!(
                strauss_multiexp::<C>(&scalars, &bases),
                expected,
                "GLV-Strauss MSM mismatch at {terms} terms",
            );
        }
    }

    #[test]
    fn strauss_multiexp_matches_expected_pallas() {
        strauss_multiexp_matches_expected::<pallas::Point>();
    }

    #[test]
    fn strauss_multiexp_matches_expected_vesta() {
        strauss_multiexp_matches_expected::<vesta::Point>();
    }

    #[cfg(feature = "multicore")]
    fn planned_strauss_multiexp_matches_expected_at_thread_counts<C: GlvParams>() {
        const THREAD_COUNTS: [usize; 4] = [2, 3, 6, 8];
        const TERM_COUNTS: [usize; 9] = [3, 4, 6, 10, 16, 18, 34, 64, 66];

        for num_threads in THREAD_COUNTS {
            maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(num_threads)
                .build()
                .expect("test thread pool must build")
                .install(|| {
                    for terms in TERM_COUNTS {
                        let (scalars, bases, expected) = verifier_multiexp_inputs::<C>(terms);
                        assert_eq!(
                            planned_strauss_multiexp::<C>(&scalars, &bases, num_threads),
                            Some(expected),
                            "planned GLV-Strauss MSM mismatch at {terms} terms \
                             with {num_threads} threads",
                        );
                    }

                    let (scalars, bases, _) =
                        verifier_multiexp_inputs::<C>(MAX_PARALLEL_STRAUSS_TERMS + 1);
                    assert_eq!(
                        planned_strauss_multiexp::<C>(&scalars, &bases, num_threads),
                        None,
                    );
                });
        }
    }

    #[cfg(feature = "multicore")]
    #[test]
    fn planned_strauss_multiexp_matches_expected_pallas() {
        planned_strauss_multiexp_matches_expected_at_thread_counts::<pallas::Point>();
    }

    #[cfg(feature = "multicore")]
    #[test]
    fn planned_strauss_multiexp_matches_expected_vesta() {
        planned_strauss_multiexp_matches_expected_at_thread_counts::<vesta::Point>();
    }

    #[cfg(feature = "multicore")]
    fn optimized_multiexp_matches_expected_at_thread_counts<C: GlvParams>() {
        const THREAD_COUNTS: [usize; 6] = [1, 2, 3, 6, 8, 32];

        for num_threads in THREAD_COUNTS {
            maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(num_threads)
                .build()
                .expect("test thread pool must build")
                .install(|| {
                    assert_eq!(current_num_threads(), num_threads);
                    optimized_multiexp_matches_expected::<C>();
                });
        }
    }

    fn serial_c10_multiexp_matches_expected<C: GlvParams>() {
        const TERMS: usize = 5_678;
        const WINDOW_BITS: usize = 10;

        assert_eq!(
            multiexp_window_bits::<C>(TERMS, 1),
            Some(WINDOW_BITS),
            "verifier batch-64 must select the serial c=10 schedule"
        );
        let (scalars, bases, expected) = verifier_multiexp_inputs::<C>(TERMS);
        let components = scalars
            .iter()
            .map(decompose::<C>)
            .map(|(first, second)| (first.into(), second.into()))
            .collect::<Vec<_>>();
        let bases = multiexp_bases::<C>(&bases);
        let actual = multiexp_serial::<C>(&components, &bases, WINDOW_BITS)
            .expect("valid curve points have invertible affine denominators");

        assert_eq!(actual, expected, "serial c=10 GLV MSM mismatch");
    }

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

        assert_eq!(multiexp_window_bits::<pallas::Point>(2_150, 1), Some(8));
        assert_eq!(multiexp_window_bits::<pallas::Point>(2_990, 1), Some(9));
        assert_eq!(multiexp_window_bits::<pallas::Point>(3_924, 1), Some(9));
        assert_eq!(multiexp_window_bits::<pallas::Point>(3_925, 1), Some(10));
        assert_eq!(multiexp_window_bits::<pallas::Point>(5_678, 1), Some(10));
        assert_eq!(multiexp_window_bits::<pallas::Point>(5_678, 8), Some(9));

        assert_eq!(glv_multiexp_window_bits::<pallas::Point>(255, 1), None);
        assert_eq!(glv_multiexp_window_bits::<pallas::Point>(2_150, 1), Some(9));
        assert_eq!(glv_multiexp_window_bits::<vesta::Point>(5_678, 1), Some(11));

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
        assert_eq!(glv_multiexp_window_bits::<pallas::Point>(2_150, 8), Some(8));
        assert_eq!(glv_multiexp_window_bits::<vesta::Point>(5_678, 8), Some(9));

        // At sufficiently large sizes with whole waves on every worker,
        // doubling the term count outweighs the shorter components at both
        // candidate widths, and an overflowing term count is never planned.
        assert_eq!(
            glv_multiexp_window_bits::<pallas::Point>(1_000_000, 8),
            None
        );
        assert_eq!(
            glv_multiexp_window_bits::<pallas::Point>(usize::MAX, 8),
            None
        );
    }

    /// The planner's decisions at cells measured on Apple M4 (asm backend)
    /// and EPYC (portable) with explicit Rayon pools. Each expected value is
    /// the backend (and for GLV, the width) that measured fastest; every
    /// `None` is a cell where the generic ladder measured at least as fast as
    /// GLV at every candidate width.
    #[test]
    fn glv_multiexp_plan_matches_measured_cells() {
        fn plan(terms: usize, threads: usize) -> Option<usize> {
            glv_multiexp_window_bits::<pallas::Point>(terms, threads)
        }

        assert_eq!(plan(255, 1), None);
        assert_eq!(plan(255, 8), None);

        // Cells the single-width comparison rejected although GLV measured
        // 4–27% faster. Widening to `w + 1` turns a partial final wave into
        // whole waves for the 127-bit components.
        assert_eq!(plan(2_600, 3), Some(9));
        assert_eq!(plan(8_192, 2), Some(11));
        assert_eq!(plan(8_192, 3), Some(11));
        assert_eq!(plan(8_192, 4), Some(11));
        assert_eq!(plan(16_384, 2), Some(11));
        assert_eq!(plan(16_384, 3), Some(11));
        assert_eq!(plan(16_384, 4), Some(11));
        assert_eq!(plan(65_536, 2), Some(13));

        // Cells where both widths agree with the previous selection.
        assert_eq!(plan(2_150, 1), Some(9));
        assert_eq!(plan(2_600, 8), Some(8));
        assert_eq!(plan(4_300, 1), Some(10));
        assert_eq!(plan(8_192, 1), Some(11));
        assert_eq!(plan(8_192, 8), Some(10));
        assert_eq!(plan(16_384, 8), Some(10));
        assert_eq!(plan(32_768, 1), Some(12));
        assert_eq!(plan(32_768, 4), Some(11));

        // Cells where the generic ladder measured faster on both machines:
        // the GLV ladder's doubled term count costs more than the halved
        // window count saves once every worker already has whole waves.
        assert_eq!(plan(32_768, 8), None);
        assert_eq!(plan(65_536, 8), None);

        // The planner never asks for a width the generic default would not
        // reach within one bit, and both curves plan identically.
        for terms in [2_600usize, 8_192, 65_536] {
            for threads in [1usize, 3, 8] {
                let default = multiexp_window_bits::<pallas::Point>(terms, threads).unwrap();
                if let Some(width) = plan(terms, threads) {
                    assert!(width == default || width == default + 1);
                }
                assert_eq!(
                    plan(terms, threads),
                    glv_multiexp_window_bits::<vesta::Point>(terms, threads)
                );
            }
        }
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

    /// Exhaustively re-derives [`EFFECTIVE_CHAIN_UNITS`] and
    /// [`EFFECTIVE_CHAIN_RELATIONS`] from [`DELTA`] and the unit code
    /// order, mirroring `sage/effective_affine_chain.sage`: over all 6^7
    /// unit sequences there are exactly 54 valid chains (every stored
    /// point in a distinct unit orbit, no pre-addition state ±2), the
    /// minimal nontrivial-rotation count is 4 with exactly 4 chains
    /// attaining it, and the pinned chain is the lexicographically least
    /// of those. Also checks the group-level nonexceptionality for both
    /// Pasta scalar fields: no pre-addition state maps to 0 or ±2 mod n.
    #[test]
    fn effective_chain_derivation() {
        // Eisenstein arithmetic on (a, b) = a + bω, with ω² = -1 - ω.
        fn emul(x: (i32, i32), y: (i32, i32)) -> (i32, i32) {
            (x.0 * y.0 - x.1 * y.1, x.0 * y.1 + x.1 * y.0 - x.1 * y.1)
        }
        fn enorm(x: (i32, i32)) -> i32 {
            x.0 * x.0 - x.0 * x.1 + x.1 * x.1
        }
        // The units in code order [+1, -1, +ω, -ω, +ω², -ω²].
        const UNITS: [(i32, i32); 6] = [(1, 0), (-1, 0), (0, 1), (0, -1), (-1, -1), (1, 1)];

        // value = ±ω^rotation · Δ_slot, if value is in a target orbit.
        let relation_of = |value: (i32, i32)| -> Option<(u8, u8, bool)> {
            for (slot, &(da, db)) in DELTA.iter().enumerate() {
                for (code, &unit) in UNITS.iter().enumerate() {
                    if emul(unit, (i32::from(da), i32::from(db))) == value {
                        return Some((slot as u8, (code >> 1) as u8, code & 1 == 1));
                    }
                }
            }
            None
        };

        // The chain walk; `None` when a pre-addition state is ±2 (the
        // incomplete mixed addition's exceptional case).
        let walk = |codes: &[usize; 7]| -> Option<[(i32, i32); 8]> {
            let mut q = (1, 0);
            let mut path = [(0, 0); 8];
            path[0] = q;
            for (step, &code) in codes.iter().enumerate() {
                if q == (2, 0) || q == (-2, 0) {
                    return None;
                }
                q = emul(UNITS[code], (q.0 + 2, q.1));
                path[step + 1] = q;
            }
            Some(path)
        };

        let mut valid = 0usize;
        let mut best_rotations = usize::MAX;
        let mut minimal: Vec<([usize; 7], [(u8, u8, bool); 8], [(i32, i32); 8])> = Vec::new();
        for index in 0..6usize.pow(7) {
            // Base-6 digits of `index`, most significant first, so
            // increasing `index` walks code sequences lexicographically.
            let mut codes = [0usize; 7];
            for (slot, code) in codes.iter_mut().enumerate() {
                *code = (index / 6usize.pow(6 - slot as u32)) % 6;
            }
            let Some(path) = walk(&codes) else { continue };
            let mut slots_seen = [false; 8];
            let mut relations = [(0u8, 0u8, false); 8];
            let ok = path.iter().enumerate().all(|(i, &q)| match relation_of(q) {
                Some(relation) if !slots_seen[usize::from(relation.0)] => {
                    slots_seen[usize::from(relation.0)] = true;
                    relations[i] = relation;
                    true
                }
                _ => false,
            });
            if !ok {
                continue;
            }
            valid += 1;
            let rotations = codes.iter().filter(|&&code| code >> 1 != 0).count();
            if rotations < best_rotations {
                best_rotations = rotations;
                minimal.clear();
            }
            if rotations == best_rotations {
                minimal.push((codes, relations, path));
            }
        }
        assert_eq!(valid, 54, "expected 54 valid seven-step chains");
        assert_eq!(best_rotations, 4, "expected a four-rotation minimum");
        assert_eq!(minimal.len(), 4, "expected 4 chains at the minimum");

        let (codes, relations, path) = minimal[0];
        assert_eq!(
            codes.map(|code| code as u8),
            EFFECTIVE_CHAIN_UNITS,
            "pinned units must be the least minimal chain"
        );
        assert_eq!(relations, EFFECTIVE_CHAIN_RELATIONS, "pinned relations");

        // Group-level nonexceptionality: every pre-addition state q and
        // its offsets q ∓ 2 have small nonzero Eisenstein norm, so their
        // scalar-field images a + bλ are nonzero mod both group orders
        // (N(a + bω) = (a + bλ)(a + bλ̄) mod n, and 0 < N < n). Check the
        // norms and, directly, the images for both Pasta scalar fields.
        fn images_nonzero<F: WithSmallOrderMulGroup<3>>(states: &[(i32, i32)]) {
            let image = |v: (i32, i32)| {
                let signed = |c: i32| {
                    let m = F::from(u64::from(c.unsigned_abs()));
                    if c < 0 { -m } else { m }
                };
                signed(v.0) + signed(v.1) * F::ZETA
            };
            for &q in states {
                for offset in [0, 2, -2] {
                    let shifted = (q.0 + offset, q.1);
                    assert!(
                        !bool::from(image(shifted).is_zero()),
                        "chain state maps to an exceptional point"
                    );
                }
            }
        }
        for &q in &path[..7] {
            for offset in [0, 2, -2] {
                let norm = enorm((q.0 + offset, q.1));
                assert!(norm != 0 && norm < 100, "norms must be small and nonzero");
            }
        }
        images_nonzero::<crate::Fp>(&path[..7]);
        images_nonzero::<crate::Fq>(&path[..7]);
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

    #[cfg(feature = "multicore")]
    fn parallel_multiexp_matches_serial<C: GlvParams>() {
        const TEST_TERMS: usize = 64;
        const WINDOW_BITS: [usize; 6] = [1, 3, 6, 8, 9, 10];

        let generator = C::generator();
        let mut points = (0..TEST_TERMS)
            .map(|i| generator * C::ScalarExt::from(i as u64 + 1))
            .collect::<Vec<_>>();
        let mut test_scalars = scalars::<C::ScalarExt>(TEST_TERMS as u64).collect::<Vec<_>>();

        // Exercise identity terms, zero scalars, and cancellation alongside
        // the deterministic full-width inputs.
        points[0] = C::identity();
        test_scalars[0] = C::ScalarExt::ONE;
        points[1] = generator;
        test_scalars[1] = C::ScalarExt::ZERO;
        points[2] = generator;
        test_scalars[2] = C::ScalarExt::ONE;
        points[3] = -generator;
        test_scalars[3] = C::ScalarExt::ONE;

        let mut bases = alloc::vec![C::AffineExt::identity(); TEST_TERMS];
        C::batch_normalize(&points, &mut bases);
        let components = test_scalars
            .iter()
            .map(decompose::<C>)
            .map(checked_signed_magnitudes)
            .collect::<Option<Vec<_>>>()
            .expect("valid scalar decompositions fit the GLV component bound");
        let bases = multiexp_bases::<C>(&bases);

        for window_bits in WINDOW_BITS {
            assert_eq!(
                multiexp_parallel::<C>(&components, &bases, window_bits),
                multiexp_serial::<C>(&components, &bases, window_bits),
                "parallel and serial MSMs differ at window width {window_bits}",
            );
        }
    }

    #[cfg(feature = "multicore")]
    #[test]
    fn parallel_multiexp_matches_serial_pallas() {
        parallel_multiexp_matches_serial::<pallas::Point>();
    }

    #[cfg(feature = "multicore")]
    #[test]
    fn parallel_multiexp_matches_serial_vesta() {
        parallel_multiexp_matches_serial::<vesta::Point>();
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
            assert!(
                a1 >> GLV_COMPONENT_BITS == 0,
                "k1 exceeds {GLV_COMPONENT_BITS} bits"
            );
            assert!(
                a2 >> GLV_COMPONENT_BITS == 0,
                "k2 exceeds {GLV_COMPONENT_BITS} bits"
            );
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

    /// The raw effective-coordinate helpers against the native group law:
    /// the incomplete mixed addition (with `z_out == z_in * ratio`), the
    /// chain-unit application against `endo` and negation, and the backward
    /// global-Z pass on a real ratio-linked chain.
    fn effective_raw_ops_match_native<C: GlvParams>() {
        let g = C::generator();
        let token = || private::CrateToken(());

        for (i, k) in scalars::<C::ScalarExt>(8).enumerate() {
            // Distinct positive multiples of g, so a != ±b and neither is
            // the identity; native `Mul` leaves a with a nontrivial Z.
            let a = g * (k + C::ScalarExt::ONE);
            let b = g * (k + C::ScalarExt::from(2 + i as u64));
            let mut b_affine = [C::AffineExt::identity(); 1];
            C::batch_normalize(&[b], &mut b_affine);
            let (bx, by) = C::affine_xy(&b_affine[0]);

            let (ax, ay, az) = a.jacobian_coordinates();
            let q = RawJacobian {
                x: ax,
                y: ay,
                z: az,
            };
            let d = EffectiveAffine { x: bx, y: by };
            let (sum, ratio) = add_mixed_with_ratio_nonexceptional(&q, &d);
            assert_eq!(sum.z, az * ratio, "Z3 must equal Z1 * ratio");
            assert_eq!(
                C::projective_unchecked(sum.x, sum.y, sum.z, token()),
                a + b,
                "incomplete mixed addition must match native addition"
            );

            for unit in 0..6u8 {
                let rotated = apply_chain_unit(q, unit);
                let mut expected = a;
                for _ in 0..(unit >> 1) {
                    expected = expected.endo();
                }
                if unit & 1 == 1 {
                    expected = -expected;
                }
                assert_eq!(rotated.z, az, "units must not touch z");
                assert_eq!(
                    C::projective_unchecked(rotated.x, rotated.y, rotated.z, token()),
                    expected,
                    "unit {unit} must act as endo/negation"
                );
            }
        }

        // The backward global-Z pass on a chain whose ratios are real
        // (five mixed additions by one step point): every rescaled entry,
        // read with the final denominator, must keep its group value.
        let step_point = g * C::ScalarExt::from(5);
        let mut step_affine = [C::AffineExt::identity(); 1];
        C::batch_normalize(&[step_point], &mut step_affine);
        let (sx, sy) = C::affine_xy(&step_affine[0]);
        let step = EffectiveAffine { x: sx, y: sy };

        let start = g * scalars::<C::ScalarExt>(1).next().unwrap();
        let (x, y, z) = start.jacobian_coordinates();
        let mut chain = [RawJacobian { x, y, z }; 6];
        let mut ratios = [C::Base::ONE; 5];
        let mut expected = [start; 6];
        for i in 0..5 {
            let (sum, ratio) = add_mixed_with_ratio_nonexceptional(&chain[i], &step);
            chain[i + 1] = sum;
            ratios[i] = ratio;
            expected[i + 1] = expected[i] + step_point;
        }
        let global = chain[5].z;
        globalize_z(&mut chain, &ratios);
        for (raw, expected) in chain.iter().zip(expected) {
            assert_eq!(
                C::projective_unchecked(raw.x, raw.y, global, token()),
                expected,
                "globalized entries must keep their group value"
            );
        }
    }

    /// Effective-table entries against native multiplication, for both a
    /// plain and a rescaled projective input representation: every restored
    /// digit point `(xs[e][j], ys[j], z)` must equal the digit multiple of
    /// P, and every entry must satisfy the effective curve equation
    /// $y^2 = x^3 + b z^6$. Identity inputs give the all-zero table with
    /// `z = 0`, alone and mixed into a batch.
    fn effective_table_matches_native<C: GlvParams>() {
        let g = C::generator();
        let token = || private::CrateToken(());
        for (i, k) in scalars::<C::ScalarExt>(4).enumerate() {
            let p = g * (k + C::ScalarExt::ONE);
            // A rescaled representation of the same point:
            // (t²X, t³Y, tZ) for a nonzero t.
            let (x, y, z) = p.jacobian_coordinates();
            let t = C::Base::from(0xACE1 + i as u64);
            let t2 = t.square();
            let rescaled = C::projective_unchecked(x * t2, y * t2 * t, z * t, token());
            assert_eq!(rescaled, p, "rescaling must preserve the point");

            for table in [EffectiveTable::new(&p), EffectiveTable::new(&rescaled)] {
                assert!(!table.is_identity());
                let z2 = table.z.square();
                let b_z6 = C::b() * (z2 * table.z).square();
                for j in 0..8 {
                    assert_eq!(
                        table.ys[j].square(),
                        table.xs[0][j].square() * table.xs[0][j] + b_z6,
                        "entry {j} must lie on the effective curve"
                    );
                }
                for code in 1..=48u8 {
                    let (x, y) = table.window_digit_coords(code);
                    assert_eq!(
                        C::projective_unchecked(x, y, table.z, token()),
                        p * digit_scalar::<C::ScalarExt>(code),
                        "digit {code} must equal [a + b*lambda]P"
                    );
                }
            }
        }

        let identity_table = EffectiveTable::<C>::new(&C::identity());
        assert!(identity_table.is_identity());
        assert!(
            identity_table
                .xs
                .iter()
                .flatten()
                .chain(&identity_table.ys)
                .chain([&identity_table.z])
                .all(|v| bool::from(v.is_zero())),
            "identity table must be the all-zero sentinel"
        );
        let batch = EffectiveTable::batch(&[C::identity(), g, C::identity()]);
        assert_eq!(batch.len(), 3);
        assert!(batch[0].is_identity() && batch[2].is_identity());
        assert!(!batch[1].is_identity());
        assert_eq!(
            C::projective_unchecked(batch[1].xs[0][0], batch[1].ys[0], batch[1].z, token()),
            g,
            "the Δ0 entry must be the base point"
        );
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

        // Exercise the affine table builder with identity lanes on both
        // sides of enough live inputs to cross its batching threshold.
        let mut points = Vec::with_capacity(TABLE_BATCH_AFFINE_MIN_POINTS + 2);
        points.push(identity);
        points.extend(
            (1..=TABLE_BATCH_AFFINE_MIN_POINTS).map(|i| generator * C::ScalarExt::from(i as u64)),
        );
        points.push(identity);
        let batched = Table::batch(&points);
        for (point, table) in points.iter().zip(&batched) {
            assert_eq!(table.point(), *point);
            assert_eq!(table.mul(&k), *point * k);
        }
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

    /// The routed same-scalar batch entry (effective sidecar with the
    /// normalized fallback) against native multiplication and both forced
    /// backends, across batch sizes straddling the sidecar gate (with an
    /// identity lane mixed in) and edge-case plus full-width scalars.
    fn same_scalar_routing_matches_native<C: GlvParams>() {
        let g = C::generator();
        let lambda = C::ScalarExt::ZETA;
        let small_sizes = [
            0usize, 1, 2, 3, 7, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129,
        ];
        let large_sizes = [512usize, 2048];
        let ks = [
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
            scalars::<C::ScalarExt>(1).next().unwrap(),
        ];
        let check = |size: usize, ks: &[C::ScalarExt]| {
            let points: Vec<C> = (0..size)
                .map(|i| {
                    if size > 2 && i == size / 2 {
                        C::identity()
                    } else {
                        g * (C::ScalarExt::from(i as u64 + 1) + lambda)
                    }
                })
                .collect();
            for &k in ks {
                let mut routed = points.clone();
                batch_mul_same_scalar_in_place(&mut routed, &k);
                for (p, out) in points.iter().zip(&routed) {
                    assert_eq!(*out, *p * k, "routed batch != native at size {size}");
                }

                let mut normalized = points.clone();
                batch_mul_same_scalar_normalized(&mut normalized, &Decomposed::new(&k));
                assert_eq!(normalized, routed, "forced normalized != routed");

                let mut effective = points.clone();
                if try_batch_mul_same_scalar_effective(&Decomposed::new(&k), &mut effective) {
                    assert_eq!(effective, routed, "forced effective != routed");
                } else {
                    assert_eq!(effective, points, "a declined batch must be untouched");
                }
            }
        };
        for size in small_sizes {
            check(size, &ks);
        }
        for size in large_sizes {
            check(size, &ks[8..]);
        }
    }

    /// The routed FFT multiplication layers (same-scalar and pairs)
    /// against their normalized backends and native multiplication, across
    /// the gate and with an identity lane forcing the fallback.
    fn fft_mul_layers_match<C: GlvParams>() {
        let g = C::generator();
        let lambda = C::ScalarExt::ZETA;
        let sizes = [1usize, 31, 32, 33, 65, 128];
        let scalar_pool: Vec<Decomposed<C>> = scalars::<C::ScalarExt>(128)
            .map(|k| Decomposed::new(&k))
            .collect();
        let k0_scalar = scalars::<C::ScalarExt>(1).next().unwrap();
        let k0 = Decomposed::<C>::new(&k0_scalar);
        for size in sizes {
            for with_identity in [false, true] {
                let points: Vec<C> = (0..size)
                    .map(|i| {
                        if with_identity && size > 2 && i == size / 2 {
                            C::identity()
                        } else {
                            g * (C::ScalarExt::from(i as u64 + 1) + lambda)
                        }
                    })
                    .collect();

                let routed = Table::mul_decomposed_same_scalar_affine(&points, &k0);
                let normalized = Table::mul_decomposed_same_scalar_affine_normalized(&points, &k0);
                assert_eq!(routed, normalized, "same-scalar layer routes must agree");
                for (p, out) in points.iter().zip(&routed) {
                    assert_eq!(
                        C::from(*out),
                        *p * k0_scalar,
                        "same-scalar layer != native at size {size}"
                    );
                }

                let pair_scalars: Vec<&Decomposed<C>> = scalar_pool.iter().take(size).collect();
                let routed = Table::mul_decomposed_pairs_affine(&points, &pair_scalars);
                let normalized =
                    Table::mul_decomposed_pairs_affine_normalized(&points, &pair_scalars);
                assert_eq!(routed, normalized, "pairs layer routes must agree");
                for ((p, out), k) in points
                    .iter()
                    .zip(&routed)
                    .zip(scalars::<C::ScalarExt>(size as u64))
                {
                    assert_eq!(
                        C::from(*out),
                        *p * k,
                        "pairs layer != native at size {size}"
                    );
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
        // i.e. 2P + P — the first affine denominator x(D) - x(P) vanishes.
        let d_eq_s = craft(&[1, 1]);
        // d == -s: 2P + (-P) — the intermediate P + D is the identity.
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
        assert!(!affine_ladder_safe::<C>(&d_eq_neg_s.0));
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

            // The effective-affine sidecar shares the same gate: it must
            // decline every exceptional schedule untouched and stay exact
            // on the same-shape safe one.
            let mut sidecar = points.clone();
            if try_batch_mul_same_scalar_effective(&d, &mut sidecar) {
                assert!(
                    d.affine_ladder_safe,
                    "sidecar must decline unsafe schedules"
                );
                for (p, out) in points.iter().zip(&sidecar) {
                    assert_eq!(*out, *p * value, "sidecar must stay exact");
                }
            } else {
                assert!(!d.affine_ladder_safe);
                assert_eq!(sidecar, points, "a declined batch must be untouched");
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
                assert!(
                    actual
                        .iter()
                        .zip(expected)
                        .all(|(actual, expected)| C::from(*actual) == expected)
                );
            }
        }
    }

    fn assert_affine_bucket_results_match_native<C: GlvParams>(
        case: &str,
        reduced: Vec<Option<AffinePoint<C::Base>>>,
        source: &[Vec<C>],
    ) {
        assert_eq!(reduced.len(), source.len());
        for (actual, bucket) in reduced.into_iter().zip(source) {
            let actual = match actual {
                Some(point) => C::from(C::affine_unchecked(
                    point.x,
                    point.y,
                    private::CrateToken(()),
                )),
                None => C::identity(),
            };
            let expected = bucket.iter().copied().sum::<C>();
            assert_eq!(actual, expected, "affine reduction mismatch in case {case}");
        }
    }

    fn assert_batch_affine_buckets_match_native<C: GlvParams>(case: &str, source: &[Vec<C>]) {
        let mut points = Vec::new();
        let mut offsets = Vec::with_capacity(source.len() + 1);
        offsets.push(0);
        for bucket in source {
            for point in bucket {
                let affine = C::AffineExt::from(*point);
                let (x, y) = C::affine_xy(&affine);
                points.push(AffinePoint { x, y });
            }
            offsets.push(points.len());
        }

        let reduced = reduce_affine_buckets(points.clone(), offsets.clone())
            .unwrap_or_else(|| panic!("valid curve points must reduce in case {case}"));
        let in_place = reduce_affine_buckets_in_place(points.clone(), offsets.clone())
            .or_else(|| reduce_affine_buckets(points, offsets))
            .unwrap_or_else(|| panic!("valid curve points must reduce in case {case}"));

        for reduced in [reduced, in_place] {
            assert_affine_bucket_results_match_native::<C>(case, reduced, source);
        }
    }

    fn batch_affine_buckets_match_native<C: GlvParams>() {
        let generator = C::generator();
        let two = generator.double();
        let three = two + generator;
        let four = three + generator;
        let five = four + generator;
        let cases = [
            ("empty bucket", alloc::vec![Vec::new()]),
            ("singleton bucket", alloc::vec![alloc::vec![generator]]),
            (
                "first-level doubling",
                alloc::vec![alloc::vec![generator, generator]],
            ),
            (
                "first-level inverse pair",
                alloc::vec![alloc::vec![generator, -generator]],
            ),
            // The first level adds G + 2G, then pairs the resulting 3G
            // with the carried 3G. The fallback therefore first occurs at
            // the second level, after the first level has been committed.
            (
                "second-level doubling",
                alloc::vec![alloc::vec![generator, two, three]],
            ),
            // As above, but the carried point is -3G, so the second-level
            // exceptional pair cancels to the identity.
            (
                "second-level inverse pair",
                alloc::vec![alloc::vec![generator, two, -three]],
            ),
            (
                "odd bucket",
                alloc::vec![alloc::vec![generator, two, three, four, five]],
            ),
            (
                "one exceptional pair in a shared batch",
                alloc::vec![
                    Vec::new(),
                    alloc::vec![generator],
                    alloc::vec![generator, two],
                    alloc::vec![generator, generator],
                    alloc::vec![three, four, five],
                ],
            ),
        ];

        for (case, source) in cases {
            assert_batch_affine_buckets_match_native::<C>(case, &source);
        }

        // Powers of two keep every intermediate pair distinct, so this
        // exercises successful in-place reduction without its fallback.
        let clean_source = [
            Vec::new(),
            alloc::vec![generator],
            alloc::vec![generator, two],
            alloc::vec![generator, two, four],
            (0..9)
                .map(|bit| generator * C::ScalarExt::from(1u64 << bit))
                .collect(),
        ];
        let mut clean_points = Vec::new();
        let mut clean_offsets = Vec::with_capacity(clean_source.len() + 1);
        clean_offsets.push(0);
        for bucket in &clean_source {
            for point in bucket {
                let affine = C::AffineExt::from(*point);
                let (x, y) = C::affine_xy(&affine);
                clean_points.push(AffinePoint { x, y });
            }
            clean_offsets.push(clean_points.len());
        }
        let clean_reduced = reduce_affine_buckets_in_place(clean_points, clean_offsets)
            .expect("distinct points should use the in-place reducer");
        assert_affine_bucket_results_match_native::<C>(
            "direct successful in-place reduction",
            clean_reduced,
            &clean_source,
        );

        let affine = C::AffineExt::from(generator);
        let (x, y) = C::affine_xy(&affine);
        let duplicate = AffinePoint { x, y };
        assert!(
            reduce_affine_buckets_in_place(alloc::vec![duplicate, duplicate], alloc::vec![0, 2],)
                .is_none()
        );
    }

    fn batch_inversion_zero_denominator_is_failure_atomic_for<F: Field>() {
        let cases = [
            ("single first lane", alloc::vec![F::ZERO]),
            ("first lane", alloc::vec![F::ZERO, F::ONE]),
            ("second lane", alloc::vec![F::ONE, F::ZERO]),
            (
                "odd trailing first lane",
                alloc::vec![F::ONE, F::ONE, F::ZERO],
            ),
        ];

        for (case, denominators) in cases {
            let mut additions = denominators
                .into_iter()
                .enumerate()
                .map(|(output, denominator)| PendingAffineAddition {
                    output,
                    x_sum: F::ZERO,
                    numerator: F::ZERO,
                    denominator,
                    inversion_scratch: F::ZERO,
                })
                .collect::<Vec<_>>();
            let mut points = alloc::vec![
                AffinePoint {
                    x: F::ONE,
                    y: F::ONE,
                };
                additions.len()
            ];
            let original_points = points.clone();

            assert!(
                batch_invert_and_add(&mut additions, &mut points).is_none(),
                "zero denominator was accepted in case {case}"
            );
            for (actual, original) in points.iter().zip(original_points) {
                assert_eq!(actual.x, original.x, "x changed in case {case}");
                assert_eq!(actual.y, original.y, "y changed in case {case}");
            }
        }
    }

    #[test]
    fn batch_inversion_zero_denominator_is_failure_atomic() {
        batch_inversion_zero_denominator_is_failure_atomic_for::<crate::Fp>();
        batch_inversion_zero_denominator_is_failure_atomic_for::<crate::Fq>();
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
                fn effective_raw_ops() {
                    effective_raw_ops_match_native::<$curve>();
                }
                #[test]
                fn effective_table() {
                    effective_table_matches_native::<$curve>();
                }
                #[test]
                fn same_scalar_routing() {
                    same_scalar_routing_matches_native::<$curve>();
                }
                #[test]
                fn fft_mul_layers() {
                    fft_mul_layers_match::<$curve>();
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
                fn batch_affine_buckets() {
                    batch_affine_buckets_match_native::<$curve>();
                }
                #[test]
                fn optimized_multiexp() {
                    #[cfg(not(feature = "multicore"))]
                    optimized_multiexp_matches_expected::<$curve>();
                    #[cfg(feature = "multicore")]
                    optimized_multiexp_matches_expected_at_thread_counts::<$curve>();
                }
                #[test]
                fn duplicate_base_multiexp() {
                    duplicate_base_multiexp_matches_expected::<$curve>();
                }
                #[test]
                fn serial_c10_multiexp() {
                    serial_c10_multiexp_matches_expected::<$curve>();
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

        fn nonzero_small_multiple() -> impl Strategy<Value = i8> {
            // A deliberately small signed range produces frequent duplicate
            // and inverse points, so random bucket trees exercise exceptional
            // affine additions instead of almost always taking the fast path.
            (-8i8..=8).prop_filter("the affine reducer omits identities", |multiple| {
                *multiple != 0
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

                        /// Arbitrary collision-heavy bucket partitions agree
                        /// with the native group law.
                        #[test]
                        fn batch_affine_buckets_match_native(
                            multiples in proptest::collection::vec(
                                proptest::collection::vec(
                                    nonzero_small_multiple(),
                                    0..16,
                                ),
                                1..8,
                            ),
                        ) {
                            let generator = <$curve>::generator();
                            let source: alloc::vec::Vec<alloc::vec::Vec<$curve>> = multiples
                                .into_iter()
                                .map(|bucket| {
                                    bucket
                                        .into_iter()
                                        .map(|multiple| {
                                            let point = generator
                                                * Scalar::from(u64::from(
                                                    multiple.unsigned_abs(),
                                                ));
                                            if multiple.is_negative() {
                                                -point
                                            } else {
                                                point
                                            }
                                        })
                                        .collect()
                                })
                                .collect();
                            assert_batch_affine_buckets_match_native::<$curve>(
                                "property-generated buckets",
                                &source,
                            );
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

    /// The magnitude profile of `terms` deterministic full-width scalars —
    /// the planner input for the measured full-width cells.
    #[cfg(feature = "orbits")]
    fn deterministic_profile<C: GlvParams>(terms: usize) -> MagnitudeProfile {
        let components: Vec<_> = scalars::<C::ScalarExt>(terms as u64)
            .map(|k| decompose::<C>(&k))
            .map(|(first, second)| (first.into(), second.into()))
            .collect();
        MagnitudeProfile::new(&components)
    }

    #[cfg(feature = "orbits")]
    #[test]
    fn multiexp_plan_selection() {
        fn plan(terms: usize, threads: usize) -> Option<MultiexpPlan> {
            plan_multiexp::<pallas::Point>(&deterministic_profile::<pallas::Point>(terms), threads)
        }
        let booth = |window_bits| Some(MultiexpPlan::Booth { window_bits });
        let orbit = |window_bits| Some(MultiexpPlan::Orbit { window_bits });

        // Below the amortization floor the generic MSM keeps the job, and
        // below the orbit backend's own 512-term floor Booth keeps it
        // (measured at 256 terms the orbit's fixed per-window costs lose
        // 2..7% at low thread counts).
        assert_eq!(plan(255, 1), None);
        assert_eq!(plan(255, 32), None);
        assert_eq!(plan(256, 1), booth(7));
        assert_eq!(plan(384, 8), booth(6));

        // Serial: measured parity with Booth within ±2% at 512–8,192 terms
        // and +4..5% ahead at 16,384 (interleaved samples; an earlier
        // sequential sweep read +2..6% everywhere through the harness
        // artifact — see `msm_backend_timings`). The model prices the
        // orbit ahead at exactly these widths, which is harmless at
        // parity.
        assert_eq!(plan(512, 1), orbit(4));
        assert_eq!(plan(1_024, 1), orbit(4));
        assert_eq!(plan(2_048, 1), orbit(5));
        assert_eq!(plan(4_096, 1), orbit(5));
        assert_eq!(plan(8_192, 1), orbit(5));
        assert_eq!(plan(16_384, 1), orbit(6));
        assert_eq!(plan(65_536, 1), orbit(6));

        // Small parallel MSMs stay on Booth: the orbit backend measured at
        // or below par there. (512 terms on 4 workers is a noise-level tie
        // that flipped winners between runs; the model prices it to the
        // orbit by under 5%.)
        assert_eq!(plan(512, 4), orbit(4));
        assert_eq!(plan(512, 8), booth(8));
        assert_eq!(plan(1_024, 8), booth(8));
        assert_eq!(plan(2_048, 8), booth(8));
        assert_eq!(plan(2_048, 16), booth(8));

        // Mid and large parallel MSMs: measured orbit wins of +10..+41%.
        assert_eq!(plan(2_048, 4), orbit(5));
        assert_eq!(plan(65_536, 4), orbit(6));
        assert_eq!(plan(4_096, 8), orbit(5));
        assert_eq!(plan(8_192, 8), orbit(6));
        assert_eq!(plan(16_384, 8), orbit(6));
        assert_eq!(plan(65_536, 8), orbit(6));
        assert_eq!(plan(8_192, 16), orbit(5));
        assert_eq!(plan(16_384, 16), orbit(5));
        // The bandwidth floor moves the 16-worker width-5/6 boundary to
        // ~28,672 terms, between grid points, so the k = 15 verifier's
        // 32,770-term final check plans width 6. Measured end to end on
        // M4 Max (whose full pool is 16), that turned the k = 15
        // verifier's ~5% orbit loss into parity and k = 16 into an 8%
        // win; 16,384 and 24,576 stay at width 5.
        assert_eq!(plan(32_768, 16), orbit(6));

        // Saturated pools (+30..+54% measured). At 65,536 terms the
        // bandwidth floor picks the widest window: c6 measured 11-13%
        // ahead of the per-worker model's c5 on both grids and both
        // curves (2026-08-26), total traffic being the binding resource
        // once every window has a worker.
        assert_eq!(plan(2_048, 32), orbit(5));
        assert_eq!(plan(8_192, 32), orbit(5));
        assert_eq!(plan(65_536, 32), orbit(6));

        // Both curves plan these full-width cells identically, and a Booth
        // selection always uses a width the measured-cell contract of
        // `glv_multiexp_window_bits` would consider.
        for terms in [512usize, 2_048, 8_192, 65_536] {
            for threads in [1usize, 4, 8, 32] {
                let plan = plan_multiexp::<pallas::Point>(
                    &deterministic_profile::<pallas::Point>(terms),
                    threads,
                );
                assert_eq!(
                    plan,
                    plan_multiexp::<vesta::Point>(
                        &deterministic_profile::<vesta::Point>(terms),
                        threads,
                    )
                );
                if let Some(MultiexpPlan::Booth { window_bits }) = plan {
                    let default = multiexp_window_bits::<pallas::Point>(terms, threads).unwrap();
                    assert!(window_bits == default || window_bits == default + 1);
                }
            }
        }
    }

    /// Sparse profiles reprice the backends: witness-commitment shapes
    /// (boolean and byte-scale scalars, zero padding) plan onto the Booth
    /// backend, whose half-columns reach far fewer windows than the joint
    /// radix-2^c recoding; a zero-heavy full-width residue keeps the orbit.
    #[cfg(feature = "orbits")]
    #[test]
    fn multiexp_plan_sparse_profiles() {
        fn profile_of(magnitudes: impl Iterator<Item = u128>) -> MagnitudeProfile {
            let components: Vec<(SignedMagnitude, SignedMagnitude)> = magnitudes
                .map(|magnitude| {
                    (
                        SignedMagnitude {
                            negative: false,
                            magnitude,
                        },
                        SignedMagnitude {
                            negative: false,
                            magnitude: 0,
                        },
                    )
                })
                .collect();
            MagnitudeProfile::new(&components)
        }

        // A boolean column: half zero, half one. A single live window
        // either way; both backends price it as almost nothing (the
        // magnitude-capped orbit walks two windows, Booth one), so either
        // choice is fine — what matters is that a GLV backend takes it at
        // its true (near-free) cost rather than a full-width one.
        let boolean = profile_of((0u128..2_048).map(|i| i & 1));
        assert!(plan_multiexp::<pallas::Point>(&boolean, 1).is_some());

        // Byte-decomposition shape: 32-bit scalars.
        let bytes = profile_of((0u128..2_048).map(|i| 0x8000_0000 + i));
        assert!(matches!(
            plan_multiexp::<pallas::Point>(&bytes, 1),
            Some(MultiexpPlan::Booth { .. })
        ));

        // Mostly zero, full-width residue (an Orchard commitment shape:
        // 2040 of 2049 zero): the live quarter is still full-width, but the
        // tiny visit counts keep Booth's cheaper reducer ahead.
        let sparse_full =
            profile_of((0u128..2_048).map(|i| if i % 4 == 0 { (1u128 << 126) + i } else { 0 }));
        let plan = plan_multiexp::<pallas::Point>(&sparse_full, 1);
        assert!(plan.is_some(), "a quarter-full MSM still beats the generic");
    }

    /// Manual timing harness comparing the MSM backends; used to calibrate
    /// [`plan_multiexp`]'s measured cells. Not part of the automated suite.
    ///
    /// ```text
    /// cargo test --release --features multicore,orbits --lib -- \
    ///     --ignored msm_backend_timings --nocapture
    /// ```
    ///
    /// **Measurement trap (found 2026-08-25):** an earlier version timed
    /// each backend as one sequential block per cell, and the process's
    /// first-run allocator warm-up landed entirely on the first curve's
    /// serial Booth column, inflating it ~15–20% at 512–16,384 terms —
    /// Booth allocates a fresh `multiexp_bases` of ~200 KiB–2 MiB per
    /// iteration, exactly the affected size band, and an order-swapped
    /// build moved the inflation with the order. Samples are therefore
    /// interleaved round-robin per cell (one sample of every candidate per
    /// round) after one untimed warm-up per candidate. The corrected
    /// full-width serial picture on the fit host is parity within ±2% at
    /// 512–8,192 terms and orbit +4–5% at 16,384; the parallel columns
    /// were unaffected.
    #[cfg(feature = "orbits")]
    #[test]
    #[ignore = "manual timing harness; see the doc comment"]
    fn msm_backend_timings() {
        use std::time::Instant;

        fn median_millis(mut samples: Vec<f64>) -> f64 {
            samples.sort_by(f64::total_cmp);
            samples[samples.len() / 2]
        }

        fn time_once<C: GlvParams>(f: impl Fn() -> Option<C>) -> f64 {
            let start = Instant::now();
            let result = f();
            let elapsed = start.elapsed().as_secs_f64() * 1e3;
            assert!(result.is_some(), "backend must produce a result");
            elapsed
        }

        fn run<C: GlvParams>(curve: &str) {
            const SIZES: [usize; 8] = [256, 512, 1_024, 2_048, 4_096, 8_192, 16_384, 65_536];
            const WITNESS_SIZES: [usize; 2] = [2_048, 8_192];
            const THREADS: [usize; 5] = [1, 4, 8, 16, 32];

            for threads in THREADS {
                #[cfg(feature = "multicore")]
                let pool = maybe_rayon::ThreadPoolBuilder::new()
                    .num_threads(threads)
                    .build()
                    .expect("bench thread pool must build");
                #[cfg(not(feature = "multicore"))]
                if threads != 1 {
                    continue;
                }

                for (corpus, terms) in SIZES
                    .iter()
                    .map(|&terms| ("full", terms))
                    .chain(WITNESS_SIZES.iter().map(|&terms| ("witness", terms)))
                {
                    let iters = (2_000_000 / terms).clamp(3, 40) | 1;
                    // "witness" mimics a halo2 witness commitment: zero
                    // padding, boolean and byte-scale cells, and full-width
                    // values in equal shares.
                    let scalars: Vec<C::ScalarExt> = testutil::scalars(terms as u64)
                        .enumerate()
                        .map(|(i, k)| match (corpus, i % 4) {
                            ("witness", 0) => C::ScalarExt::ZERO,
                            ("witness", 1) => C::ScalarExt::from(i as u64 & 1),
                            ("witness", 2) => C::ScalarExt::from(0x8000_0000 + i as u64),
                            _ => k,
                        })
                        .collect();
                    let points: Vec<C> = testutil::scalars::<C::ScalarExt>(terms as u64)
                        .map(|s| C::generator() * (s + C::ScalarExt::ONE))
                        .collect();
                    let mut bases = alloc::vec![C::AffineExt::identity(); terms];
                    C::batch_normalize(&points, &mut bases);
                    let components: Vec<_> = scalars
                        .iter()
                        .map(decompose::<C>)
                        .map(checked_signed_magnitudes)
                        .collect::<Option<_>>()
                        .unwrap();

                    let body = || {
                        let booth_bits = booth_multiexp_estimate::<C>(terms, threads)
                            .expect("booth estimate")
                            .1;
                        let booth_run = || {
                            let booth_bases = multiexp_bases::<C>(&bases);
                            multiexp::<C>(&components, &booth_bases, booth_bits, threads)
                        };
                        let orbit_widths: Vec<usize> =
                            (orbit::MIN_WINDOW_BITS..=orbit::MAX_WINDOW_BITS).collect();
                        // One untimed warm-up per candidate, then interleaved
                        // rounds — one sample of every candidate per round —
                        // so process-lifetime warm-up cannot land on
                        // whichever candidate runs first (see the doc
                        // comment's measurement trap).
                        assert!(booth_run().is_some());
                        for &c in &orbit_widths {
                            assert!(
                                orbit::multiexp::<C>(&components, &bases, c, threads).is_some()
                            );
                        }
                        let mut booth_samples = Vec::with_capacity(iters);
                        let mut orbit_samples =
                            alloc::vec![Vec::with_capacity(iters); orbit_widths.len()];
                        for _ in 0..iters {
                            booth_samples.push(time_once::<C>(&booth_run));
                            for (&c, samples) in orbit_widths.iter().zip(&mut orbit_samples) {
                                samples.push(time_once::<C>(|| {
                                    orbit::multiexp::<C>(&components, &bases, c, threads)
                                }));
                            }
                        }
                        let booth = median_millis(booth_samples);
                        let orbits: Vec<(usize, f64)> = orbit_widths
                            .iter()
                            .zip(orbit_samples)
                            .map(|(&c, samples)| (c, median_millis(samples)))
                            .collect();
                        let plan = plan_multiexp::<C>(&MagnitudeProfile::new(&components), threads);
                        let (best_c, best_orbit) = orbits
                            .iter()
                            .copied()
                            .min_by(|a, b| a.1.total_cmp(&b.1))
                            .unwrap();
                        let orbit_report: alloc::string::String = orbits
                            .iter()
                            .map(|(c, ms)| format!("c{c}={ms:.3} "))
                            .collect();
                        println!(
                            "{curve} {corpus} terms={terms:>6} threads={threads:>2} \
                             booth(b{booth_bits})={booth:.3}ms {orbit_report}| \
                             best-orbit=c{best_c} speedup={:+.1}% plan={plan:?}",
                            (booth / best_orbit - 1.0) * 100.0,
                        );
                    };
                    #[cfg(feature = "multicore")]
                    pool.install(body);
                    #[cfg(not(feature = "multicore"))]
                    body();
                }
            }
        }

        run::<vesta::Point>("vesta");
        run::<pallas::Point>("pallas");
    }
}
