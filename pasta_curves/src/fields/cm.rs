//! Quadratic CM/AMNS arithmetic kernel for the Pasta base fields.
//!
//! This module implements field arithmetic in the ring
//! $R = \mathbb{Z}[\sigma]/(\sigma^2 - 3\sigma + 3)$: for each Pasta modulus
//! $r \in \{p, q\}$ there is a generator $g = t + m\sigma$ with
//! $\mathrm{Norm}(g) = t^2 + 3tm + 3m^2 = r$, so $\mathbb{F}_r \cong R/(g)$.
//! A coefficient pair $(a, b)$ stored in the four `u64` limbs of `Fp`/`Fq`
//! (limbs `[0..2]` = `a`, limbs `[2..4]` = `b`, each a two's-complement
//! `i128`) represents the field element $x$ with
//!
//! $$ a + b\sigma \equiv \beta x \pmod g, \qquad \beta = 2^{131}. $$
//!
//! Storage invariant, re-established by every public operation:
//!
//! $$ |a| < 31 \cdot 2^{122}, \qquad |b| < 3 \cdot 2^{124}. $$
//!
//! Multiplication is a Karatsuba ring product ($u = ac$, $v = bd$,
//! $w = (a+b)(c+d)$; $V_0 = u - 3v$, $V_1 = w - u + 2v$; nine full 64×64
//! word products) followed by a two-pass reduction by $\beta = 8 M$,
//! $M = 2^{128}$:
//!
//! 1. a Montgomery-style pass modulo $M$ using $I = g^{-1} \bmod M$:
//!    $q = -VI \bmod M$ (coefficients reinterpreted centered in
//!    $[-2^{127}, 2^{127})$), then $W = (V + qg)/M$ exactly;
//! 2. the **adapted-basis 3-bit lift**: because $g \equiv 1 \pmod 8$
//!    (const-asserted below), the second-pass quotient is
//!    $s \equiv -W \pmod 8$; the full quotient $Q = q + Ms$ must be centered
//!    in the *adapted* basis $Q = X + Y(\sigma - 3)$ with
//!    $X, Y \in [-\beta/2, \beta/2)$ — NOT centered coefficientwise, which
//!    would break the closure proof. Then $Z = (W + sg)/8$ exactly, with
//!    $|Z_0| \le 0.95106 \cdot 2^{127}$ and $|Z_1| \le 0.36046 \cdot 2^{127}$,
//!    inside the storage invariant.
//!
//! Addition and subtraction re-establish the invariant with at most one
//! correction by $w_2 = (\sigma - 3)g = (-3m_0, t)$ (keyed on
//! $2a \gtrless \pm 3m_0$) followed by at most one correction by
//! $w_1 = g = (t, m)$ (keyed on $2b \gtrless \pm m$), all branchless.
//!
//! The representation is redundant: representatives may differ by lattice
//! vectors of $\Lambda = \mathbb{Z}w_1 + \mathbb{Z}w_2$. Equality therefore
//! must NOT compare stored limbs; use [`is_zero_raw`] on a normalized
//! difference — $(0, 0)$ is the only lattice point inside the normalizer's
//! output box (pinned by tests below).
//!
//! Every operation here is constant-time: the only data-dependent `if` in
//! this module is on compile-time associated constants; all other selection
//! is borrow/sign-derived mask arithmetic. (Inversion is not implemented
//! here; the crate's `modinv62` remains the — documented variable-time —
//! inversion.)
//!
//! Constants are generated and cross-checked by `sage/cm_constants.sage`
//! and re-verified by the compile-time assertions and unit tests below.
#![allow(dead_code)] // TODO(M3): remove when Fp/Fq route through this kernel.

use subtle::{Choice, ConstantTimeEq};

/// An upstream-style verification check: live in unit tests (including
/// `--release` runs, where `debug_assert!` would be inert) and in debug
/// builds; compiled out of production builds. Messages must be string
/// literals so the checks stay legal inside `const fn`s.
macro_rules! verify {
    ($cond:expr, $msg:literal) => {
        #[cfg(any(test, debug_assertions))]
        {
            assert!($cond, $msg);
        }
    };
}

/// Per-field CM/AMNS constants. Values are printed by
/// `sage/cm_constants.sage`; every one is pinned by [`check_params`] or a
/// unit test. Sign convention: `M > 0`, `M0 > 0`, `T` signed;
/// `T ≡ 1 (mod 8)` and `M ≡ 0 (mod 8)` select the unique unit associate of
/// the generator for which the 3-bit lift below is valid.
pub(crate) trait CmParams {
    /// $t$: the rational coefficient of $g = t + m\sigma$.
    const T: i128;
    /// $m$: the $\sigma$ coefficient of $g$.
    const M: i128;
    /// $m_0 = t + m$, so that $w_2 = (\sigma - 3)g = (-3m_0, t)$.
    const M0: i128;
    /// $I_0$: rational coefficient of $g^{-1} \bmod 2^{128}$.
    const I0: u128;
    /// $I_1$: $\sigma$ coefficient of $g^{-1} \bmod 2^{128}$.
    const I1: u128;
    /// The CM encoding of the field element 1, i.e. a reduced representative
    /// of $\beta = 2^{131}$.
    const ONE: (i128, i128);
    /// The canonical modulus $r$, four little-endian `u64` limbs.
    const MODULUS_LIMBS: [u64; 4];
    /// $c = r - 2^{254}$ (126 bits), for the Solinas folds in conversion.
    const SOLINAS_C: u128;
    /// The canonical embedding of $\sigma$ (little-endian limbs).
    const SIGMA: [u64; 4];
    /// $\beta^{-1} \bmod r$ (little-endian limbs).
    const BETA_INV: [u64; 4];
    /// $\sigma \beta^{-1} \bmod r$ (little-endian limbs).
    const SIGMA_BETA_INV: [u64; 4];
    /// $\mathrm{round}(2^{512} |t| / r)$: Babai rounding constant for the
    /// canonical→CM conversion, 512 fractional bits (little-endian limbs).
    /// 384 bits (the GLV scale) is NOT enough here: a ±1 rounding slip adds
    /// $3m_0 \approx 1.73 \cdot 2^{127}$ to `a` and breaks the invariant,
    /// while at $2^{512}$ scale slips are impossible (the perturbation is
    /// below $1/(2r)$ and $r$ is odd, so no ties exist).
    const G_T: [u64; 7];
    /// $\mathrm{round}(2^{512} m / r)$ (little-endian limbs).
    const G_M: [u64; 7];
}

/// [`CmParams`] for the Pallas base field (`Fp`). Here $\sigma = \zeta + 2$
/// for the crate's `Fp::ZETA`.
pub(crate) struct FpParams;

impl CmParams for FpParams {
    const T: i128 = -0x47afc1f319ba33ffffffff;
    const M: i128 = 0x49e69d1640f049157fcae1c700000000;
    const M0: i128 = 0x49e69d1640a899538cb1279300000001;
    const I0: u128 = 0x4a9b1320085d103ef319ba3400000001;
    const I1: u128 = 0xd36d32beb7330c2580351e3900000000;
    const ONE: (i128, i128) = (
        0x34ad6ea72e37d4302950d37effffffe5,
        -0x02852dd18be78bd3fffffff7,
    );
    const MODULUS_LIMBS: [u64; 4] = [
        0x992d30ed00000001,
        0x224698fc094cf91b,
        0x0000000000000000,
        0x4000000000000000,
    ];
    const SOLINAS_C: u128 = 0x224698fc094cf91b992d30ed00000001;
    const SIGMA: [u64; 4] = [
        0x1dad5ebdfdfe4abb,
        0x1d1f8bd237ad3149,
        0x2caad5dc57aab1b0,
        0x12ccca834acdba71,
    ];
    const BETA_INV: [u64; 4] = [
        0x06fb93ea881bb2ce,
        0x137a278f8b909132,
        0x94c9698768000000,
        0x334e3b05ec1509ed,
    ];
    const SIGMA_BETA_INV: [u64; 4] = [
        0x750a8c89027d7729,
        0x36f71184bb26af55,
        0xecd4ff0308100daa,
        0x178e1780b9001a4c,
    ];
    const G_T: [u64; 7] = [
        0x83e2d25185776b37,
        0xa4f318e582b4b234,
        0x7bf563dd917ae05d,
        0xffffffffff666e35,
        0xcc66e8cffffffffb,
        0x00000000011ebf07,
        0x0000000000000000,
    ];
    const G_M: [u64; 7] = [
        0x53555a06a5b38f4a,
        0x7022eb26339b15cb,
        0x0009789fdd747ae0,
        0x61afdea6853283ae,
        0xff2b871bffffffff,
        0x279a745903c12455,
        0x0000000000000001,
    ];
}

/// [`CmParams`] for the Vesta base field (`Fq`). Here $\sigma = \zeta^2 + 2$
/// for the crate's `Fq::ZETA` — the conjugate root is the one whose reduced
/// generator has small $t$ with $t \equiv 1, m \equiv 0 \pmod 8$.
pub(crate) struct FqParams;

impl CmParams for FqParams {
    const T: i128 = 0x47afc1f319ba3400000001;
    const M: i128 = 0x49e69d1640a899538cb1279300000000;
    const M0: i128 = 0x49e69d1640f049157fcae1c700000001;
    const I0: u128 = 0xb740293c07238f930ce645cc00000001;
    const I1: u128 = 0xcce55a7eb7b3719f734ed86d00000000;
    const ONE: (i128, i128) = (
        0x34ad6ea726a84abb859a3002ffffffe5,
        0x02852dd18be78bd400000009,
    );
    const MODULUS_LIMBS: [u64; 4] = [
        0x8c46eb2100000001,
        0x224698fc0994a8dd,
        0x0000000000000000,
        0x4000000000000000,
    ];
    const SOLINAS_C: u128 = 0x224698fc0994a8dd8c46eb2100000001;
    const SIGMA: [u64; 4] = [
        0x619d1840af55f1b3,
        0x1259527ec1d4752e,
        0xaee24b27e308f0a6,
        0x397e65a7d7c1ad71,
    ];
    const BETA_INV: [u64; 4] = [
        0x65287d2a9fd79077,
        0x154d2d193d152906,
        0xe462375908000000,
        0x36b641d48c1c9874,
    ];
    const SIGMA_BETA_INV: [u64; 4] = [
        0x6e7d70b8ff7f99fd,
        0x7f0461749a48c3bb,
        0xf0c2430692855072,
        0x1d8f0325dfc51086,
    ];
    const G_T: [u64; 7] = [
        0x2ca2697876ddda24,
        0xcb24b19a7b20e9a2,
        0x7bf422ae2d81872a,
        0xffffffffff666e35,
        0xcc66e8d000000003,
        0x00000000011ebf07,
        0x0000000000000000,
    ];
    const G_M: [u64; 7] = [
        0x1d2869965f2a237a,
        0x03d843e6359b1ee0,
        0x4a95a2d972171db4,
        0x61afdea68480fa55,
        0x32c49e4bffffffff,
        0x279a745902a2654e,
        0x0000000000000001,
    ];
}

/// Storage bound on `|a|`.
pub(crate) const A_BOUND: u128 = 31 << 122;
/// Storage bound on `|b|`.
pub(crate) const B_BOUND: u128 = 3 << 124;

/// `|x|` as a `u128` without relying on `unsigned_abs` const-stability.
#[inline(always)]
const fn abs_i128(x: i128) -> u128 {
    let m = (x >> 127) as u128;
    ((x as u128) ^ m).wrapping_add(m & 1)
}

/// `true` iff the pair satisfies the storage invariant.
pub(crate) const fn in_bounds(x: (i128, i128)) -> bool {
    abs_i128(x.0) < A_BOUND && abs_i128(x.1) < B_BOUND
}

/// Compile-time pinning of every arithmetic-critical parameter relation.
const fn check_params<P: CmParams>() {
    assert!(P::M > 0, "M must be positive");
    assert!(P::M0 > 0, "M0 must be positive");
    assert!(P::M0 == P::T + P::M, "M0 must equal T + M");
    assert!(P::T.rem_euclid(8) == 1, "T must be 1 mod 8");
    assert!(P::M % 8 == 0, "M must be 0 mod 8");
    assert!(P::M0 % 2 == 1, "M0 must be odd (no a-threshold ties)");

    // Norm identity: T^2 + 3TM + 3M^2 == r, evaluated in 256 bits.
    let norm = w256_add(
        smul_i128(P::T, P::T),
        w256_mul3(w256_add(smul_i128(P::T, P::M), smul_i128(P::M, P::M))),
    );
    let r_lo = (P::MODULUS_LIMBS[0] as u128) | ((P::MODULUS_LIMBS[1] as u128) << 64);
    let r_hi = (P::MODULUS_LIMBS[2] as u128) | ((P::MODULUS_LIMBS[3] as u128) << 64);
    assert!(norm.lo == r_lo && norm.hi == r_hi, "norm(g) must equal r");

    // r == 2^254 + SOLINAS_C.
    let c_plus = w256_add(
        W256 {
            lo: P::SOLINAS_C,
            hi: 0,
        },
        W256 {
            lo: 0,
            hi: 1 << 126,
        },
    );
    assert!(c_plus.lo == r_lo && c_plus.hi == r_hi, "r must be 2^254 + c");

    // g * I == 1 in R/2^128 (two's-complement wrapping arithmetic is exact
    // modulo 2^128, so the signed T folds in automatically).
    let (i0, i1) = ring_mul_low(P::T as u128, P::M as u128, P::I0, P::I1);
    assert!(i0 == 1 && i1 == 0, "I must invert g modulo 2^128");

    // ONE must satisfy the storage invariant.
    assert!(in_bounds(P::ONE), "ONE must satisfy the storage invariant");
}

const _: () = {
    check_params::<FpParams>();
    check_params::<FqParams>();
};

// ---------------------------------------------------------------------------
// Wide-integer primitives.
// ---------------------------------------------------------------------------

/// A 256-bit two's-complement value, `hi * 2^128 + lo` with wrapping
/// semantics. Intermediates may wrap; every final value read out of a `W256`
/// is bounds-checked by a `verify!`.
#[derive(Clone, Copy)]
struct W256 {
    lo: u128,
    hi: u128,
}

const W256_ZERO: W256 = W256 { lo: 0, hi: 0 };

#[inline(always)]
const fn w256_add(a: W256, b: W256) -> W256 {
    let (lo, carry) = a.lo.overflowing_add(b.lo);
    W256 {
        lo,
        hi: a.hi.wrapping_add(b.hi).wrapping_add(carry as u128),
    }
}

#[inline(always)]
const fn w256_sub(a: W256, b: W256) -> W256 {
    let (lo, borrow) = a.lo.overflowing_sub(b.lo);
    W256 {
        lo,
        hi: a.hi.wrapping_sub(b.hi).wrapping_sub(borrow as u128),
    }
}

/// Conditionally negates: `mask` must be all-ones (negate) or all-zeros.
#[inline(always)]
const fn w256_cond_neg(a: W256, mask: u128) -> W256 {
    let (lo, carry) = (a.lo ^ mask).overflowing_add(mask & 1);
    W256 {
        lo,
        hi: (a.hi ^ mask).wrapping_add(carry as u128),
    }
}

#[inline(always)]
const fn w256_shl1(a: W256) -> W256 {
    W256 {
        lo: a.lo << 1,
        hi: (a.hi << 1) | (a.lo >> 127),
    }
}

/// `3 * a` (used for every ×3 in the ring formulas).
#[inline(always)]
const fn w256_mul3(a: W256) -> W256 {
    w256_add(a, w256_shl1(a))
}

/// Sign-extends an `i128` to 256 bits.
#[inline(always)]
const fn w256_from_i128(x: i128) -> W256 {
    W256 {
        lo: x as u128,
        hi: (x >> 127) as u128,
    }
}

/// `x * 2^128` for a small non-negative `x`.
#[inline(always)]
const fn w256_shl128(x: u64) -> W256 {
    W256 {
        lo: 0,
        hi: x as u128,
    }
}

/// Exact arithmetic shift right by 128: the low half must be zero. Only
/// valid when the operand's true value fits 256 signed bits (the lift's
/// small differences); for the pass-1 `(V + q·g)/M`, whose sum spans 257
/// bits, use [`w256_add_asr128_exact`].
#[inline(always)]
const fn w256_asr128_exact(a: W256) -> W256 {
    verify!(a.lo == 0, "division by 2^128 must be exact");
    W256 {
        lo: a.hi,
        hi: ((a.hi as i128) >> 127) as u128,
    }
}

/// `(a + b) / 2^128`, exact: the low halves must cancel to zero. The true
/// sum can span 257 bits (`|V0 + (q·g)0|` reaches ~1.55·2^255), so the
/// quotient is reassembled from the high limbs with signed-carry extension
/// instead of materializing the sum in a 256-bit register pair.
#[inline(always)]
const fn w256_add_asr128_exact(a: W256, b: W256) -> W256 {
    let (lo, carry) = a.lo.overflowing_add(b.lo);
    verify!(lo == 0, "division by 2^128 must be exact");
    let (wlo, c1) = a.hi.overflowing_add(b.hi);
    let (wlo, c2) = wlo.overflowing_add(carry as u128);
    let whi = ((a.hi as i128) >> 127) + ((b.hi as i128) >> 127) + c1 as i128 + c2 as i128;
    W256 {
        lo: wlo,
        hi: whi as u128,
    }
}

/// A 320-bit signed value (`ext·2^256 + hi·2^128 + lo`) for the one place a
/// two's-complement 256-bit register pair is not enough as a *stored* value:
/// the σ-component of `q·g`, whose magnitude reaches
/// `2^127·(4m + |t|) ≈ 2.31·2^254 > 2^255`.
#[derive(Clone, Copy)]
struct W320 {
    lo: u128,
    hi: u128,
    ext: i128,
}

#[inline(always)]
const fn w320_from(a: W256) -> W320 {
    W320 {
        lo: a.lo,
        hi: a.hi,
        ext: (a.hi as i128) >> 127,
    }
}

#[inline(always)]
const fn w320_add(a: W320, b: W320) -> W320 {
    let (lo, c0) = a.lo.overflowing_add(b.lo);
    let (hi, c1) = a.hi.overflowing_add(b.hi);
    let (hi, c2) = hi.overflowing_add(c0 as u128);
    W320 {
        lo,
        hi,
        ext: a.ext + b.ext + c1 as i128 + c2 as i128,
    }
}

#[inline(always)]
const fn w320_sub(a: W320, b: W320) -> W320 {
    let (lo, b0) = a.lo.overflowing_sub(b.lo);
    let (hi, b1) = a.hi.overflowing_sub(b.hi);
    let (hi, b2) = hi.overflowing_sub(b0 as u128);
    W320 {
        lo,
        hi,
        ext: a.ext - b.ext - b1 as i128 - b2 as i128,
    }
}

#[inline(always)]
const fn w320_shl1(a: W320) -> W320 {
    W320 {
        lo: a.lo << 1,
        hi: (a.hi << 1) | (a.lo >> 127),
        ext: (a.ext << 1) | ((a.hi >> 127) as i128),
    }
}

/// Exact division by 2^128 of a 320-bit value whose quotient fits a `W256`.
#[inline(always)]
const fn w320_asr128_exact(a: W320) -> W256 {
    verify!(a.lo == 0, "division by 2^128 must be exact");
    W256 {
        lo: a.hi,
        hi: a.ext as u128,
    }
}

/// Exact arithmetic shift right by 3: the low three bits must be zero.
#[inline(always)]
const fn w256_asr3_exact(a: W256) -> W256 {
    verify!(a.lo & 7 == 0, "division by 8 must be exact");
    W256 {
        lo: (a.lo >> 3) | (a.hi << 125),
        hi: ((a.hi as i128) >> 3) as u128,
    }
}

/// Reads a value that must fit in `i128` (the high half must be the sign
/// extension of the low half).
#[inline(always)]
const fn w256_low_i128(a: W256) -> i128 {
    verify!(
        a.hi == (((a.lo as i128) >> 127) as u128),
        "value must fit in i128"
    );
    a.lo as i128
}

/// Centers modulo `2^131`: returns the representative in
/// `[-2^130, 2^130)` congruent to `a` modulo `2^131`.
#[inline(always)]
const fn w256_center131(a: W256) -> W256 {
    const HALF: W256 = W256 { lo: 0, hi: 4 }; // 2^130
    let t = w256_add(a, HALF);
    let masked = W256 {
        lo: t.lo,
        hi: t.hi & 7, // keep 131 bits total
    };
    w256_sub(masked, HALF)
}

/// A sign/magnitude transient for the sum of two `i128`s. The magnitude is
/// `top * 2^128 + lo`; `top` covers the single corner `|x + y| = 2^128`
/// (reachable in reduction pass 1 when both centered quotient coefficients
/// are `i128::MIN`), which a plain `(bool, u128)` would silently truncate.
#[derive(Clone, Copy)]
struct Sm129 {
    neg: bool,
    top: bool,
    lo: u128,
}

#[inline(always)]
const fn sm129_from_sum(x: i128, y: i128) -> Sm129 {
    let (lo, carry) = (x as u128).overflowing_add(y as u128);
    // hi ∈ {-1, 0} because |x + y| <= 2^128.
    let hi = (x >> 127) + (y >> 127) + carry as i128;
    verify!(hi == 0 || hi == -1, "129-bit sum out of range");
    let mask = hi as u128; // all-ones iff negative
    let mag_lo = (lo ^ mask).wrapping_add(mask & 1);
    // top is set only for the exact value -2^128 (negative with lo == 0).
    let lo_nonzero = (lo | lo.wrapping_neg()) >> 127; // 1 iff lo != 0
    let top = (mask & (lo_nonzero ^ 1)) & 1 == 1;
    Sm129 {
        neg: hi < 0,
        top,
        lo: mag_lo,
    }
}

// ---------------------------------------------------------------------------
// Word products.
// ---------------------------------------------------------------------------

/// `(|a - b|, a < b)` without branches.
#[inline(always)]
const fn abs_diff64(a: u64, b: u64) -> (u64, bool) {
    let (d, borrow) = a.overflowing_sub(b);
    let m = (borrow as u64).wrapping_neg();
    ((d ^ m).wrapping_add(m & 1), borrow)
}

/// Full unsigned 128×128→256 product via subtractive Karatsuba: exactly
/// three full 64×64 word products (`a0·b0`, `a1·b1`, `|a0−a1|·|b1−b0|`).
#[inline(always)]
const fn mul_u128_wide(a: u128, b: u128) -> W256 {
    let a0 = a as u64;
    let a1 = (a >> 64) as u64;
    let b0 = b as u64;
    let b1 = (b >> 64) as u64;

    let z0 = (a0 as u128) * (b0 as u128);
    let z2 = (a1 as u128) * (b1 as u128);
    let (da, sa) = abs_diff64(a0, a1);
    let (db, sb) = abs_diff64(b1, b0);
    let zm = (da as u128) * (db as u128);

    // mid = a0·b1 + a1·b0 = z0 + z2 + (a0−a1)(b1−b0), in [0, 2^129).
    let (s, c1) = z0.overflowing_add(z2);
    let neg = sa ^ sb; // sign of (a0−a1)(b1−b0)
    let mask = (neg as u128).wrapping_neg();
    let zm_signed = (zm ^ mask).wrapping_add(mask & 1);
    let (mid_lo, c2) = s.overflowing_add(zm_signed);
    // mid_hi = c1 + c2 − [δ was actually subtracted] ∈ {0, 1}. The borrow
    // applies only when zm != 0: negating a zero δ wraps back to zero and
    // must not charge the phantom 2^128.
    let zm_nonzero = (zm | zm.wrapping_neg()) >> 127; // 1 iff zm != 0
    let mid_hi = (c1 as u128)
        .wrapping_add(c2 as u128)
        .wrapping_sub((neg as u128) & zm_nonzero);
    verify!(mid_hi <= 1, "Karatsuba middle limb out of range");

    let (lo, c3) = z0.overflowing_add(mid_lo << 64);
    let hi = z2
        .wrapping_add(mid_lo >> 64)
        .wrapping_add(mid_hi << 64)
        .wrapping_add(c3 as u128);
    W256 { lo, hi }
}

/// Full unsigned 128-bit square: three word products
/// (`a0²`, `a1²`, `a0·a1` with the middle doubled).
#[inline(always)]
const fn square_u128_wide(a: u128) -> W256 {
    let a0 = a as u64;
    let a1 = (a >> 64) as u64;

    let z0 = (a0 as u128) * (a0 as u128);
    let z2 = (a1 as u128) * (a1 as u128);
    let cross = (a0 as u128) * (a1 as u128);

    // mid = 2·a0·a1 < 2^129.
    let mid_lo = cross << 1;
    let mid_hi = cross >> 127;

    let (lo, c3) = z0.overflowing_add(mid_lo << 64);
    let hi = z2
        .wrapping_add(mid_lo >> 64)
        .wrapping_add(mid_hi << 64)
        .wrapping_add(c3 as u128);
    W256 { lo, hi }
}

/// Full signed 128×128→256 product: magnitudes multiply, signs XOR.
#[inline(always)]
const fn smul_i128(x: i128, y: i128) -> W256 {
    let sx = (x >> 127) as u128;
    let sy = (y >> 127) as u128;
    let mx = ((x as u128) ^ sx).wrapping_add(sx & 1);
    let my = ((y as u128) ^ sy).wrapping_add(sy & 1);
    w256_cond_neg(mul_u128_wide(mx, my), sx ^ sy)
}

/// Product of two [`Sm129`] transients whose magnitudes fit 128 bits (the
/// ring-multiply cross terms: `|a+b| <= 43·2^122 < 2^128`).
#[inline(always)]
const fn smul_sm_pair(x: Sm129, y: Sm129) -> W256 {
    verify!(!x.top && !y.top, "cross-term magnitude must fit 128 bits");
    let p = mul_u128_wide(x.lo, y.lo);
    w256_cond_neg(p, ((x.neg ^ y.neg) as u128).wrapping_neg())
}

/// `x * M0` for an [`Sm129`] `x` whose magnitude may be exactly `2^128`
/// (the pass-1 `q0 + q1` transient). `M0 > 0` is const-asserted.
#[inline(always)]
const fn smul_sm_m0<P: CmParams>(x: Sm129) -> W256 {
    let p = mul_u128_wide(x.lo, P::M0 as u128);
    let top_mask = (x.top as u128).wrapping_neg();
    let p = W256 {
        lo: p.lo,
        hi: p.hi.wrapping_add(top_mask & (P::M0 as u128)),
    };
    w256_cond_neg(p, (x.neg as u128).wrapping_neg())
}

/// Truncated ring product modulo `2^128` (reduction pass 1): three
/// `u128` low multiplications; wrapping arithmetic is exact mod `2^128`.
#[inline(always)]
const fn ring_mul_low(x0: u128, x1: u128, y0: u128, y1: u128) -> (u128, u128) {
    let u = x0.wrapping_mul(y0);
    let v = x1.wrapping_mul(y1);
    let w = x0.wrapping_add(x1).wrapping_mul(y0.wrapping_add(y1));
    (
        u.wrapping_sub(v.wrapping_mul(3)),
        w.wrapping_sub(u).wrapping_add(v.wrapping_mul(2)),
    )
}

// ---------------------------------------------------------------------------
// Ring products (raw, unreduced).
// ---------------------------------------------------------------------------

/// Karatsuba recombination shared by the raw product and pass 1's `q·g`:
/// `(u − 3v, w − u + 2v)`. Intermediates may wrap; the final values fit
/// signed 256 bits by the operand bounds.
#[inline(always)]
const fn karatsuba_combine(u: W256, v: W256, w: W256) -> (W256, W256) {
    (
        w256_sub(u, w256_mul3(v)),
        w256_add(w256_sub(w, u), w256_shl1(v)),
    )
}

/// Raw ring product of `(a + bσ)(c + dσ)`: `u = ac`, `v = bd`,
/// `w = (a+b)(c+d)` (the sums via [`Sm129`]: they can exceed `i128`);
/// `V0 = u − 3v`, `V1 = w − u + 2v`. Nine full 64×64 word products.
#[inline(always)]
const fn ring_mul_wide(a: i128, b: i128, c: i128, d: i128) -> (W256, W256) {
    let u = smul_i128(a, c);
    let v = smul_i128(b, d);
    let w = smul_sm_pair(sm129_from_sum(a, b), sm129_from_sum(c, d));
    karatsuba_combine(u, v, w)
}

/// Raw ring square: `V0 = a² − 3b²`, `V1 = 2ab + 3b²` (two squares and one
/// signed product).
#[inline(always)]
const fn ring_square_wide(a: i128, b: i128) -> (W256, W256) {
    let sa = (a >> 127) as u128;
    let sb = (b >> 127) as u128;
    let za = square_u128_wide(((a as u128) ^ sa).wrapping_add(sa & 1));
    let zb = square_u128_wide(((b as u128) ^ sb).wrapping_add(sb & 1));
    let cross = smul_i128(a, b);
    (
        w256_sub(za, w256_mul3(zb)),
        w256_add(w256_shl1(cross), w256_mul3(zb)),
    )
}

// ---------------------------------------------------------------------------
// The two-pass reducer.
// ---------------------------------------------------------------------------

/// The corrected adapted-basis 3-bit lift (pass 2), factored out for
/// exhaustive testing. Given the pass-1 centered quotient `(q0, q1)` and the
/// low words of `W = (V + qg)/M`, returns the standard-basis second-pass
/// quotient `(s0, s1)` with `s ≡ −W (mod 8)` coefficientwise (valid because
/// `g ≡ 1 (mod 8)`), such that the FULL quotient `Q = q + M·s` is centered
/// in the adapted basis: `Q = X + Y(σ−3)` with `X, Y ∈ [−2^130, 2^130)`.
/// Ranges: `s0 ∈ [−16, 16]`, `s1 ∈ [−4, 4]`.
#[inline(always)]
const fn lift_adapted(q0: i128, q1: i128, w0_low: u64, w1_low: u64) -> (i128, i128) {
    let xs = w0_low.wrapping_add(w1_low.wrapping_mul(3)).wrapping_neg() & 7;
    let ys = w1_low.wrapping_neg() & 7;

    let q0w = w256_from_i128(q0);
    let q1w = w256_from_i128(q1);
    // X = center(q0 + 3q1 + M·xs), Y = center(q1 + M·ys), both mod β = 2^131.
    let x = w256_center131(w256_add(w256_add(q0w, w256_mul3(q1w)), w256_shl128(xs)));
    let y = w256_center131(w256_add(q1w, w256_shl128(ys)));
    // s1 = (Y − q1)/M and s0 = (X − 3Y − q0)/M, both exact.
    let s1 = w256_low_i128(w256_asr128_exact(w256_sub(y, q1w)));
    let s0 = w256_low_i128(w256_asr128_exact(w256_sub(w256_sub(x, w256_mul3(y)), q0w)));
    verify!(s0 >= -16 && s0 <= 16, "s0 out of range");
    verify!(s1 >= -4 && s1 <= 4, "s1 out of range");
    (s0, s1)
}

/// Reduction by `β = 2^131`: given the raw ring product `V` with
/// `|V0| <= A² + 3B²` and `|V1| <= 2AB + 3B²`, returns `Z ≡ V·β⁻¹ (mod g)`
/// within the storage invariant.
#[cfg_attr(not(feature = "uninline-portable"), inline)]
const fn reduce<P: CmParams>(v0: W256, v1: W256) -> (i128, i128) {
    // ---- Pass 1: divide by M = 2^128. ----
    // q = −V·g⁻¹ mod M; the u128→i128 reinterpretation IS the centering
    // into [−2^127, 2^127).
    let (n0, n1) = ring_mul_low(v0.lo, v1.lo, P::I0, P::I1);
    let q0 = n0.wrapping_neg() as i128;
    let q1 = n1.wrapping_neg() as i128;

    // q·g by the same Karatsuba shape: u = q0·T, v = q1·M, w = (q0+q1)·M0.
    // The rational component (q·g)0 = u − 3v fits a signed 256-bit value
    // (≤ 1.73·2^254); the σ-component (q·g)1 = w − u + 2v does NOT
    // (≤ 2.31·2^254), so that lane carries a 320-bit extension.
    let u = smul_i128(q0, P::T);
    let v = smul_i128(q1, P::M);
    let w = smul_sm_m0::<P>(sm129_from_sum(q0, q1));
    let qg0 = w256_sub(u, w256_mul3(v));
    let qg1 = w320_add(w320_sub(w320_from(w), w320_from(u)), w320_shl1(w320_from(v)));

    // W = (V + q·g)/M, exact. NOTE: |W| can reach ~2^128.8 (it does NOT fit
    // i128); the fused/W320 helpers keep the sum's bits beyond 2^255.
    let w0 = w256_add_asr128_exact(v0, qg0);
    let w1 = w320_asr128_exact(w320_add(w320_from(v1), qg1));

    // ---- Pass 2: the adapted 3-bit lift, then divide by 8. ----
    let (s0, s1) = lift_adapted(q0, q1, w0.lo as u64, w1.lo as u64);

    // s·g = (s0·T − 3·s1·M, s0·M + s1·T + 3·s1·M).
    let s1m3 = w256_mul3(smul_i128(s1, P::M));
    let sg0 = w256_sub(smul_i128(s0, P::T), s1m3);
    let sg1 = w256_add(w256_add(smul_i128(s0, P::M), smul_i128(s1, P::T)), s1m3);

    let z0 = w256_low_i128(w256_asr3_exact(w256_add(w0, sg0)));
    let z1 = w256_low_i128(w256_asr3_exact(w256_add(w1, sg1)));
    verify!(
        abs_i128(z0) < A_BOUND && abs_i128(z1) < B_BOUND,
        "reduction closure violated"
    );
    (z0, z1)
}

// ---------------------------------------------------------------------------
// Public kernel operations.
// ---------------------------------------------------------------------------

/// Field multiplication on coefficient pairs.
#[cfg_attr(not(feature = "uninline-portable"), inline)]
pub(crate) const fn mul<P: CmParams>(x: (i128, i128), y: (i128, i128)) -> (i128, i128) {
    verify!(in_bounds(x) && in_bounds(y), "mul operand out of bounds");
    let (v0, v1) = ring_mul_wide(x.0, x.1, y.0, y.1);
    reduce::<P>(v0, v1)
}

/// Field squaring on coefficient pairs (dedicated formula).
#[cfg_attr(not(feature = "uninline-portable"), inline)]
pub(crate) const fn square<P: CmParams>(x: (i128, i128)) -> (i128, i128) {
    verify!(in_bounds(x), "square operand out of bounds");
    let (v0, v1) = ring_square_wide(x.0, x.1);
    reduce::<P>(v0, v1)
}

/// A 129(+)-bit two's-complement transient for the normalizer lane whose
/// comparisons and sums can exceed `i128` (both the `a`-lane sum and the
/// `b`-lane threshold compare — the latter overflows `i128` for boundary
/// operands, so both lanes run through this type).
#[derive(Clone, Copy)]
struct S129 {
    lo: u128,
    hi: i128, // small signed extension; value = hi·2^128 + lo
}

#[inline(always)]
const fn s129_from_i128(x: i128) -> S129 {
    S129 {
        lo: x as u128,
        hi: x >> 127,
    }
}

#[inline(always)]
const fn s129_from_sum(x: i128, y: i128) -> S129 {
    let (lo, carry) = (x as u128).overflowing_add(y as u128);
    S129 {
        lo,
        hi: (x >> 127) + (y >> 127) + carry as i128,
    }
}

#[inline(always)]
const fn s129_from_diff(x: i128, y: i128) -> S129 {
    let (lo, borrow) = (x as u128).overflowing_sub(y as u128);
    S129 {
        lo,
        hi: (x >> 127) - (y >> 127) - borrow as i128,
    }
}

/// All-ones iff `x > c` (borrow-derived, branchless).
#[inline(always)]
const fn s129_gt_mask(x: S129, c: i128) -> u128 {
    // d = c − x; x > c ⟺ d < 0 ⟺ sign(d.hi) set.
    let (_, borrow) = (c as u128).overflowing_sub(x.lo);
    let dhi = (c >> 127) - x.hi - borrow as i128;
    ((dhi >> 127) as i128) as u128
}

/// All-ones iff `x < c`.
#[inline(always)]
const fn s129_lt_mask(x: S129, c: i128) -> u128 {
    // d = x − c; x < c ⟺ d < 0.
    let (_, borrow) = x.lo.overflowing_sub(c as u128);
    let dhi = x.hi - (c >> 127) - borrow as i128;
    ((dhi >> 127) as i128) as u128
}

/// `x + (m & mask)` for a positive magnitude `m < 2^128`.
#[inline(always)]
const fn s129_add_masked(x: S129, m: u128, mask: u128) -> S129 {
    let (lo, carry) = x.lo.overflowing_add(m & mask);
    S129 {
        lo,
        hi: x.hi + carry as i128,
    }
}

/// `x − (m & mask)` for a positive magnitude `m < 2^128`.
#[inline(always)]
const fn s129_sub_masked(x: S129, m: u128, mask: u128) -> S129 {
    let (lo, borrow) = x.lo.overflowing_sub(m & mask);
    S129 {
        lo,
        hi: x.hi - borrow as i128,
    }
}

#[inline(always)]
const fn s129_to_i128(x: S129) -> i128 {
    verify!(
        x.hi == ((x.lo as i128) >> 127),
        "S129 value must fit in i128"
    );
    x.lo as i128
}

/// `(v & mask)` as a signed value, for a two's-complement `v` and an
/// all-ones/all-zeros `mask` (select `v` or `0`).
#[inline(always)]
const fn i128_and_mask(v: i128, mask: u128) -> i128 {
    ((v as u128) & mask) as i128
}

/// The branchless lattice normalizer: at most one `w2 = (−3m0, t)`
/// correction keyed on `2a ≷ ±3m0`, then at most one `w1 = (t, m)`
/// correction keyed on `2b ≷ ±m`. Since `3m0` is odd and `m` is even
/// (const-asserted), the thresholds are exactly `a ≷ ±⌊3m0/2⌋` (strict)
/// and `b ≥ m/2` / `b < −m/2`.
///
/// Domain: `|a| ≤ 2·A_BOUND` (as an [`S129`]), `|b| ≤ 2·B_BOUND`.
/// Postcondition: `|a| ≤ 3m0/2 + 2|t|`, `|b| ≤ m/2` — comfortably inside
/// the storage invariant.
#[inline(always)]
const fn normalize<P: CmParams>(a: S129, b: i128) -> (i128, i128) {
    let three_m0 = 3 * (P::M0 as u128); // < 2^128 (M0 < 2^127)
    let half_3m0 = (three_m0 >> 1) as i128; // ⌊3m0/2⌋ < 2^127
    let half_m = P::M / 2;

    // Phase 1: w2 correction on the a-lane.
    let gt = s129_gt_mask(a, half_3m0); // 2a > 3m0  ⟺  a > ⌊3m0/2⌋
    let lt = s129_lt_mask(a, -half_3m0); // 2a < −3m0 ⟺  a < −⌊3m0/2⌋
    let a = s129_sub_masked(a, three_m0, gt);
    let a = s129_add_masked(a, three_m0, lt);
    let b = b
        .wrapping_add(i128_and_mask(P::T, gt))
        .wrapping_sub(i128_and_mask(P::T, lt));
    let a = s129_to_i128(a); // |a| ≤ ⌊3m0/2⌋ + ... < 2^127 now

    // Phase 2: w1 correction on the b-lane. The compare itself can exceed
    // i128 (|b| up to 2B + |t| vs. threshold m/2), so it runs through S129.
    let bb = s129_from_i128(b);
    let gtb = s129_gt_mask(bb, half_m - 1); // b ≥ m/2 ⟺ b > m/2 − 1
    let ltb = s129_lt_mask(bb, -half_m); // b < −m/2
    let b = b
        .wrapping_sub(i128_and_mask(P::M, gtb))
        .wrapping_add(i128_and_mask(P::M, ltb));
    let a = a
        .wrapping_sub(i128_and_mask(P::T, gtb))
        .wrapping_add(i128_and_mask(P::T, ltb));

    verify!(
        in_bounds((a, b)),
        "normalizer postcondition violated"
    );
    (a, b)
}

/// Field addition on coefficient pairs.
#[cfg_attr(not(feature = "uninline-portable"), inline)]
pub(crate) const fn add<P: CmParams>(x: (i128, i128), y: (i128, i128)) -> (i128, i128) {
    verify!(in_bounds(x) && in_bounds(y), "add operand out of bounds");
    // The a-lane sum can exceed i128 (|a1| + |a2| < 2A); the b-lane sum
    // cannot (|b1| + |b2| < 2B = 0.75·2^127).
    normalize::<P>(s129_from_sum(x.0, y.0), x.1 + y.1)
}

/// Field subtraction on coefficient pairs.
#[cfg_attr(not(feature = "uninline-portable"), inline)]
pub(crate) const fn sub<P: CmParams>(x: (i128, i128), y: (i128, i128)) -> (i128, i128) {
    verify!(in_bounds(x) && in_bounds(y), "sub operand out of bounds");
    normalize::<P>(s129_from_diff(x.0, y.0), x.1 - y.1)
}

/// Field negation: plain coefficient negation (`i128::MIN` is excluded by
/// the storage invariant, so this cannot overflow).
#[cfg_attr(not(feature = "uninline-portable"), inline)]
pub(crate) const fn neg(x: (i128, i128)) -> (i128, i128) {
    verify!(in_bounds(x), "neg operand out of bounds");
    (x.0.wrapping_neg(), x.1.wrapping_neg())
}

/// Doubling: `add(x, x)` (kept explicit for the const `from_raw` ladder).
#[cfg_attr(not(feature = "uninline-portable"), inline)]
pub(crate) const fn double<P: CmParams>(x: (i128, i128)) -> (i128, i128) {
    add::<P>(x, x)
}

/// Constant-time zero test on RAW coefficients. Sound only for pairs inside
/// the normalizer's output box (in particular, for any [`sub`] result):
/// `(0, 0)` is the only lattice point of `Λ = Zw1 + Zw2` in that box, so a
/// normalized difference of equal field elements is exactly `(0, 0)`.
#[inline]
pub(crate) fn is_zero_raw(x: (i128, i128)) -> Choice {
    let z = (x.0 as u128) | (x.1 as u128);
    (z as u64).ct_eq(&0) & ((z >> 64) as u64).ct_eq(&0)
}

/// Constant-time equality: normalize the difference, then raw zero test.
#[inline]
pub(crate) fn ct_eq<P: CmParams>(x: (i128, i128), y: (i128, i128)) -> Choice {
    is_zero_raw(sub::<P>(x, y))
}

// ---------------------------------------------------------------------------
// Packing between the `[u64; 4]` storage layout and coefficient pairs.
// ---------------------------------------------------------------------------

/// Packs `(a, b)` into the `[u64; 4]` storage layout (limbs `[0..2]` = `a`,
/// `[2..4]` = `b`, two's complement, little-endian words).
#[inline(always)]
pub(crate) const fn pack(x: (i128, i128)) -> [u64; 4] {
    [
        x.0 as u64,
        ((x.0 as u128) >> 64) as u64,
        x.1 as u64,
        ((x.1 as u128) >> 64) as u64,
    ]
}

/// Unpacks the `[u64; 4]` storage layout into `(a, b)`.
#[inline(always)]
pub(crate) const fn unpack(w: &[u64; 4]) -> (i128, i128) {
    (
        ((w[0] as u128) | ((w[1] as u128) << 64)) as i128,
        ((w[2] as u128) | ((w[3] as u128) << 64)) as i128,
    )
}

// ---------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Test-only exact big-integer helpers over little-endian u64 limbs
    /// (self-contained; `glv.rs` has similar machinery but is feature-gated).
    mod limb {
        /// `prod = a * b`; `prod` must be zeroed, len = a.len() + b.len().
        pub(super) fn schoolbook_mul(a: &[u64], b: &[u64], prod: &mut [u64]) {
            assert_eq!(prod.len(), a.len() + b.len());
            for (i, &ai) in a.iter().enumerate() {
                let mut carry = 0u128;
                for (j, &bj) in b.iter().enumerate() {
                    let t = (ai as u128) * (bj as u128) + (prod[i + j] as u128) + carry;
                    prod[i + j] = t as u64;
                    carry = t >> 64;
                }
                prod[i + b.len()] = carry as u64;
            }
        }
    }

    /// Converts a `W256` to `(negative, 256-bit magnitude as 32 LE bytes)`.
    fn w256_sign_mag_bytes(v: W256) -> (bool, [u8; 32]) {
        let negative = (v.hi >> 127) == 1;
        let mag = if negative {
            w256_sub(W256_ZERO, v)
        } else {
            v
        };
        let mut bytes = [0u8; 32];
        bytes[0..16].copy_from_slice(&mag.lo.to_le_bytes());
        bytes[16..32].copy_from_slice(&mag.hi.to_le_bytes());
        (negative, bytes)
    }

    fn u128_from_rng(rng: &mut rand_xorshift::XorShiftRng) -> u128 {
        use rand::Rng;
        (rng.next_u64() as u128) | ((rng.next_u64() as u128) << 64)
    }

    /// A random coefficient pair satisfying the storage invariant.
    fn random_pair(rng: &mut rand_xorshift::XorShiftRng) -> (i128, i128) {
        use rand::Rng;
        let ma = (u128_from_rng(rng) % A_BOUND) as i128;
        let mb = (u128_from_rng(rng) % B_BOUND) as i128;
        let sa = rng.next_u64() & 1 == 1;
        let sb = rng.next_u64() & 1 == 1;
        (if sa { -ma } else { ma }, if sb { -mb } else { mb })
    }

    macro_rules! cm_field_tests {
        ($name:ident, $params:ty, $field:ty, $sigma_from_zeta:expr) => {
            mod $name {
                use super::super::*;
                use super::{limb, random_pair, u128_from_rng, w256_sign_mag_bytes};
                use ff::{Field, FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
                use rand::SeedableRng;
                use rand_xorshift::XorShiftRng;
                use std::vec::Vec;

                type P = $params;
                type F = $field;

                const SEED: [u8; 16] = [
                    0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32,
                    0x54, 0x06, 0xbc, 0xe5,
                ];

                /// The canonical σ as a Montgomery-backed field element.
                fn sigma_f() -> F {
                    F::from_raw(<P as CmParams>::SIGMA)
                }

                /// Field element of a signed i128 (oracle building block).
                fn f_of_i128(v: i128) -> F {
                    let mag = F::from_u128(v.unsigned_abs());
                    if v < 0 {
                        -mag
                    } else {
                        mag
                    }
                }

                /// Field element of a signed W256 (oracle building block).
                fn f_of_w256(v: W256) -> F {
                    let (negative, bytes) = w256_sign_mag_bytes(v);
                    let mut wide = [0u8; 64];
                    wide[0..32].copy_from_slice(&bytes);
                    let mag = F::from_uniform_bytes(&wide);
                    if negative {
                        -mag
                    } else {
                        mag
                    }
                }

                /// ORACLE: the field element represented by a coefficient
                /// pair, computed entirely with the (still-Montgomery)
                /// reference field: `(a + b·σ)·β⁻¹`.
                fn oracle_val(x: (i128, i128)) -> F {
                    (f_of_i128(x.0) + f_of_i128(x.1) * sigma_f())
                        * F::from_raw(<P as CmParams>::BETA_INV)
                }

                /// ORACLE: the field element represented by a raw (V0, V1)
                /// ring value at scale β² (i.e. before one reduction):
                /// `(V0 + V1·σ)·β⁻²`.
                fn oracle_raw(v0: W256, v1: W256) -> F {
                    let beta_inv = F::from_raw(<P as CmParams>::BETA_INV);
                    (f_of_w256(v0) + f_of_w256(v1) * sigma_f()) * beta_inv * beta_inv
                }

                // T1: parameter identities (mirrors the const asserts, but
                // reports values on failure and runs on every test pass).
                #[test]
                fn constants_norm_identity() {
                    let t = <P as CmParams>::T;
                    let m = <P as CmParams>::M;
                    assert_eq!(<P as CmParams>::M0, t + m);
                    assert_eq!(t.rem_euclid(8), 1);
                    assert_eq!(m.rem_euclid(8), 0);
                    // T² + 3TM + 3M² == r, evaluated with the test-only limb
                    // oracle so it does not depend on the kernel's own
                    // wide arithmetic (T6 validates that separately).
                    // Since t may be negative, compute |t|² + 3m² + 3tm as
                    // tt + 3mm ± 3·|t|m.
                    let split = |x: u128| [x as u64, (x >> 64) as u64];
                    let wide = |x: u128, y: u128| {
                        let mut prod = [0u64; 4];
                        limb::schoolbook_mul(&split(x), &split(y), &mut prod);
                        ((prod[0] as u128) | ((prod[1] as u128) << 64),
                         (prod[2] as u128) | ((prod[3] as u128) << 64))
                    };
                    let ta = t.unsigned_abs();
                    let ma = m.unsigned_abs();
                    let (tt_lo, tt_hi) = wide(ta, ta);
                    let (tm_lo, tm_hi) = wide(ta, ma);
                    let (mm_lo, mm_hi) = wide(ma, ma);
                    // acc = tt + 3·mm  (cannot overflow 256 bits: < 4r).
                    let add2 = |a: (u128, u128), b: (u128, u128)| {
                        let (lo, c) = a.0.overflowing_add(b.0);
                        (lo, a.1.wrapping_add(b.1).wrapping_add(c as u128))
                    };
                    let sub2 = |a: (u128, u128), b: (u128, u128)| {
                        let (lo, br) = a.0.overflowing_sub(b.0);
                        (lo, a.1.wrapping_sub(b.1).wrapping_sub(br as u128))
                    };
                    let tm3 = add2(add2((tm_lo, tm_hi), (tm_lo, tm_hi)), (tm_lo, tm_hi));
                    let mm3 = add2(add2((mm_lo, mm_hi), (mm_lo, mm_hi)), (mm_lo, mm_hi));
                    let acc = add2((tt_lo, tt_hi), mm3);
                    let norm = if t < 0 { sub2(acc, tm3) } else { add2(acc, tm3) };
                    let r_lo = (<P as CmParams>::MODULUS_LIMBS[0] as u128)
                        | ((<P as CmParams>::MODULUS_LIMBS[1] as u128) << 64);
                    let r_hi = (<P as CmParams>::MODULUS_LIMBS[2] as u128)
                        | ((<P as CmParams>::MODULUS_LIMBS[3] as u128) << 64);
                    assert_eq!(norm, (r_lo, r_hi));
                }

                // T2: g·I ≡ 1 (mod 2^128).
                #[test]
                fn g_inverse_mod_2_128() {
                    let (c0, c1) = ring_mul_low(
                        <P as CmParams>::T as u128,
                        <P as CmParams>::M as u128,
                        <P as CmParams>::I0,
                        <P as CmParams>::I1,
                    );
                    assert_eq!(c0, 1);
                    assert_eq!(c1, 0);
                }

                // T3: ONE represents β (i.e. the field element 1 after β⁻¹).
                #[test]
                fn one_represents_beta() {
                    assert!(in_bounds(<P as CmParams>::ONE));
                    assert_eq!(oracle_val(<P as CmParams>::ONE), F::ONE);
                }

                // T4: σ² − 3σ + 3 == 0 in the field.
                #[test]
                fn sigma_is_root() {
                    let s = sigma_f();
                    assert_eq!(
                        s.square() - s * F::from(3u64) + F::from(3u64),
                        F::ZERO
                    );
                }

                // T5: the per-field σ–ζ relation (Fp: ζ+2; Fq: ζ²+2).
                #[test]
                fn sigma_matches_crate_zeta() {
                    let rel: fn(F) -> F = $sigma_from_zeta;
                    assert_eq!(sigma_f(), rel(<F as WithSmallOrderMulGroup<3>>::ZETA));
                }

                // T6: the subtractive-Karatsuba word product against a
                // schoolbook oracle, including mid-carry corners.
                #[test]
                fn mul_u128_wide_matches_schoolbook() {
                    let mut rng = XorShiftRng::from_seed(SEED);
                    let corners: &[u128] = &[
                        0,
                        1,
                        2,
                        (1 << 64) - 1,
                        1 << 64,
                        (1 << 64) + 1,
                        u128::MAX,
                        u128::MAX - 1,
                        (u64::MAX as u128) << 64,
                        u64::MAX as u128,
                        1 << 127,
                        (1 << 127) - 1,
                    ];
                    let check = |a: u128, b: u128| {
                        let got = mul_u128_wide(a, b);
                        let mut prod = [0u64; 4];
                        limb::schoolbook_mul(
                            &[a as u64, (a >> 64) as u64],
                            &[b as u64, (b >> 64) as u64],
                            &mut prod,
                        );
                        assert_eq!(got.lo, (prod[0] as u128) | ((prod[1] as u128) << 64));
                        assert_eq!(got.hi, (prod[2] as u128) | ((prod[3] as u128) << 64));
                        if a == b {
                            let sq = square_u128_wide(a);
                            assert_eq!(sq.lo, got.lo);
                            assert_eq!(sq.hi, got.hi);
                        }
                    };
                    for &a in corners {
                        for &b in corners {
                            check(a, b);
                        }
                    }
                    for _ in 0..1000 {
                        let a = u128_from_rng(&mut rng);
                        let b = u128_from_rng(&mut rng);
                        check(a, b);
                        check(a, a);
                    }
                }

                // T8: the adapted lift, exhaustively over the 64 (W0, W1)
                // residues times quotient-coefficient corners.
                #[test]
                fn lift_adapted_exhaustive() {
                    let q_corners: &[i128] = &[
                        0,
                        1,
                        -1,
                        2,
                        -2,
                        1 << 126,
                        -(1 << 126),
                        i128::MAX,
                        i128::MIN,
                        i128::MIN + 1,
                    ];
                    for &q0 in q_corners {
                        for &q1 in q_corners {
                            for w0 in 0u64..8 {
                                for w1 in 0u64..8 {
                                    let (s0, s1) = lift_adapted(q0, q1, w0, w1);
                                    // s ≡ −W (mod 8) coefficientwise.
                                    assert_eq!(
                                        s0.rem_euclid(8) as u64,
                                        w0.wrapping_neg() & 7,
                                        "s0 congruence"
                                    );
                                    assert_eq!(
                                        s1.rem_euclid(8) as u64,
                                        w1.wrapping_neg() & 7,
                                        "s1 congruence"
                                    );
                                    assert!((-16..=16).contains(&s0));
                                    assert!((-4..=4).contains(&s1));
                                }
                            }
                        }
                    }
                }

                // T7: reducer corners — synthetic V hitting quotient
                // extremes and magnitude caps; exactness is enforced by the
                // live `verify!`s inside `reduce`.
                #[test]
                fn reduce_corners_exact_and_bounded() {
                    let mut rng = XorShiftRng::from_seed(SEED);
                    // |V0| cap = A² + 3B² = 1393·2^244; |V1| cap = 2AB + 3B²
                    // = 1176·2^244 (in absolute value).
                    const V0_CAP_HI: u128 = 1393 << 116;
                    const V1_CAP_HI: u128 = 1176 << 116;

                    let q_corners: &[u128] = &[
                        0,
                        1,
                        u128::MAX,          // q = −1 after wrapping_neg? (raw n)
                        1 << 127,           // q = i128::MIN
                        (1 << 127) - 1,     // q = i128::MAX-ish
                        (1 << 127) + 1,
                    ];

                    // Construct V.lo ≡ −q·g (mod 2^128) for a chosen centered
                    // q, then sweep high parts from −cap to +cap.
                    for &nq0 in q_corners {
                        for &nq1 in q_corners {
                            // Choose n = V·I mod M directly; then
                            // V.lo must satisfy V ≡ n·g (mod M) — i.e. the
                            // reducer will recover q = −n.
                            let (vlo0, vlo1) = ring_mul_low(
                                nq0,
                                nq1,
                                <P as CmParams>::T as u128,
                                <P as CmParams>::M as u128,
                            );
                            for _ in 0..16 {
                                // Random signed high parts within caps.
                                let h0 =
                                    u128_from_rng(&mut rng) % (2 * V0_CAP_HI) ;
                                let h1 =
                                    u128_from_rng(&mut rng) % (2 * V1_CAP_HI);
                                let v0 = W256 {
                                    lo: vlo0,
                                    hi: h0.wrapping_sub(V0_CAP_HI),
                                };
                                let v1 = W256 {
                                    lo: vlo1,
                                    hi: h1.wrapping_sub(V1_CAP_HI),
                                };
                                let z = reduce::<P>(v0, v1);
                                assert!(in_bounds(z));
                                assert_eq!(oracle_val(z), oracle_raw(v0, v1));
                            }
                        }
                    }
                }

                // T9: multiplication against the oracle at sign extremes and
                // at random.
                #[test]
                fn mul_matches_oracle() {
                    let mut rng = XorShiftRng::from_seed(SEED);
                    let a_max = (A_BOUND - 1) as i128;
                    let b_max = (B_BOUND - 1) as i128;
                    let corners: Vec<(i128, i128)> = [
                        (0, 0),
                        (1, 0),
                        (0, 1),
                        (a_max, b_max),
                        (a_max, -b_max),
                        (-a_max, b_max),
                        (-a_max, -b_max),
                        (a_max, 0),
                        (-a_max, 0),
                        (0, b_max),
                        (0, -b_max),
                        <P as CmParams>::ONE,
                    ]
                    .to_vec();
                    for &x in &corners {
                        for &y in &corners {
                            let z = mul::<P>(x, y);
                            assert!(in_bounds(z));
                            assert_eq!(oracle_val(z), oracle_val(x) * oracle_val(y));
                        }
                    }
                    for _ in 0..10_000 {
                        let x = random_pair(&mut rng);
                        let y = random_pair(&mut rng);
                        let z = mul::<P>(x, y);
                        assert!(in_bounds(z));
                        assert_eq!(oracle_val(z), oracle_val(x) * oracle_val(y));
                    }
                }

                // T10: squaring — dedicated formula equals mul(x, x) and the
                // oracle.
                #[test]
                fn square_matches_mul_and_oracle() {
                    let mut rng = XorShiftRng::from_seed(SEED);
                    let a_max = (A_BOUND - 1) as i128;
                    let b_max = (B_BOUND - 1) as i128;
                    let corners = [
                        (0, 0),
                        (a_max, b_max),
                        (a_max, -b_max),
                        (-a_max, b_max),
                        (-a_max, -b_max),
                        <P as CmParams>::ONE,
                    ];
                    for &x in &corners {
                        let s = square::<P>(x);
                        let m = mul::<P>(x, x);
                        assert_eq!(oracle_val(s), oracle_val(m));
                        assert_eq!(oracle_val(s), oracle_val(x).square());
                    }
                    for _ in 0..10_000 {
                        let x = random_pair(&mut rng);
                        let s = square::<P>(x);
                        assert!(in_bounds(s));
                        assert_eq!(oracle_val(s), oracle_val(x).square());
                        assert_eq!(oracle_val(s), oracle_val(mul::<P>(x, x)));
                    }
                }

                // T11: addition/subtraction threshold corners around
                // ±⌊3m0/2⌋ (a-lane) and ±m/2 (b-lane), plus negation.
                #[test]
                fn add_sub_threshold_corners() {
                    let half_a = ((3 * (<P as CmParams>::M0 as u128)) >> 1) as i128;
                    let half_b = <P as CmParams>::M / 2;
                    let a_max = (A_BOUND - 1) as i128;
                    let b_max = (B_BOUND - 1) as i128;

                    // Threshold-adjacent sums that fit i128 are built by
                    // target-splitting; the far extremes (sums near ±2A,
                    // which do NOT fit i128) are built as explicit pairs.
                    let mut a_targets = Vec::new();
                    for &base in &[0i128, half_a, -half_a, a_max] {
                        for d in -2i128..=2 {
                            a_targets.push(base + d);
                            a_targets.push(-(base + d));
                        }
                    }
                    let mut b_targets = Vec::new();
                    for &base in &[0i128, half_b, -half_b, 2 * b_max - 2] {
                        for d in -2i128..=2 {
                            b_targets.push(base + d);
                            b_targets.push(-(base + d));
                        }
                    }

                    // Split each (a, b) target into two in-bounds addends.
                    for &ta in &a_targets {
                        for &tb in &b_targets {
                            let x = (ta - ta / 2, tb - tb / 2);
                            let y = (ta / 2, tb / 2);
                            assert!(in_bounds(x) && in_bounds(y));
                            let s = add::<P>(x, y);
                            assert!(in_bounds(s));
                            assert_eq!(oracle_val(s), oracle_val(x) + oracle_val(y));
                            let d = sub::<P>(x, neg(y));
                            assert_eq!(oracle_val(d), oracle_val(x) + oracle_val(y));
                        }
                    }

                    // Explicit extreme pairs: a-lane sums up to ±(2A − 2).
                    for j in 0..3i128 {
                        for &(sx, sy) in &[(1i128, 1i128), (-1, -1), (1, -1)] {
                            let x = (sx * a_max, b_max);
                            let y = (sy * (a_max - j), -b_max + j);
                            let s = add::<P>(x, y);
                            assert!(in_bounds(s));
                            assert_eq!(oracle_val(s), oracle_val(x) + oracle_val(y));
                        }
                    }

                    // Negation involution + oracle.
                    let mut rng = XorShiftRng::from_seed(SEED);
                    for _ in 0..1000 {
                        let x = random_pair(&mut rng);
                        assert_eq!(neg(neg(x)), x);
                        assert_eq!(oracle_val(neg(x)), -oracle_val(x));
                    }
                }

                // T12: small lattice vectors normalize to exactly (0, 0).
                #[test]
                fn lattice_points_normalize_to_zero() {
                    let t = <P as CmParams>::T;
                    let m = <P as CmParams>::M;
                    let m0 = <P as CmParams>::M0;
                    // v = n1·w1 + n2·w2 = (n1·t − 3n2·m0, n1·m + n2·t). The
                    // a-coordinate of ±w2 exceeds i128, so it is never
                    // materialized: with m0 = 2q + 1 (m0 is odd, q = m0 >> 1)
                    // we have 3n2·m0 = n2·(2·3q + 3) and split the halves as
                    // x_a = n1·t − n2·3q − 3n2, y_a = −n2·3q — both in bounds.
                    let q3 = 3 * (m0 >> 1); // ≈ 0.87·2^127, fits i128
                    for n1 in -1i128..=1 {
                        for n2 in -1i128..=1 {
                            if n1 == 0 && n2 == 0 {
                                continue;
                            }
                            let vb = n1 * m + n2 * t;
                            let x = (n1 * t - n2 * q3 - 3 * n2, vb - vb / 2);
                            let y = (-n2 * q3, vb / 2);
                            assert!(in_bounds(x) && in_bounds(y));
                            let z = add::<P>(x, y);
                            assert_eq!(z, (0, 0), "lattice point must vanish");
                        }
                    }
                }

                // T13: random additions/subtractions against the oracle.
                #[test]
                fn add_sub_random_match_oracle() {
                    let mut rng = XorShiftRng::from_seed(SEED);
                    for _ in 0..10_000 {
                        let x = random_pair(&mut rng);
                        let y = random_pair(&mut rng);
                        let s = add::<P>(x, y);
                        let d = sub::<P>(x, y);
                        assert!(in_bounds(s) && in_bounds(d));
                        assert_eq!(oracle_val(s), oracle_val(x) + oracle_val(y));
                        assert_eq!(oracle_val(d), oracle_val(x) - oracle_val(y));
                    }
                }

                // ct_eq: redundant representatives compare equal; unequal
                // values do not. (Full T23 lands with the conversions; this
                // covers the kernel-reachable cases.)
                #[test]
                fn ct_eq_redundant_and_negative() {
                    let mut rng = XorShiftRng::from_seed(SEED);
                    let t = <P as CmParams>::T;
                    let m = <P as CmParams>::M;
                    let one = (1i128, 0i128);
                    for _ in 0..2000 {
                        let x = random_pair(&mut rng);
                        // Shift by ±w1 when the result stays in bounds. (The
                        // ±w2 shift delta exceeds i128; deterministic w2
                        // cases follow below.)
                        for &(da, db) in &[(t, m), (-t, -m)] {
                            let y = (x.0 + da, x.1 + db);
                            if in_bounds(y) {
                                assert!(bool::from(ct_eq::<P>(x, y)));
                                assert_eq!(oracle_val(x), oracle_val(y));
                            }
                        }
                        assert!(bool::from(ct_eq::<P>(x, x)));
                        let xp1 = add::<P>(x, one);
                        assert!(!bool::from(ct_eq::<P>(x, xp1)));
                        assert!(bool::from(is_zero_raw(sub::<P>(x, x))));
                    }
                    // Deterministic ±w2 representatives: x sits in the window
                    // where x − 3m0 is still in bounds, and both sides are
                    // written in closed form (the delta 3m0 exceeds i128).
                    let a_max = (A_BOUND - 1) as i128;
                    let three_m0 = 3 * (<P as CmParams>::M0 as u128);
                    let w2_lo = (three_m0 - (A_BOUND - 1)) as i128; // 3m0 − (A−1)
                    for j in 0..4i128 {
                        let x = (w2_lo + j, j); // a ≈ +0.76·2^127
                        let y = (j - a_max, j + t); // x + (−3m0, t), exactly
                        assert!(in_bounds(x) && in_bounds(y));
                        assert!(bool::from(ct_eq::<P>(x, y)));
                        assert_eq!(oracle_val(x), oracle_val(y));
                        let xn = neg(x);
                        let yn = neg(y);
                        assert!(bool::from(ct_eq::<P>(xn, yn)));
                    }
                    assert!(bool::from(is_zero_raw((0, 0))));
                    assert!(!bool::from(is_zero_raw(one)));
                }

                // pack/unpack round-trip and zero representation.
                #[test]
                fn pack_unpack_roundtrip() {
                    let mut rng = XorShiftRng::from_seed(SEED);
                    assert_eq!(pack((0, 0)), [0u64; 4]);
                    assert_eq!(unpack(&[0u64; 4]), (0, 0));
                    for _ in 0..1000 {
                        let x = random_pair(&mut rng);
                        assert_eq!(unpack(&pack(x)), x);
                    }
                    let one = <P as CmParams>::ONE;
                    assert_eq!(unpack(&pack(one)), one);
                }
            }
        };
    }

    // Stepwise reducer diagnostic: every pass-1/pass-2 intermediate is
    // checked against the Montgomery oracle, so a regression (e.g. from a
    // future assembly backend) pinpoints the first broken step instead of
    // only failing end-to-end. This is where the two subtle width bugs were
    // caught: |V0 + (q·g)0| spans 257 bits and |(q·g)1| alone spans 258.
    #[test]
    fn reduce_intermediates_match_oracle() {
        use crate::fields::Fp;
        use ff::{Field, FromUniformBytes, PrimeField};
        type P = FpParams;

        fn f_of_i128(v: i128) -> Fp {
            let mag = Fp::from_u128(v.unsigned_abs());
            if v < 0 {
                -mag
            } else {
                mag
            }
        }
        fn f_of_w256(v: W256) -> Fp {
            let (negative, bytes) = w256_sign_mag_bytes(v);
            let mut wide = [0u8; 64];
            wide[0..32].copy_from_slice(&bytes);
            let mag = Fp::from_uniform_bytes(&wide);
            if negative {
                -mag
            } else {
                mag
            }
        }
        fn f_of_w320(v: W320) -> Fp {
            let mut wide = [0u8; 64];
            wide[0..16].copy_from_slice(&v.lo.to_le_bytes());
            wide[16..32].copy_from_slice(&v.hi.to_le_bytes());
            let unsigned = Fp::from_uniform_bytes(&wide);
            let m256 = Fp::from_raw([0, 0, 1, 0]).square();
            unsigned + f_of_i128(v.ext) * m256
        }

        use rand::SeedableRng;
        let mut rng = rand_xorshift::XorShiftRng::from_seed([0x5a; 16]);
        for _ in 0..50 {
        let v0 = W256 {
            lo: u128_from_rng(&mut rng),
            hi: (u128_from_rng(&mut rng) % ((1393u128 << 116) * 2)).wrapping_sub(1393 << 116),
        };
        let v1 = W256 {
            lo: u128_from_rng(&mut rng),
            hi: (u128_from_rng(&mut rng) % ((1176u128 << 116) * 2)).wrapping_sub(1176 << 116),
        };
        let (n0, n1) = ring_mul_low(v0.lo, v1.lo, <P as CmParams>::I0, <P as CmParams>::I1);
        let q0 = n0.wrapping_neg() as i128;
        let q1 = n1.wrapping_neg() as i128;
        let u = smul_i128(q0, <P as CmParams>::T);
        let v = smul_i128(q1, <P as CmParams>::M);
        let w = smul_sm_m0::<P>(sm129_from_sum(q0, q1));
        assert_eq!(
            f_of_w256(u),
            f_of_i128(q0) * f_of_i128(<P as CmParams>::T),
            "u = q0*T"
        );
        assert_eq!(
            f_of_w256(v),
            f_of_i128(q1) * f_of_i128(<P as CmParams>::M),
            "v = q1*M"
        );
        assert_eq!(
            f_of_w256(w),
            (f_of_i128(q0) + f_of_i128(q1)) * f_of_i128(<P as CmParams>::M0),
            "w = (q0+q1)*M0"
        );
        let qg0 = w256_sub(u, w256_mul3(v));
        let qg1 = w320_add(w320_sub(w320_from(w), w320_from(u)), w320_shl1(w320_from(v)));
        let three = Fp::from(3u64);
        assert_eq!(
            f_of_w256(qg0),
            f_of_i128(q0) * f_of_i128(<P as CmParams>::T)
                - three * f_of_i128(q1) * f_of_i128(<P as CmParams>::M),
            "qg0"
        );
        assert_eq!(
            f_of_w320(qg1),
            f_of_i128(q0) * f_of_i128(<P as CmParams>::M)
                + f_of_i128(q1) * f_of_i128(<P as CmParams>::T)
                + three * f_of_i128(q1) * f_of_i128(<P as CmParams>::M),
            "qg1"
        );
        let w0 = w256_add_asr128_exact(v0, qg0);
        let w1 = w320_asr128_exact(w320_add(w320_from(v1), qg1));
        let (s0, s1) = lift_adapted(q0, q1, w0.lo as u64, w1.lo as u64);
        let s1m3 = w256_mul3(smul_i128(s1, <P as CmParams>::M));
        let sg0 = w256_sub(smul_i128(s0, <P as CmParams>::T), s1m3);
        let sg1 = w256_add(
            w256_add(
                smul_i128(s0, <P as CmParams>::M),
                smul_i128(s1, <P as CmParams>::T),
            ),
            s1m3,
        );
        assert_eq!(
            f_of_w256(sg0),
            f_of_i128(s0) * f_of_i128(<P as CmParams>::T)
                - three * f_of_i128(s1) * f_of_i128(<P as CmParams>::M),
            "sg0"
        );
        let m128 = Fp::from_raw([0, 0, 1, 0]); // 2^128
        assert_eq!(
            f_of_w256(w0) * m128,
            f_of_w256(v0) + f_of_w256(qg0),
            "W0 exact division"
        );
        assert_eq!(
            f_of_w256(w1) * m128,
            f_of_w256(v1) + f_of_w320(qg1),
            "W1 exact division"
        );
        assert_eq!(
            f_of_w256(sg1),
            f_of_i128(s0) * f_of_i128(<P as CmParams>::M)
                + f_of_i128(s1) * f_of_i128(<P as CmParams>::T)
                + three * f_of_i128(s1) * f_of_i128(<P as CmParams>::M),
            "sg1"
        );
        let z0 = w256_low_i128(w256_asr3_exact(w256_add(w0, sg0)));
        let z1 = w256_low_i128(w256_asr3_exact(w256_add(w1, sg1)));
        let eight = Fp::from(8u64);
        assert_eq!(
            f_of_i128(z0) * eight,
            f_of_w256(w0) + f_of_w256(sg0),
            "Z0 exact division"
        );
        assert_eq!(
            f_of_i128(z1) * eight,
            f_of_w256(w1) + f_of_w256(sg1),
            "Z1 exact division"
        );
        let beta_sq_inv = {
            let b = Fp::from_raw(<P as CmParams>::BETA_INV);
            b * b
        };
        let sigma = Fp::from_raw(<P as CmParams>::SIGMA);
        let lhs = (f_of_i128(z0) + f_of_i128(z1) * sigma) * Fp::from_raw(<P as CmParams>::BETA_INV);
        let rhs = (f_of_w256(v0) + f_of_w256(v1) * sigma) * beta_sq_inv;
        assert_eq!(lhs, rhs, "final Z");
        }
    }

    cm_field_tests!(fp_cm, FpParams, crate::fields::Fp, |z| {
        z + <crate::fields::Fp as ff::Field>::ONE.double()
    });
    cm_field_tests!(fq_cm, FqParams, crate::fields::Fq, |z| {
        z.square() + <crate::fields::Fq as ff::Field>::ONE.double()
    });
}
