//! Shared portable arithmetic for the Pasta fields.
//!
//! `Fp` and `Fq` have the same representation (four little-endian `u64`
//! limbs in Montgomery form with `R = 2^256`) and differ only in their modulus
//! and the Montgomery constant `INV = -p^{-1} mod 2^64`, so the pure-Rust
//! operations are written once here, over limb arrays, and each field passes
//! its own constants. The Apple AArch64 assembly backend is selected in the
//! fields' `*_runtime` methods; everything else, including every `const fn`
//! path and every non-Apple target, comes through this module.
//!
//! The routines are the ones `fp.rs` and `fq.rs` previously carried inline:
//! schoolbook products into a 512-bit intermediate, the classical eight-limb
//! Montgomery reduction (Algorithm 14.32 in the Handbook of Applied
//! Cryptography), and masked add-back corrections. Nothing branches on limb
//! values and nothing indexes memory by them, so all of it is constant-time.

use crate::arithmetic::{adc, mac, sbb};

/// Adds two canonical elements modulo `modulus`.
#[cfg_attr(not(feature = "uninline-portable"), inline)]
pub(super) const fn add(lhs: &[u64; 4], rhs: &[u64; 4], modulus: &[u64; 4]) -> [u64; 4] {
    let (d0, carry) = adc(lhs[0], rhs[0], 0);
    let (d1, carry) = adc(lhs[1], rhs[1], carry);
    let (d2, carry) = adc(lhs[2], rhs[2], carry);
    let (d3, _) = adc(lhs[3], rhs[3], carry);

    // Attempt to subtract the modulus, to ensure the value
    // is smaller than the modulus.
    sub(&[d0, d1, d2, d3], modulus, modulus)
}

/// Doubles a canonical element modulo `modulus`.
#[inline]
pub(super) const fn double(value: &[u64; 4], modulus: &[u64; 4]) -> [u64; 4] {
    // TODO: This can be achieved more efficiently with a bitshift.
    add(value, value, modulus)
}

/// Subtracts `rhs` from `lhs` modulo `modulus`.
///
/// `lhs` may be any 256-bit value; `rhs` must be canonical or the modulus
/// itself. The result is `lhs - rhs` when that does not underflow and
/// `lhs - rhs + modulus` otherwise, which is canonical whenever `lhs` is below
/// `2 * modulus` (the case the reductions rely on).
#[cfg_attr(not(feature = "uninline-portable"), inline)]
pub(super) const fn sub(lhs: &[u64; 4], rhs: &[u64; 4], modulus: &[u64; 4]) -> [u64; 4] {
    let (d0, borrow) = sbb(lhs[0], rhs[0], 0);
    let (d1, borrow) = sbb(lhs[1], rhs[1], borrow);
    let (d2, borrow) = sbb(lhs[2], rhs[2], borrow);
    let (d3, borrow) = sbb(lhs[3], rhs[3], borrow);

    // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
    // borrow = 0x000...000. Thus, we use it as a mask to conditionally add the modulus.
    let (d0, carry) = adc(d0, modulus[0] & borrow, 0);
    let (d1, carry) = adc(d1, modulus[1] & borrow, carry);
    let (d2, carry) = adc(d2, modulus[2] & borrow, carry);
    let (d3, _) = adc(d3, modulus[3] & borrow, carry);

    [d0, d1, d2, d3]
}

/// Negates a canonical element modulo `modulus`.
#[cfg_attr(not(feature = "uninline-portable"), inline)]
pub(super) const fn neg(value: &[u64; 4], modulus: &[u64; 4]) -> [u64; 4] {
    // Subtract `value` from `modulus` to negate. Ignore the final
    // borrow because it cannot underflow; value is guaranteed to
    // be in the field.
    let (d0, borrow) = sbb(modulus[0], value[0], 0);
    let (d1, borrow) = sbb(modulus[1], value[1], borrow);
    let (d2, borrow) = sbb(modulus[2], value[2], borrow);
    let (d3, _) = sbb(modulus[3], value[3], borrow);

    // `tmp` could be `modulus` if `value` was zero. Create a mask that is
    // zero if `value` was zero, and `u64::max_value()` if value was nonzero.
    let mask = (((value[0] | value[1] | value[2] | value[3]) == 0) as u64).wrapping_sub(1);

    [d0 & mask, d1 & mask, d2 & mask, d3 & mask]
}

/// Multiplies `lhs` by `rhs`, returning the unreduced 512-bit product.
#[cfg_attr(not(feature = "uninline-portable"), inline)]
pub(super) const fn mul_wide(lhs: &[u64; 4], rhs: &[u64; 4]) -> [u64; 8] {
    // Schoolbook multiplication

    let (r0, carry) = mac(0, lhs[0], rhs[0], 0);
    let (r1, carry) = mac(0, lhs[0], rhs[1], carry);
    let (r2, carry) = mac(0, lhs[0], rhs[2], carry);
    let (r3, r4) = mac(0, lhs[0], rhs[3], carry);

    let (r1, carry) = mac(r1, lhs[1], rhs[0], 0);
    let (r2, carry) = mac(r2, lhs[1], rhs[1], carry);
    let (r3, carry) = mac(r3, lhs[1], rhs[2], carry);
    let (r4, r5) = mac(r4, lhs[1], rhs[3], carry);

    let (r2, carry) = mac(r2, lhs[2], rhs[0], 0);
    let (r3, carry) = mac(r3, lhs[2], rhs[1], carry);
    let (r4, carry) = mac(r4, lhs[2], rhs[2], carry);
    let (r5, r6) = mac(r5, lhs[2], rhs[3], carry);

    let (r3, carry) = mac(r3, lhs[3], rhs[0], 0);
    let (r4, carry) = mac(r4, lhs[3], rhs[1], carry);
    let (r5, carry) = mac(r5, lhs[3], rhs[2], carry);
    let (r6, r7) = mac(r6, lhs[3], rhs[3], carry);

    [r0, r1, r2, r3, r4, r5, r6, r7]
}

/// Squares a canonical element, returning the canonical square.
#[cfg_attr(not(feature = "uninline-portable"), inline)]
pub(super) const fn square(value: &[u64; 4], modulus: &[u64; 4], inv: u64) -> [u64; 4] {
    canonicalize(
        &reduce_square_lazy(&square_wide(value), modulus, inv),
        modulus,
    )
}

/// Squares `value`, returning the unreduced 512-bit product.
#[cfg_attr(not(feature = "uninline-portable"), inline)]
pub(super) const fn square_wide(value: &[u64; 4]) -> [u64; 8] {
    let (r1, carry) = mac(0, value[0], value[1], 0);
    let (r2, carry) = mac(0, value[0], value[2], carry);
    let (r3, r4) = mac(0, value[0], value[3], carry);

    let (r3, carry) = mac(r3, value[1], value[2], 0);
    let (r4, r5) = mac(r4, value[1], value[3], carry);

    let (r5, r6) = mac(r5, value[2], value[3], 0);

    let r7 = r6 >> 63;
    let r6 = (r6 << 1) | (r5 >> 63);
    let r5 = (r5 << 1) | (r4 >> 63);
    let r4 = (r4 << 1) | (r3 >> 63);
    let r3 = (r3 << 1) | (r2 >> 63);
    let r2 = (r2 << 1) | (r1 >> 63);
    let r1 = r1 << 1;

    let (r0, carry) = mac(0, value[0], value[0], 0);
    let (r1, carry) = adc(0, r1, carry);
    let (r2, carry) = mac(r2, value[1], value[1], carry);
    let (r3, carry) = adc(0, r3, carry);
    let (r4, carry) = mac(r4, value[2], value[2], carry);
    let (r5, carry) = adc(0, r5, carry);
    let (r6, carry) = mac(r6, value[3], value[3], carry);
    let (r7, _) = adc(0, r7, carry);

    [r0, r1, r2, r3, r4, r5, r6, r7]
}

/// The four cancellation rounds of the Montgomery reduction of a 512-bit
/// value `t < R * modulus` (Algorithm 14.32 in the Handbook of Applied
/// Cryptography), yielding the surviving four limbs, a value below
/// `2 * modulus`.
///
/// This is a macro rather than a helper function on purpose: an extra
/// function layer here, even an `inline(always)` one, changes LLVM's
/// inlining decisions for the multiplication that expands it.
macro_rules! montgomery_rounds {
    ($t:expr, $modulus:expr, $inv:expr) => {{
        let [r0, r1, r2, r3, r4, r5, r6, r7] = *$t;
        let modulus: &[u64; 4] = $modulus;
        let inv: u64 = $inv;

        let k = r0.wrapping_mul(inv);
        let (_, carry) = mac(r0, k, modulus[0], 0);
        let (r1, carry) = mac(r1, k, modulus[1], carry);
        let (r2, carry) = mac(r2, k, modulus[2], carry);
        let (r3, carry) = mac(r3, k, modulus[3], carry);
        let (r4, carry2) = adc(r4, 0, carry);

        let k = r1.wrapping_mul(inv);
        let (_, carry) = mac(r1, k, modulus[0], 0);
        let (r2, carry) = mac(r2, k, modulus[1], carry);
        let (r3, carry) = mac(r3, k, modulus[2], carry);
        let (r4, carry) = mac(r4, k, modulus[3], carry);
        let (r5, carry2) = adc(r5, carry2, carry);

        let k = r2.wrapping_mul(inv);
        let (_, carry) = mac(r2, k, modulus[0], 0);
        let (r3, carry) = mac(r3, k, modulus[1], carry);
        let (r4, carry) = mac(r4, k, modulus[2], carry);
        let (r5, carry) = mac(r5, k, modulus[3], carry);
        let (r6, carry2) = adc(r6, carry2, carry);

        let k = r3.wrapping_mul(inv);
        let (_, carry) = mac(r3, k, modulus[0], 0);
        let (r4, carry) = mac(r4, k, modulus[1], carry);
        let (r5, carry) = mac(r5, k, modulus[2], carry);
        let (r6, carry) = mac(r6, k, modulus[3], carry);
        let (r7, _) = adc(r7, carry2, carry);

        [r4, r5, r6, r7]
    }};
}

/// Montgomery-reduces a 512-bit value `t < R * modulus` to a canonical
/// element, where `inv = -modulus^{-1} mod 2^64`.
#[cfg_attr(not(feature = "uninline-portable"), inline(always))]
pub(super) const fn montgomery_reduce(t: &[u64; 8], modulus: &[u64; 4], inv: u64) -> [u64; 4] {
    // Result may be within modulus of the correct value
    sub(&montgomery_rounds!(t, modulus, inv), modulus, modulus)
}

/// Montgomery-reduces a 512-bit value `t < R * modulus` by cancelling its low
/// half first, returning a result below `2 * modulus`.
///
/// The Montgomery quotient `Q` depends only on the low 256 bits of `t`, and
/// `(t + Q * modulus) / R == (t_lo + Q * modulus) / R + t_hi` exactly, so the
/// four cancellation rounds can run over four live limbs instead of eight and
/// the high half is added once at the end. This is how the assembly backend's
/// squaring and its `mul_by_1` helper are structured. The value produced is
/// the same as the classical reduction's, limb for limb; only the
/// dependency graph differs, which is shorter for the narrow product of a
/// squaring and measured slower for the wider product of a multiplication.
///
/// `(t_lo + Q * modulus) / R <= modulus` and `t_hi < modulus`, so the sum is
/// below `2 * modulus` and fits in four limbs.
#[cfg(any(target_arch = "x86_64", test))]
#[cfg_attr(not(feature = "uninline-portable"), inline(always))]
pub(super) const fn montgomery_reduce_low_lazy(
    t: &[u64; 8],
    modulus: &[u64; 4],
    inv: u64,
) -> [u64; 4] {
    let [r0, r1, r2, r3, t4, t5, t6, t7] = *t;

    // Each round chooses k so that the lowest live limb plus k * modulus[0]
    // vanishes modulo 2^64, adds k * modulus, and drops that limb. The
    // carry out of the top limb becomes the new top limb.
    let k = r0.wrapping_mul(inv);
    let (_, carry) = mac(r0, k, modulus[0], 0);
    let (r0, carry) = mac(r1, k, modulus[1], carry);
    let (r1, carry) = mac(r2, k, modulus[2], carry);
    let (r2, r3) = mac(r3, k, modulus[3], carry);

    let k = r0.wrapping_mul(inv);
    let (_, carry) = mac(r0, k, modulus[0], 0);
    let (r0, carry) = mac(r1, k, modulus[1], carry);
    let (r1, carry) = mac(r2, k, modulus[2], carry);
    let (r2, r3) = mac(r3, k, modulus[3], carry);

    let k = r0.wrapping_mul(inv);
    let (_, carry) = mac(r0, k, modulus[0], 0);
    let (r0, carry) = mac(r1, k, modulus[1], carry);
    let (r1, carry) = mac(r2, k, modulus[2], carry);
    let (r2, r3) = mac(r3, k, modulus[3], carry);

    let k = r0.wrapping_mul(inv);
    let (_, carry) = mac(r0, k, modulus[0], 0);
    let (r0, carry) = mac(r1, k, modulus[1], carry);
    let (r1, carry) = mac(r2, k, modulus[2], carry);
    let (r2, r3) = mac(r3, k, modulus[3], carry);

    // Add the high half; the sum is below 2 * modulus, so no carry out.
    let (r0, carry) = adc(r0, t4, 0);
    let (r1, carry) = adc(r1, t5, carry);
    let (r2, carry) = adc(r2, t6, carry);
    let (r3, _) = adc(r3, t7, carry);

    [r0, r1, r2, r3]
}

/// Reduces the 512-bit product of a squaring to a value below `2 * modulus`.
///
/// On x86-64 this is the low-half reduction: with `mul` pinned to `rax:rdx`
/// the classical form waits on the product's top limbs round by round, and
/// overlapping the cancellation rounds with the product's tail measured a
/// dependent squaring chain 10% faster (and every other mode faster too).
/// On AArch64 the classical rounds were already scheduled well and the
/// low-half form measured 6% slower on the same chain, so other targets keep
/// the classical form. Both produce the same limbs.
#[cfg_attr(not(feature = "uninline-portable"), inline(always))]
const fn reduce_square_lazy(t: &[u64; 8], modulus: &[u64; 4], inv: u64) -> [u64; 4] {
    #[cfg(target_arch = "x86_64")]
    {
        montgomery_reduce_low_lazy(t, modulus, inv)
    }

    #[cfg(not(target_arch = "x86_64"))]
    {
        montgomery_rounds!(t, modulus, inv)
    }
}

/// Subtracts `modulus` from a value below `2 * modulus` if that does not
/// underflow, which makes the value canonical.
#[cfg_attr(not(feature = "uninline-portable"), inline(always))]
pub(super) const fn canonicalize(value: &[u64; 4], modulus: &[u64; 4]) -> [u64; 4] {
    sub(value, modulus, modulus)
}

/// Squares `value` `n` times, leaving the accumulator in `[0, 2 * modulus)`
/// throughout instead of canonicalizing after every squaring. This is the
/// portable form of the assembly backend's `sqr_n_mul` loop.
///
/// # Why the chain stays in the reduction's domain
///
/// A Montgomery reduction accepts any input below `R * p` and returns a value
/// below `p + t_hi`, where `t_hi = t / R`. So if the accumulator is below
/// `c * p`, its square is below `c^2 * p^2` and the next accumulator is below
/// `(1 + c^2 * p / R) * p`. From a canonical start the multipliers are
///
/// ```text
/// 1, 1.25, 1.390625, 1.483..., ...   (approaching 2 from below as ~2 - 4/n)
/// ```
///
/// and a step is legal as long as `(c * p)^2 < R * p`, i.e. `c * p` is below
/// `isqrt(R * p)`. For both Pasta moduli `isqrt(R * p) = 2p - (p mod 2^128) - 1`
/// (since `p = 2^254 + c'` with `c' = p mod 2^128`), about `2^125` below
/// `2p`, while the chain bound only closes on `2p` as `4p / n`: reaching the
/// unsafe point would take about `2^131` squarings against a `u32` count.
/// Iterating the exact integer bound `B <- p + floor(B^2 / R)` for forty
/// million steps still gives `1.9999999 * p`.
///
/// The result must be canonicalized by the caller, either with
/// [`canonicalize`] or by multiplying it with a canonical value: that product
/// is below `2p * p < R * p`, so the multiplication's own reduction accepts it
/// and returns a canonical result.
#[cfg_attr(not(feature = "uninline-portable"), inline)]
#[cfg_attr(
    all(
        feature = "aarch64-asm",
        target_arch = "aarch64",
        target_vendor = "apple"
    ),
    allow(dead_code)
)]
pub(super) fn sqr_n_lazy(value: &[u64; 4], n: u32, modulus: &[u64; 4], inv: u64) -> [u64; 4] {
    let mut acc = *value;
    for _ in 0..n {
        acc = reduce_square_lazy(&square_wide(&acc), modulus, inv);
    }
    acc
}
