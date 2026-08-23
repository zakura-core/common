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

/// Montgomery-reduces a 512-bit value `t < R * modulus` to a canonical
/// element, where `inv = -modulus^{-1} mod 2^64`.
#[cfg_attr(not(feature = "uninline-portable"), inline(always))]
pub(super) const fn montgomery_reduce(t: &[u64; 8], modulus: &[u64; 4], inv: u64) -> [u64; 4] {
    // The Montgomery reduction here is based on Algorithm 14.32 in
    // Handbook of Applied Cryptography
    // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

    let [r0, r1, r2, r3, r4, r5, r6, r7] = *t;

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

    // Result may be within modulus of the correct value
    sub(&[r4, r5, r6, r7], modulus, modulus)
}
