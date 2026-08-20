//! Shared portable arithmetic for the Pasta fields.
//!
//! Addition, subtraction, doubling and negation are short enough that the
//! shape of their carry chains dominates. These implementations differ from
//! the older `mac`/`adc`-with-a-64-bit-carry-word forms in three ways, all
//! borrowed from the Apple AArch64 assembly in `aarch64_asm.rs`:
//!
//! * **Single-bit carries.** [`adc`]/[`sbb`] return a `bool`, so each chain
//!   lowers to one `adc`/`sbb` sequence rather than an add plus a
//!   materialized carry register per limb.
//! * **Select instead of masked add-back.** The correction after an addition
//!   subtracts `p` unconditionally and then picks between the two results,
//!   which is one dependent chain rather than two.
//! * **The Pasta modulus shape.** Both moduli have `p[2] == 0` and
//!   `p[3] == 2^62`, so `p` is materialized inline and only `p[0]` and `p[1]`
//!   need to be passed in. The callers assert the shape.
//!
//! Doubling additionally uses a shift rather than a self-addition: `p < 2^255`
//! means the shift cannot overflow 256 bits, and the four shifted limbs are
//! independent of each other where a carry chain is not.
//!
//! [`montgomery_reduce_low`] carries over one more idea from the assembly: the
//! Montgomery quotient depends only on the low half of the product, so the
//! cancellation rounds can run over four limbs and add the high half once at
//! the end. Squaring uses it. Multiplication does not, and neither uses the
//! interleaved (CIOS) product: both were tried and measured slower on x86-64,
//! because roughly halving the instruction count also serializes the whole
//! routine through the flag register, which the wider `mac` form avoids.
//!
//! There are no branches on limb values and no memory accesses here, so the
//! code is constant-time.

/// Compute `a + b + carry`, returning the sum and the carry out.
#[inline(always)]
pub(super) const fn adc(a: u64, b: u64, carry: bool) -> (u64, bool) {
    // `u64::carrying_add` is not yet const-stable; this lowers identically.
    let (s, c0) = a.overflowing_add(b);
    let (s, c1) = s.overflowing_add(carry as u64);
    (s, c0 | c1)
}

/// Compute `a - b - borrow`, returning the difference and the borrow out.
#[inline(always)]
pub(super) const fn sbb(a: u64, b: u64, borrow: bool) -> (u64, bool) {
    let (d, b0) = a.overflowing_sub(b);
    let (d, b1) = d.overflowing_sub(borrow as u64);
    (d, b0 | b1)
}

/// Compute `a + b * c + carry` as a 128-bit value, returned as (low, high).
#[inline(always)]
const fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let ret = (a as u128) + ((b as u128) * (c as u128)) + (carry as u128);
    (ret as u64, (ret >> 64) as u64)
}

/// Conditionally subtract `p` from a value already known to be less than `2p`.
#[inline(always)]
const fn conditional_subtract_p(r: [u64; 4], p0: u64, p1: u64) -> [u64; 4] {
    let (s0, borrow) = sbb(r[0], p0, false);
    let (s1, borrow) = sbb(r[1], p1, borrow);
    let (s2, borrow) = sbb(r[2], 0, borrow);
    let (s3, borrow) = sbb(r[3], 1 << 62, borrow);

    // Borrow means the subtraction underflowed, so keep the original value.
    let take = (borrow as u64).wrapping_sub(1);
    [
        (s0 & take) | (r[0] & !take),
        (s1 & take) | (r[1] & !take),
        (s2 & take) | (r[2] & !take),
        (s3 & take) | (r[3] & !take),
    ]
}

/// Adds two canonical field elements.
#[inline(always)]
pub(super) const fn add(lhs: &[u64; 4], rhs: &[u64; 4], p0: u64, p1: u64) -> [u64; 4] {
    // Both operands are below `p < 2^255`, so the sum cannot exceed 256 bits.
    let (d0, c) = adc(lhs[0], rhs[0], false);
    let (d1, c) = adc(lhs[1], rhs[1], c);
    let (d2, c) = adc(lhs[2], rhs[2], c);
    let (d3, _) = adc(lhs[3], rhs[3], c);
    conditional_subtract_p([d0, d1, d2, d3], p0, p1)
}

/// Doubles a canonical field element.
#[inline(always)]
pub(super) const fn double(value: &[u64; 4], p0: u64, p1: u64) -> [u64; 4] {
    // `value < p < 2^255`, so the shift cannot overflow 256 bits. The shifts
    // are independent of each other, unlike the carry chain of `add`.
    let d3 = (value[3] << 1) | (value[2] >> 63);
    let d2 = (value[2] << 1) | (value[1] >> 63);
    let d1 = (value[1] << 1) | (value[0] >> 63);
    let d0 = value[0] << 1;
    conditional_subtract_p([d0, d1, d2, d3], p0, p1)
}

/// Subtracts two canonical field elements.
#[inline(always)]
pub(super) const fn sub(lhs: &[u64; 4], rhs: &[u64; 4], p0: u64, p1: u64) -> [u64; 4] {
    let (d0, borrow) = sbb(lhs[0], rhs[0], false);
    let (d1, borrow) = sbb(lhs[1], rhs[1], borrow);
    let (d2, borrow) = sbb(lhs[2], rhs[2], borrow);
    let (d3, borrow) = sbb(lhs[3], rhs[3], borrow);

    // Add the modulus back if the subtraction underflowed.
    let mask = (borrow as u64).wrapping_neg();
    let (d0, c) = adc(d0, p0 & mask, false);
    let (d1, c) = adc(d1, p1 & mask, c);
    let (d2, c) = adc(d2, 0, c);
    let (d3, _) = adc(d3, (1 << 62) & mask, c);
    [d0, d1, d2, d3]
}

/// Negates a canonical field element.
#[inline(always)]
pub(super) const fn neg(value: &[u64; 4], p0: u64, p1: u64) -> [u64; 4] {
    let (d0, borrow) = sbb(p0, value[0], false);
    let (d1, borrow) = sbb(p1, value[1], borrow);
    let (d2, borrow) = sbb(0, value[2], borrow);
    let (d3, _) = sbb(1 << 62, value[3], borrow);

    // `p - 0` is `p`, which is not canonical; mask the result to zero in that
    // one case.
    let mask = (((value[0] | value[1] | value[2] | value[3]) == 0) as u64).wrapping_sub(1);
    [d0 & mask, d1 & mask, d2 & mask, d3 & mask]
}

/// Montgomery-reduces a 512-bit value `t < R * p`.
///
/// The Montgomery quotient `Q` depends only on the low 256 bits of `t`, so
/// `(t + Q*p) / R == (t_lo + Q*p) / R + t_hi`. Running the four cancellation
/// rounds over the low half alone keeps four limbs live instead of eight,
/// which is how the assembly's `mul_by_1` helper is structured. The high half
/// is folded in once at the end.
///
/// `(t_lo + Q*p) / R <= p` and `t_hi < p`, so the sum is below `2p` and one
/// conditional subtraction canonicalizes it.
///
/// The individual limb products keep the wide `mac` form on purpose: rewriting
/// them with single-bit carries halves the instruction count but serializes
/// the whole reduction through the flag register, which measured slower on
/// x86-64.
#[inline(always)]
pub(super) const fn montgomery_reduce_low(t: &[u64; 8], p0: u64, p1: u64, inv: u64) -> [u64; 4] {
    let (mut r0, mut r1, mut r2, mut r3) = (t[0], t[1], t[2], t[3]);

    let mut i = 0;
    while i < 4 {
        // Choose k so that r0 + k * p[0] vanishes modulo 2^64, add k * p, and
        // drop the cancelled limb. `p[2]` is zero and `p[3]` is 2^62, so those
        // two products fold away at compile time.
        let k = r0.wrapping_mul(inv);
        let (_, carry) = mac(r0, k, p0, 0);
        let (x1, carry) = mac(r1, k, p1, carry);
        let (x2, carry) = mac(r2, k, 0, carry);
        let (x3, carry) = mac(r3, k, 1 << 62, carry);
        r0 = x1;
        r1 = x2;
        r2 = x3;
        r3 = carry;
        i += 1;
    }

    let (r0, c) = adc(r0, t[4], false);
    let (r1, c) = adc(r1, t[5], c);
    let (r2, c) = adc(r2, t[6], c);
    let (r3, _) = adc(r3, t[7], c);

    conditional_subtract_p([r0, r1, r2, r3], p0, p1)
}
