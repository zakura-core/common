//! Prototype 1: sparse-modulus portable Rust.
//!
//! CIOS Montgomery multiplication and squaring specialized to the Pasta
//! modulus shape (`p[2] = 0`, `p[3] = 2^62`), written so LLVM can inline it
//! into callers and keep values in registers between field operations.

use crate::{adc, mac, reduce_once, Limbs, INV, P0, P1};

/// One CIOS round: `acc = (acc + a * bi + q * p) / 2^64`.
///
/// The accumulator enters and leaves with its fifth limb zero (the value is
/// below `b + p < 2p < 2^256` for canonical operands).
#[inline(always)]
fn round(t: [u64; 4], a: &Limbs, bi: u64) -> [u64; 4] {
    // acc += a * bi (five limbs; the fifth is the final carry).
    let (r0, c) = mac(t[0], a[0], bi, 0);
    let (r1, c) = mac(t[1], a[1], bi, c);
    let (r2, c) = mac(t[2], a[2], bi, c);
    let (r3, c) = mac(t[3], a[3], bi, c);
    let r4 = c;

    // Montgomery cancellation of r0. low(q*p[0]) cancels r0 exactly, so only
    // the carry out of that addition survives.
    let q = r0.wrapping_mul(INV);
    let carry = (((r0 as u128) + (q as u128) * (P0 as u128)) >> 64) as u64;
    let (s0, c) = mac(r1, q, P1, carry);
    let (s1, c) = adc(r2, 0, c); // p[2] = 0
    let (s2, c) = adc(r3, q << 62, c); // low(q * p[3])
    let (s3, _) = adc(r4, q >> 2, c); // high(q * p[3]); no carry out
    [s0, s1, s2, s3]
}

/// Montgomery multiplication of canonical Montgomery residues.
#[inline(always)]
pub fn mul(a: &Limbs, b: &Limbs) -> Limbs {
    let t = round([0; 4], a, b[0]);
    let t = round(t, a, b[1]);
    let t = round(t, a, b[2]);
    let t = round(t, a, b[3]);
    reduce_once(t)
}

/// Montgomery squaring of a canonical Montgomery residue.
#[inline(always)]
pub fn sqr(a: &Limbs) -> Limbs {
    // Cross products.
    let (r1, carry) = mac(0, a[0], a[1], 0);
    let (r2, carry) = mac(0, a[0], a[2], carry);
    let (r3, r4) = mac(0, a[0], a[3], carry);
    let (r3, carry) = mac(r3, a[1], a[2], 0);
    let (r4, r5) = mac(r4, a[1], a[3], carry);
    let (r5, r6) = mac(r5, a[2], a[3], 0);

    // Double the cross products.
    let r7 = r6 >> 63;
    let r6 = (r6 << 1) | (r5 >> 63);
    let r5 = (r5 << 1) | (r4 >> 63);
    let r4 = (r4 << 1) | (r3 >> 63);
    let r3 = (r3 << 1) | (r2 >> 63);
    let r2 = (r2 << 1) | (r1 >> 63);
    let r1 = r1 << 1;

    // Add the diagonal squares.
    let (r0, carry) = mac(0, a[0], a[0], 0);
    let (r1, carry) = adc(r1, 0, carry);
    let (r2, carry) = mac(r2, a[1], a[1], carry);
    let (r3, carry) = adc(r3, 0, carry);
    let (r4, carry) = mac(r4, a[2], a[2], carry);
    let (r5, carry) = adc(r5, 0, carry);
    let (r6, carry) = mac(r6, a[3], a[3], carry);
    let (r7, _) = adc(r7, 0, carry);

    montgomery_reduce_sparse([r0, r1, r2, r3, r4, r5, r6, r7])
}

/// Reduces an eight-limb product with the sparse Pasta modulus.
#[inline(always)]
fn montgomery_reduce_sparse(r: [u64; 8]) -> Limbs {
    let [r0, r1, r2, r3, r4, r5, r6, r7] = r;

    let q = r0.wrapping_mul(INV);
    let carry = (((r0 as u128) + (q as u128) * (P0 as u128)) >> 64) as u64;
    let (r1, carry) = mac(r1, q, P1, carry);
    let (r2, carry) = adc(r2, 0, carry);
    let (r3, carry) = adc(r3, q << 62, carry);
    let (r4, carry2) = adc(r4, q >> 2, carry);

    let q = r1.wrapping_mul(INV);
    let carry = (((r1 as u128) + (q as u128) * (P0 as u128)) >> 64) as u64;
    let (r2, carry) = mac(r2, q, P1, carry);
    let (r3, carry) = adc(r3, 0, carry);
    let (r4, carry) = adc(r4, q << 62, carry);
    let (r5, carry2) = adc(r5, (q >> 2) + carry2, carry);

    let q = r2.wrapping_mul(INV);
    let carry = (((r2 as u128) + (q as u128) * (P0 as u128)) >> 64) as u64;
    let (r3, carry) = mac(r3, q, P1, carry);
    let (r4, carry) = adc(r4, 0, carry);
    let (r5, carry) = adc(r5, q << 62, carry);
    let (r6, carry2) = adc(r6, (q >> 2) + carry2, carry);

    let q = r3.wrapping_mul(INV);
    let carry = (((r3 as u128) + (q as u128) * (P0 as u128)) >> 64) as u64;
    let (r4, carry) = mac(r4, q, P1, carry);
    let (r5, carry) = adc(r5, 0, carry);
    let (r6, carry) = adc(r6, q << 62, carry);
    let (r7, _) = adc(r7, (q >> 2) + carry2, carry);

    reduce_once([r4, r5, r6, r7])
}
