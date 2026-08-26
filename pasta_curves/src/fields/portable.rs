//! Shared portable squaring for the Pasta fields.
//!
//! `Fp` and `Fq` have the same representation (four little-endian `u64`
//! limbs in Montgomery form with `R = 2^256`), so their pure-Rust squaring
//! routines are written once here over limb arrays. Each field keeps its own
//! modulus and Montgomery reduction wrapper.

use crate::arithmetic::{adc, mac};

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
