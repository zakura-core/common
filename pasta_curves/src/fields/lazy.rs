//! Field elements kept below `2p` inside x86-64 point formulas.
//!
//! A Montgomery multiplication accepts a product below `R * p` and, before
//! its final subtraction, returns a value below `p + t / R`. For either Pasta
//! modulus, this gives the bounds used here:
//!
//! | operation                               | result bound |
//! |-----------------------------------------|--------------|
//! | canonical x canonical                   | `< 1.25p`    |
//! | lazy (`< 2p`) x canonical               | `< 1.5p`     |
//! | a point-formula lazy value squared      | `< 2p`       |
//! | lazy +/- canonical, corrected by `p`    | `< 2p`       |
//! | lazy +/- lazy, corrected by `2p`        | `< 2p`       |
//!
//! Multiplication deliberately has no lazy-by-lazy operation: `4p^2` is
//! outside the `R * p` Montgomery input domain because the Pasta moduli are
//! slightly larger than `R / 4`. Point formulas therefore canonicalize one
//! operand at each multiplication boundary.

use crate::arithmetic::{adc, sbb};

/// A field whose canonical elements can be viewed in a lazy representation.
pub(crate) trait LazyField: ff::Field {
    type Lazy: LazyElement<Self>;

    fn lazy(self) -> Self::Lazy;
}

/// A field element represented by an integer in `[0, 2p)`.
pub(crate) trait LazyElement<F>: Copy {
    /// Multiplies by a canonical element.
    fn mul(&self, rhs: &F) -> Self;

    /// Squares a value whose formula-derived range satisfies the module bound.
    fn square(&self) -> Self;

    /// Adds a canonical element.
    fn add(&self, rhs: &F) -> Self;

    /// Adds another lazy element.
    fn add_lazy(&self, rhs: &Self) -> Self;

    fn double(&self) -> Self {
        self.add_lazy(self)
    }

    /// Subtracts a canonical element.
    fn sub(&self, rhs: &F) -> Self;

    /// Subtracts another lazy element.
    fn sub_lazy(&self, rhs: &Self) -> Self;

    /// Conditionally subtracts `p` and returns the canonical field element.
    fn reduce(self) -> F;
}

/// `2 * modulus` as four limbs. Both Pasta moduli have room for the doubling.
pub(super) const fn twice(modulus: &[u64; 4]) -> [u64; 4] {
    let (d0, carry) = adc(modulus[0], modulus[0], 0);
    let (d1, carry) = adc(modulus[1], modulus[1], carry);
    let (d2, carry) = adc(modulus[2], modulus[2], carry);
    let (d3, _) = adc(modulus[3], modulus[3], carry);
    [d0, d1, d2, d3]
}

/// Whether `value` satisfies the lazy representation invariant.
pub(super) const fn is_below_twice(value: &[u64; 4], two_modulus: &[u64; 4]) -> bool {
    let (_, borrow) = sbb(value[0], two_modulus[0], 0);
    let (_, borrow) = sbb(value[1], two_modulus[1], borrow);
    let (_, borrow) = sbb(value[2], two_modulus[2], borrow);
    let (_, borrow) = sbb(value[3], two_modulus[3], borrow);
    borrow != 0
}

/// Subtracts `rhs`, adding `correction` back on underflow.
#[inline(always)]
pub(super) const fn sub(lhs: &[u64; 4], rhs: &[u64; 4], correction: &[u64; 4]) -> [u64; 4] {
    let (d0, borrow) = sbb(lhs[0], rhs[0], 0);
    let (d1, borrow) = sbb(lhs[1], rhs[1], borrow);
    let (d2, borrow) = sbb(lhs[2], rhs[2], borrow);
    let (d3, borrow) = sbb(lhs[3], rhs[3], borrow);

    let (d0, carry) = adc(d0, correction[0] & borrow, 0);
    let (d1, carry) = adc(d1, correction[1] & borrow, carry);
    let (d2, carry) = adc(d2, correction[2] & borrow, carry);
    let (d3, _) = adc(d3, correction[3] & borrow, carry);
    [d0, d1, d2, d3]
}

/// Adds a canonical value to a lazy value, correcting once by `p`.
#[inline(always)]
pub(super) const fn add(lhs: &[u64; 4], rhs: &[u64; 4], modulus: &[u64; 4]) -> [u64; 4] {
    let (d0, carry) = adc(lhs[0], rhs[0], 0);
    let (d1, carry) = adc(lhs[1], rhs[1], carry);
    let (d2, carry) = adc(lhs[2], rhs[2], carry);
    let (d3, _) = adc(lhs[3], rhs[3], carry);
    sub(&[d0, d1, d2, d3], modulus, modulus)
}

/// Adds two lazy values and corrects the five-limb sum once by `2p`.
#[inline(always)]
pub(super) const fn add_lazy(lhs: &[u64; 4], rhs: &[u64; 4], two_modulus: &[u64; 4]) -> [u64; 4] {
    let (d0, carry) = adc(lhs[0], rhs[0], 0);
    let (d1, carry) = adc(lhs[1], rhs[1], carry);
    let (d2, carry) = adc(lhs[2], rhs[2], carry);
    let (d3, carry) = adc(lhs[3], rhs[3], carry);

    let (d0, borrow) = sbb(d0, two_modulus[0], 0);
    let (d1, borrow) = sbb(d1, two_modulus[1], borrow);
    let (d2, borrow) = sbb(d2, two_modulus[2], borrow);
    let (d3, borrow) = sbb(d3, two_modulus[3], borrow);

    // `borrow` is all ones after underflow. A carry out of the original sum
    // proves the five-limb value was already at least 2p, so it suppresses the
    // add-back.
    let mask = borrow & carry.wrapping_sub(1);
    let (d0, carry) = adc(d0, two_modulus[0] & mask, 0);
    let (d1, carry) = adc(d1, two_modulus[1] & mask, carry);
    let (d2, carry) = adc(d2, two_modulus[2] & mask, carry);
    let (d3, _) = adc(d3, two_modulus[3] & mask, carry);
    [d0, d1, d2, d3]
}

/// Conditionally subtracts `p` from a value below `2p`.
#[inline(always)]
pub(super) const fn canonicalize(value: &[u64; 4], modulus: &[u64; 4]) -> [u64; 4] {
    sub(value, modulus, modulus)
}
