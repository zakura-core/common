//! Field elements kept below `2p` between operations.
//!
//! A Montgomery multiplication accepts any product below `R * p` and returns a
//! value below `p + t / R`; the final conditional subtraction that makes it
//! canonical is only needed when the value is compared, serialized, or used
//! where the bounds below do not hold. With `p / R` just over `1/4` for the
//! Pasta moduli:
//!
//! | operation                                                  | result bound |
//! |------------------------------------------------------------|--------------|
//! | canonical × canonical                                      | `1.25 p`     |
//! | lazy (`< 2p`) × canonical                                  | `1.5 p`      |
//! | lazy (`< 2p`) ± canonical, then one conditional subtraction | `< 2p`      |
//! | lazy (`< 2p`) squared                                      | `< 2p` (see `portable::sqr_n_lazy`) |
//!
//! so with **one canonical operand per multiplication** everything stays below
//! `2p` and no multiplication needs its final subtraction. Two lazy operands
//! are not allowed: their product can reach `4p^2`, which exceeds `R * p`
//! because `4p > R` for these moduli (by about `2^128`). This is also exactly
//! the contract of the Apple AArch64 assembly multiplication (unreduced `lhs`,
//! canonical `rhs`), so the same formulas serve both backends. On that backend
//! the routines canonicalize anyway and require canonical inputs, so its lazy
//! values are simply canonical and [`LazyElement::reduce`] is free; the
//! savings are on the portable path.

/// A field whose elements have a lazy form.
pub(crate) trait LazyField: ff::Field {
    /// The lazy form of an element.
    type Lazy: LazyElement<Self>;

    /// Views a canonical element as a lazy one; this is free, so a product of
    /// two canonical elements that should stay lazy is `a.lazy().mul(&b)`.
    fn lazy(self) -> Self::Lazy;
}

/// A field element below `2p`.
pub(crate) trait LazyElement<F>: Copy {
    /// Multiplies by a canonical element.
    fn mul(&self, rhs: &F) -> Self;

    /// Squares.
    fn square(&self) -> Self;

    /// Subtracts a canonical element.
    fn sub(&self, rhs: &F) -> Self;

    /// Canonicalizes.
    fn reduce(self) -> F;
}
