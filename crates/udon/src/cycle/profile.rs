//! Recursion profiles: what a proof carries beyond the base recursion.

/// A recursion profile: the polynomials a proof carries on each side of the
/// cycle beyond the base recursion's own.
///
/// The cycle only carries the profile; what the counts mean and how they
/// shape a proof is the proof system's business. Implementations are
/// zero-sized markers, like cycles.
pub trait Profile: Copy + Default + Eq + core::fmt::Debug + Send + Sync + 'static {
    /// Polynomials the profile adds over the circuit field, one per circuit or
    /// stage it registers on that side.
    const NATIVE_EXTENSION: usize;

    /// Polynomials the profile adds over the scalar field.
    const NESTED_EXTENSION: usize;
}

/// The base recursion alone: no extension on either side.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Standard;

impl Profile for Standard {
    const NATIVE_EXTENSION: usize = 0;
    const NESTED_EXTENSION: usize = 0;
}
