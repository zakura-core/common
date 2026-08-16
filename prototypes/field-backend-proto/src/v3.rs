//! Prototype 3: hand-fused Jacobian doubling in assembly.
//!
//! `src/double_n.S` implements dbl-2009-l (a = 0) with every field operation
//! macro-inlined over a fixed stack frame: one call doubles the point `n`
//! times with no per-field-op call, ABI spill, or out-pointer traffic.

extern "C" {
    fn proto_double_n(xyz: *mut [u64; 12], n: usize);
}

/// Doubles the Jacobian point `[X, Y, Z]` (three Montgomery-form field
/// elements, little-endian limbs) in place, `n` times. `n` must be at
/// least 1.
#[inline]
pub fn double_n(xyz: &mut [u64; 12], n: usize) {
    // The assembly decrements before testing, so n = 0 would wrap.
    assert!(n >= 1);
    unsafe { proto_double_n(xyz, n) };
}
