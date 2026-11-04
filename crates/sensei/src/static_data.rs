//! Zero-copy access to embedded data.
//!
//! The mechanism — the [`Pod`](trait@bento::Pod) safety contract, the aligned
//! embedding casts, and the [`bento::embed_array!`] and [`bento::embed_struct!`]
//! declaration macros — lives in the `bento` crate, and the `Pod` implementations
//! live with the record types they describe: the field and point records in
//! `udon`, the circuit records in `sensei-shared`. This crate defines
//! no stored types of its own, so it contains no `unsafe` at all; this module
//! only re-exports the declaration macros for the primitive tables and, when
//! enabled, the prover and verifier data (including `native::target` under the
//! `prover` feature).

#[cfg(feature = "prover")]
pub(crate) use bento::embed_array;
pub(crate) use bento::embed_struct;
#[cfg(test)]
pub(crate) use bento::{bytes_of, bytes_of_slice};

#[cfg(test)]
mod tests {
    use super::{bytes_of, bytes_of_slice};
    use std::prelude::v1::*;
    use udon::field::Fp;

    #[test]
    fn field_elements_round_trip_through_stored_bytes() {
        let one = <Fp>::ONE;
        let limbs = one.montgomery_limbs();
        let stored = bytes_of(&one);
        assert_eq!(stored.len(), 32);
        for (limb, chunk) in limbs.iter().zip(stored.chunks_exact(8)) {
            assert_eq!(chunk, limb.to_le_bytes());
        }
        assert_eq!(bytes_of_slice(&[one, one])[..32], *stored);
    }
}
