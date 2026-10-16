//! Implementation dependencies for Orchard's legacy backend.
//! Orchard consumers should depend on `orchard`, not this support crate.
#![no_std]
pub use {ff, group, pasta_curves, poseidon, reddsa, sinsemilla};
#[cfg(feature = "circuit")]
pub use {halo2_gadgets, halo2_proofs};
