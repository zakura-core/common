//! # sapling
//!
//! ## Nomenclature
//!
//! All types in the `sapling-crypto` crate, unless otherwise specified, are
//! Sapling-specific types. For example, [`PaymentAddress`] is documented as being a
//! shielded payment address; we implicitly mean it is an Sapling payment address (as
//! opposed to e.g. an Orchard payment address, which is also shielded).
//!
//! ## Feature flags
//!
//! - `pinned-vk-only`: embeds the canonical Sapling verifying keys
//!   without proving parameters, and enables `circuit`. It adds no Wagyu
//!   dependency; separately enabled proving dependencies are unaffected.
//! ### Wallet derivation
//!
//! The default-enabled `zip32` feature exposes wallet derivation and PCZT APIs.
//! Node clients may omit it while retaining verification and coinbase construction.
//! `zip32-addresses` implies `zip32`.
//!
//! ### ZIP 32 addresses
//!
//! The default-enabled `zip32-addresses` feature provides indexed address
//! generation and diversifier-index recovery using FF1. Consumers that disable
//! default features must enable it explicitly to use these wallet APIs. Direct
//! address construction from diversifiers and note decryption
//! remain available without it.
//!

//! Standard builds use `std::io`. Builds without the standard library must
//! enable `no-std-io` to select the compatible `corez` I/O traits.
//!

//! The default-enabled `memory-usage` feature supplies dynamic memory-accounting
//! trait implementations. Clients that do not use them may omit the feature.
//!

#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]
// Catch documentation errors caused by code changes.
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(unsafe_code)]

#[macro_use]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

mod address;
pub mod builder;
pub mod bundle;
mod once;

#[cfg(feature = "circuit")]
pub mod circuit;
pub mod constants;
pub mod group_hash;
pub mod keys;
pub mod note;
pub mod note_encryption;
#[cfg(feature = "zip32")]
pub mod pczt;
pub mod pedersen_hash;
#[cfg(feature = "circuit")]
pub mod prover;
#[cfg(test)]
mod rng_compat;
mod spec;
mod tree;
pub mod util;
pub mod value;
#[cfg(feature = "circuit")]
mod verifier;
#[cfg(feature = "zip32")]
pub mod zip32;

pub use address::PaymentAddress;
pub use bundle::Bundle;
pub use keys::{Diversifier, NullifierDerivingKey, ProofGenerationKey, SaplingIvk, ViewingKey};
pub use note::{Note, Rseed, nullifier::Nullifier};
pub use tree::{
    Anchor, CommitmentTree, IncrementalWitness, MerklePath, NOTE_COMMITMENT_TREE_DEPTH, Node,
    merkle_hash,
};

#[cfg(feature = "circuit")]
pub use verifier::{BatchValidator, PreparedBatchVerifyingKeys, SaplingVerificationContext};

#[cfg(any(test, feature = "test-dependencies"))]
#[cfg_attr(docsrs, doc(cfg(feature = "test-dependencies")))]
pub mod testing {
    pub use super::{
        address::testing::arb_payment_address, keys::testing::arb_incoming_viewing_key,
        note::testing::arb_note, tree::testing::arb_node,
    };
}

#[cfg(test)]
mod test_vectors;

#[cfg(all(not(feature = "std"), not(feature = "no-std-io")))]
compile_error!("enable either `std` or `no-std-io` for I/O support");

#[cfg(feature = "std")]
pub(crate) use std::io;

#[cfg(all(not(feature = "std"), feature = "no-std-io"))]
pub(crate) use corez::io;
