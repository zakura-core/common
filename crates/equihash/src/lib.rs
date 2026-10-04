//! Equihash is a Proof-of-Work algorithm based on a generalization of the
//! Birthday problem that finds colliding hash values. It was designed to be
//! memory-hard: memory bandwidth is the bottleneck for parallel solvers.
//!
//! This crate implements Equihash as specified for the Zcash consensus rules.
//! It verifies solutions for `(n, k)` parameters where `n` is a multiple of 8
//! and of `k + 1`, `3 <= k < n`, `n <= 512`, and the collision length
//! `n / (k + 1)` is between 8 and 24 bits. The inputs must be a Zcash block
//! header and nonce.
//!
//! ## Feature flags
//!
//! - **`solver`** — Experimental pure Rust Tromp solver support.
//!   Enables runtime CPU detection in the Rust BLAKE2b backend.
//!
//! References
//! ==========
//! - [Section 7.6.1: Equihash.] Zcash Protocol Specification, version 2020.1.10
//!   or later.
//! - Alex Biryukov and Dmitry Khovratovich.
//!   [*Equihash: Asymmetric Proof-of-Work Based on the Generalized Birthday
//!   Problem.*][BK16]
//!   NDSS ’16.
//!
//! [Section 7.6.1: Equihash.]: https://zips.z.cash/protocol/protocol.pdf#equihash
//! [BK16]: https://www.internetsociety.org/sites/default/files/blogs-media/equihash-asymmetric-proof-of-work-based-generalized-birthday-problem.pdf

// Catch documentation errors caused by code changes.
#![deny(rustdoc::broken_intra_doc_links)]
#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, doc(auto_cfg))]

#[cfg(feature = "std")]
extern crate std;

#[macro_use]
extern crate alloc;

const BLAKE2B_PERSONALIZATION_PREFIX: [u8; 8] = *b"ZcashPoW";

mod leaf_hash;
mod minimal;
mod params;
mod verify;

#[cfg(test)]
mod test_vectors;

pub use verify::{Error, is_valid_solution};

#[cfg(feature = "solver")]
mod blake2b;
#[cfg(feature = "solver")]
pub mod tromp;
