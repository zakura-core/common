//! *A crate for Zcash key and address management.*
//!
//! `zcash_keys` contains Rust structs, traits and functions for creating Zcash spending
//! and viewing keys and addresses.
//!
//! ## Feature flags
//!
//! ### ZIP 32 addresses
//!
//! The default-enabled `zip32-addresses` feature provides indexed address
//! generation and diversifier-index recovery using FF1. Consumers that disable
//! default features must enable it explicitly to use these wallet APIs. Direct
//! address construction from diversifiers, key derivation, and note decryption
//! remain available without it.
//!

#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, doc(auto_cfg))]
// Catch documentation errors caused by code changes.
#![deny(rustdoc::broken_intra_doc_links)]

#[macro_use]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

pub mod address;
pub mod encoding;

#[cfg(any(
    feature = "orchard",
    feature = "sapling",
    feature = "transparent-inputs"
))]
pub mod keys;
