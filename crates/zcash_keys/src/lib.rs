//! *A crate for Zcash key and address management.*
//!
//! `zcash_keys` contains Rust structs, traits and functions for creating Zcash spending
//! and viewing keys and addresses.
//!
//! ## Feature flags
//!
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

#[cfg(all(not(feature = "std"), not(feature = "no-std-io")))]
compile_error!("enable either `std` or `no-std-io` for I/O support");

#[allow(unused_imports)]
#[cfg(feature = "std")]
pub(crate) use std::io;

#[allow(unused_imports)]
#[cfg(all(not(feature = "std"), feature = "no-std-io"))]
pub(crate) use corez::io;
