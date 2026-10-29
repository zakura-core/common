//! # Zcash transparent protocol
//!
//! ## Feature flags
//!
//! - `std` (default): Enables `std` support in dependencies.
//! - `pczt` (default): The [`pczt`] module and [`builder::TransparentBuilder::build_for_pczt`].
//!   Implies `bip32`.
//! - `bip32`: Conversions between [`keys::TransparentKeyScope`] /
//!   [`keys::NonHardenedChildIndex`] and `bip32::ChildNumber`.
//! - `transparent-inputs`: Transparent key derivation and spending. Implies `pczt`.
//! - `test-dependencies`: Exposes APIs useful for testing.
//! - `pq`: SLH-DSA-SHA2-192s primitives and an explicit
//!   bounded script evaluator, with a proposed PQ identifier inside existing
//!   P2SH redeem scripts. Does not activate PQ transaction validation.
//!
//! Disabling `pczt` (by turning off default features) removes the `bip32` dependency,
//! which a consumer that only parses, validates, or builds coinbase transparent bundles
//! does not need.
//!

//! The default-enabled `wallet` feature supplies wallet derivation APIs.
//! Clients selecting features explicitly may omit it for verification and
//! coinbase construction; wallet input and PCZT features imply it.
//!

#![no_std]

#[cfg(feature = "std")]
extern crate std;

pub mod address;
pub mod builder;
pub mod bundle;
pub mod coinbase;
pub mod keys;
#[cfg(feature = "pczt")]
pub mod pczt;
#[cfg(feature = "pq")]
pub mod pq;
pub mod sighash;
pub mod util;
#[cfg(feature = "transparent-inputs")]
pub mod zip48;

#[cfg(all(test, feature = "transparent-inputs"))]
mod test_vectors;

#[macro_use]
extern crate alloc;
