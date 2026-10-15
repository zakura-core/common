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
//!
//! Disabling `pczt` (by turning off default features) removes the `bip32` dependency,
//! which a consumer that only parses, validates, or builds coinbase transparent bundles
//! does not need.
//!

//! Standard builds use `std::io`. Builds without the standard library must
//! enable `no-std-io` to select the compatible `corez` I/O traits.
//!

//! The default-enabled `zip32` feature supplies wallet derivation APIs.
//! Clients selecting features explicitly may omit it for verification and
//! coinbase construction; wallet input and PCZT features imply it.
//!

//! The default-enabled `memory-usage` feature supplies dynamic memory-accounting
//! trait implementations. Clients that do not use them may omit the feature.
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
pub mod sighash;
pub mod util;
#[cfg(feature = "transparent-inputs")]
pub mod zip48;

#[cfg(all(test, feature = "transparent-inputs"))]
mod test_vectors;

#[macro_use]
extern crate alloc;

#[cfg(all(not(feature = "std"), not(feature = "no-std-io")))]
compile_error!("enable either `std` or `no-std-io` for I/O support");

#[cfg(feature = "std")]
pub(crate) use std::io;

#[cfg(all(not(feature = "std"), feature = "no-std-io"))]
pub(crate) use corez::io;
