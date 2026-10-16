//! Implementation of the Pallas / Vesta curve cycle.
//!
//! # Assembly selection
//!
//! The `portable` feature disables all handwritten assembly on every platform,
//! overriding both `aarch64-asm` and `x86_64-asm` and automatic x86 selection.
//! It also prevents compilation and linking of the AArch64 assembly archive.
//!
//! # Timing
//!
//! This crate does not guarantee constant-time field or curve arithmetic.
//! In particular, curve addition and batch normalization branch on identity
//! and exceptional cases, and field inversion is variable-time. Scalar
//! multiplication uses these curve operations internally. Callers whose
//! threat model requires secret-independent execution must use a separately
//! audited constant-time implementation.

#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![allow(unknown_lints)]
#![allow(clippy::op_ref, clippy::same_item_push, clippy::upper_case_acronyms)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(unsafe_code)]

#[cfg(all(
    feature = "portable",
    any(pasta_curves_x86_64_asm, pasta_curves_aarch64_asm)
))]
compile_error!("portable must disable every Pasta assembly backend");

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(test)]
#[macro_use]
extern crate std;

#[macro_use]
mod macros;
mod curves;
mod fields;
#[cfg(feature = "sqrt-table")]
mod once;

pub mod arithmetic;
#[cfg(feature = "deferred")]
#[cfg_attr(docsrs, doc(cfg(feature = "deferred")))]
pub mod deferred;
pub mod pallas;
pub mod vesta;

#[cfg(feature = "glv")]
#[cfg_attr(docsrs, doc(cfg(feature = "glv")))]
pub mod glv;

#[cfg(feature = "alloc")]
mod hashtocurve;

#[cfg(feature = "serde")]
mod serde_impl;

pub use curves::*;
pub use fields::*;

pub extern crate group;

#[cfg(feature = "alloc")]
#[test]
fn test_endo_consistency() {
    use crate::arithmetic::CurveExt;
    use group::{Group, ff::WithSmallOrderMulGroup};

    let a = pallas::Point::generator();
    assert_eq!(a * pallas::Scalar::ZETA, a.endo());
    let a = vesta::Point::generator();
    assert_eq!(a * vesta::Scalar::ZETA, a.endo());
}
