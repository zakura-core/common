//! # halo2_proofs

#![cfg_attr(docsrs, feature(doc_cfg))]
// The actual lints we want to disable.
#![allow(clippy::op_ref, clippy::many_single_char_names)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(unsafe_code)]

pub mod arithmetic;
pub mod circuit;
pub use pasta_curves as pasta;
mod multicore;
pub mod plonk;
pub mod poly;
pub mod transcript;

pub mod dev;
mod helpers;

#[cfg(feature = "prover-fixed-msm-table")]
const PROVER_FIXED_MSM_TABLE_K: u32 = 11;
// Ten bases cap each full subset block at 1,023 points. For Pasta's 64-byte
// affine representation, this keeps the k = 11 table near 12.8 MiB; a wider
// block doubles storage per added base, while a narrower block adds more
// per-bit table lookups and additions.
#[cfg(feature = "prover-fixed-msm-table")]
const PROVER_FIXED_MSM_TABLE_BLOCK_BASES: usize = 10;
