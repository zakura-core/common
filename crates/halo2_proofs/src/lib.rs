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

// Selector families smaller than this are cheaper to evaluate directly.
const MIN_SELECTOR_FAMILY_LEN: usize = 4;

#[cfg(feature = "batch")]
const INSTANCE_WINDOW_BITS: usize = 8;
#[cfg(feature = "batch")]
const INSTANCE_WINDOW_ENTRIES_PER_BASE: usize = (1 << INSTANCE_WINDOW_BITS) - 1;
// Each cached row retains 255 affine points, so this bounds the Pasta cache at
// just under one MiB while covering Orchard's ten-row instance columns.
#[cfg(feature = "batch")]
const MAX_CACHED_INSTANCE_ROWS: usize = 64;

#[cfg(feature = "batch")]
trait InstanceWindowTable<C: pasta_curves::arithmetic::CurveAffine> {
    fn instance_window_table(&self, base_count: usize) -> std::sync::Arc<Vec<C>>;
}
