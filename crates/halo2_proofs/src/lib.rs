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

#[cfg(any(feature = "batch", all(feature = "multicore", not(feature = "orbits"))))]
fn decode_scalar_repr<F: ff::PrimeField>(mut bytes: impl ExactSizeIterator<Item = u8>) -> F {
    const LIMB_BYTES: usize = core::mem::size_of::<u64>();

    // Callers supply bytes most-significant first. Decode a limb at a time so
    // validating an opaque [`PrimeField::Repr`] needs four field operations
    // for the 32-byte Pasta representation rather than one per byte.
    let radix = F::from(u64::MAX) + F::ONE;
    let mut bytes_in_limb = bytes.len() % LIMB_BYTES;
    if bytes_in_limb == 0 {
        bytes_in_limb = LIMB_BYTES;
    }
    let mut decoded = None;
    let mut limb = 0u64;
    for byte in &mut bytes {
        limb = (limb << u8::BITS) | u64::from(byte);
        bytes_in_limb -= 1;
        if bytes_in_limb == 0 {
            let limb_value = F::from(limb);
            decoded = Some(match decoded {
                Some(decoded) => decoded * radix + limb_value,
                None => limb_value,
            });
            limb = 0;
            bytes_in_limb = LIMB_BYTES;
        }
    }
    decoded.unwrap_or(F::ZERO)
}

// Selector families smaller than this are cheaper to evaluate directly.
const MIN_SELECTOR_FAMILY_LEN: usize = 4;

#[cfg(feature = "batch")]
const INSTANCE_WINDOW_BITS: usize = 8;
#[cfg(feature = "batch")]
const INSTANCE_WINDOW_ENTRIES_PER_BASE: usize = (1 << INSTANCE_WINDOW_BITS) - 1;
// Orchard's current public instance has seven full-width field elements
// followed by three Boolean flags. The fixed-base prover path is deliberately
// restricted to this exact shape.
#[cfg(feature = "batch")]
const PREPARED_INSTANCE_COLUMNS: usize = 1;
#[cfg(feature = "batch")]
const PREPARED_INSTANCE_DENSE_ROWS: usize = 7;
#[cfg(feature = "batch")]
const PREPARED_INSTANCE_BOOLEAN_ROWS: usize = 3;
#[cfg(feature = "batch")]
const PREPARED_INSTANCE_ROWS: usize = PREPARED_INSTANCE_DENSE_ROWS + PREPARED_INSTANCE_BOOLEAN_ROWS;
#[cfg(feature = "batch")]
const PREPARED_INSTANCE_OFFSETS: usize = 1 << PREPARED_INSTANCE_BOOLEAN_ROWS;
// Signed width four retains about 224 KiB for Pasta and needs at most 64
// additions per dense scalar.
#[cfg(feature = "batch")]
const PREPARED_INSTANCE_WINDOW_BITS: usize = 4;
#[cfg(feature = "batch")]
const PREPARED_INSTANCE_WINDOW_MAGNITUDES: usize = 1 << (PREPARED_INSTANCE_WINDOW_BITS - 1);
#[cfg(feature = "batch")]
const fn prepared_instance_window_count(scalar_bits: usize) -> usize {
    // Reserve a carry-only window exactly when the scalar bit length ends on a
    // window boundary. A partial high window cannot carry out.
    scalar_bits / PREPARED_INSTANCE_WINDOW_BITS + 1
}
// Each cached row retains 255 affine points, so this bounds the Pasta cache at
// just under one MiB while covering Orchard's ten-row instance columns.
#[cfg(feature = "batch")]
const MAX_CACHED_INSTANCE_ROWS: usize = 64;

#[cfg(feature = "batch")]
#[derive(Clone, Copy)]
enum InstanceScalarByteOrder {
    LittleEndian,
    BigEndian,
    Unsupported,
}

/// Positioned fixed-window powers for the dense public-instance rows.
///
/// Each row stores every positive signed-digit magnitude after its positional
/// shift, so online evaluation consists only of table lookups, affine
/// negations, and mixed additions. The eight possible Boolean-row
/// contributions are pre-added to `w` and retained alongside the table.
#[cfg(feature = "batch")]
struct PreparedInstanceTable<C: pasta_curves::arithmetic::CurveAffine> {
    points: Vec<C>,
    scalar_bits: usize,
    windows: usize,
    byte_order: InstanceScalarByteOrder,
    offsets: [C::Curve; PREPARED_INSTANCE_OFFSETS],
}

#[cfg(feature = "batch")]
trait InstanceWindowTable<C: pasta_curves::arithmetic::CurveAffine> {
    fn instance_window_table(&self, base_count: usize) -> std::sync::Arc<Vec<C>>;

    fn prepare_instance_table(&self) -> bool;

    fn prepared_instance_table(&self) -> Option<std::sync::Arc<PreparedInstanceTable<C>>>;
}
