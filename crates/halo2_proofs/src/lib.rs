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

#[cfg(feature = "batch")]
use ff::PrimeField;

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
// Signed width four retains eight positive magnitudes per positioned window.
#[cfg(feature = "batch")]
const PREPARED_FIXED_BASE_WINDOW_BITS: usize = 4;
#[cfg(feature = "batch")]
const PREPARED_FIXED_BASE_WINDOW_MAGNITUDES: usize = 1 << (PREPARED_FIXED_BASE_WINDOW_BITS - 1);
#[cfg(feature = "batch")]
const fn prepared_fixed_base_window_count(scalar_bits: usize) -> usize {
    // Reserve a carry-only window exactly when the scalar bit length ends on a
    // window boundary. A partial high window cannot carry out.
    scalar_bits / PREPARED_FIXED_BASE_WINDOW_BITS + 1
}
#[cfg(feature = "batch")]
const PREPARED_IPA_MASK_K: u32 = 11;
#[cfg(feature = "batch")]
const PREPARED_IPA_MASK_BASES: usize = PREPARED_IPA_MASK_K as usize + 2;
// Each cached row retains 255 affine points, so this bounds the Pasta cache at
// just under one MiB while covering Orchard's ten-row instance columns.
#[cfg(feature = "batch")]
const MAX_CACHED_INSTANCE_ROWS: usize = 64;

#[cfg(feature = "batch")]
#[derive(Clone, Copy)]
enum ScalarByteOrder {
    LittleEndian,
    BigEndian,
    Unsupported,
}

#[cfg(feature = "batch")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PreparedFixedBaseDigit {
    magnitude: usize,
    negative: bool,
}

#[cfg(feature = "batch")]
fn prepared_fixed_base_scalar_bit(bytes: &[u8], bit: usize, byte_order: ScalarByteOrder) -> bool {
    let byte_from_edge = bit / u8::BITS as usize;
    let byte = match byte_order {
        ScalarByteOrder::LittleEndian => bytes[byte_from_edge],
        ScalarByteOrder::BigEndian => bytes[bytes.len() - byte_from_edge - 1],
        ScalarByteOrder::Unsupported => unreachable!("byte order checked by caller"),
    };
    byte & (1 << (bit % u8::BITS as usize)) != 0
}

#[cfg(feature = "batch")]
fn prepared_fixed_base_scalar_digit(
    bytes: &[u8],
    window: usize,
    scalar_bits: usize,
    byte_order: ScalarByteOrder,
) -> PreparedFixedBaseDigit {
    let bit_start = window * PREPARED_FIXED_BASE_WINDOW_BITS;
    debug_assert_eq!(u8::BITS as usize % PREPARED_FIXED_BASE_WINDOW_BITS, 0);
    let value = if bit_start < scalar_bits {
        let byte_from_edge = bit_start / u8::BITS as usize;
        let byte = match byte_order {
            ScalarByteOrder::LittleEndian => bytes[byte_from_edge],
            ScalarByteOrder::BigEndian => bytes[bytes.len() - byte_from_edge - 1],
            ScalarByteOrder::Unsupported => unreachable!("byte order checked by caller"),
        };
        let bit_offset = bit_start % u8::BITS as usize;
        let live_bits = (scalar_bits - bit_start).min(PREPARED_FIXED_BASE_WINDOW_BITS);
        let mask = (1 << live_bits) - 1;
        (usize::from(byte) >> bit_offset) & mask
    } else {
        0
    };
    let overlap = if bit_start == 0 {
        0
    } else {
        usize::from(prepared_fixed_base_scalar_bit(
            bytes,
            bit_start - 1,
            byte_order,
        ))
    };

    // The bit below each window is its carry-in, while the window's high bit
    // is its carry-out. These terms cancel between adjacent windows, leaving a
    // signed digit whose magnitude is at most half the radix.
    let radix = PREPARED_FIXED_BASE_WINDOW_MAGNITUDES * 2;
    if value < radix / 2 {
        PreparedFixedBaseDigit {
            magnitude: value + overlap,
            negative: false,
        }
    } else {
        let magnitude = radix - value - overlap;
        PreparedFixedBaseDigit {
            magnitude,
            negative: magnitude != 0,
        }
    }
}

/// Positioned signed-width-four multiples for a fixed sequence of bases.
#[cfg(feature = "batch")]
struct PreparedFixedBaseTable<C: pasta_curves::arithmetic::CurveAffine> {
    points: Vec<C>,
    scalar_bits: usize,
    windows: usize,
    byte_order: ScalarByteOrder,
    bases: usize,
}

#[cfg(feature = "batch")]
impl<C: pasta_curves::arithmetic::CurveAffine> PreparedFixedBaseTable<C> {
    fn scalar_representations<'a>(
        &self,
        scalars: impl IntoIterator<Item = &'a C::Scalar>,
    ) -> Option<Vec<<C::Scalar as ff::PrimeField>::Repr>>
    where
        C::Scalar: 'a,
    {
        if matches!(self.byte_order, ScalarByteOrder::Unsupported) {
            return None;
        }

        scalars
            .into_iter()
            .map(|scalar| {
                let repr = scalar.to_repr();
                let bytes = repr.as_ref();
                let repr_bits = bytes.len().checked_mul(u8::BITS as usize)?;
                if self.scalar_bits > repr_bits
                    || (self.scalar_bits..repr_bits)
                        .any(|bit| prepared_fixed_base_scalar_bit(bytes, bit, self.byte_order))
                {
                    return None;
                }

                // [`PrimeField::Repr`] is opaque. The construction-time probe
                // only selects a candidate order; validate every scalar before
                // its digits index the positioned table.
                let decoded = match self.byte_order {
                    ScalarByteOrder::LittleEndian => {
                        decode_scalar_repr::<C::Scalar>(bytes.iter().rev().copied())
                    }
                    ScalarByteOrder::BigEndian => {
                        decode_scalar_repr::<C::Scalar>(bytes.iter().copied())
                    }
                    ScalarByteOrder::Unsupported => unreachable!("checked above"),
                };
                (decoded == *scalar).then_some(repr)
            })
            .collect()
    }

    fn point(&self, base: usize, window: usize, digit: PreparedFixedBaseDigit) -> Option<C> {
        if digit.magnitude == 0 {
            return None;
        }
        debug_assert!(base < self.bases);
        debug_assert!(window < self.windows);
        debug_assert!(digit.magnitude <= PREPARED_FIXED_BASE_WINDOW_MAGNITUDES);
        let index = (base * self.windows + window) * PREPARED_FIXED_BASE_WINDOW_MAGNITUDES
            + digit.magnitude
            - 1;
        let point = self.points[index];
        Some(if digit.negative { -point } else { point })
    }
}

/// Positioned fixed-window powers for the dense public-instance rows.
///
/// Each row stores every positive signed-digit magnitude after its positional
/// shift, so online evaluation consists only of table lookups, affine
/// negations, and mixed additions. The eight possible Boolean-row
/// contributions are pre-added to `w` and retained alongside the table.
#[cfg(feature = "batch")]
struct PreparedInstanceTable<C: pasta_curves::arithmetic::CurveAffine> {
    fixed_base: PreparedFixedBaseTable<C>,
    offsets: [C::Curve; PREPARED_INSTANCE_OFFSETS],
}

#[cfg(feature = "batch")]
trait PreparedCommitmentTables<C: pasta_curves::arithmetic::CurveAffine> {
    fn instance_window_table(&self, base_count: usize) -> std::sync::Arc<Vec<C>>;

    fn prepare_instance_table(&self) -> bool;

    fn prepared_instance_table(&self) -> Option<std::sync::Arc<PreparedInstanceTable<C>>>;

    fn prepare_ipa_mask_table(&self) -> bool;

    fn prepared_ipa_mask_table(&self) -> Option<std::sync::Arc<PreparedFixedBaseTable<C>>>;
}
