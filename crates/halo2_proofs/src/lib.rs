//! # halo2_proofs
//!
//! # Timing
//!
//! Proof creation and multiexponentiation are not constant-time with respect
//! to witnesses, blinding factors, or other scalar inputs. Callers must not
//! rely on this crate for secret-independent execution.

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

#[cfg(any(feature = "batch", feature = "multicore"))]
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

#[cfg(any(feature = "batch", feature = "multicore"))]
const ORCHARD_K: u32 = 11;

#[cfg(feature = "multicore")]
const PREPARED_SPARSE_COMMITMENT_K: u32 = ORCHARD_K;

/// The Orchard-sized domain used by the sorted 10-bit range-check commitment.
#[cfg(feature = "multicore")]
const PREPARED_SORTED_U10_COMMITMENT_K: u32 = PREPARED_SPARSE_COMMITMENT_K;

/// Cached multiples `H`, `2H`, and `4H` for each Lagrange suffix sum.
#[cfg(feature = "multicore")]
const SORTED_U10_SUFFIX_MULTIPLES: usize = 3;
/// Blinded suffix terms in the permuted 10-bit range-check table.
///
/// The Pasta backend privately mirrors this value so it can reject accidental
/// callers without requiring a public cross-crate protocol constant.
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
const PERMUTED_U10_TABLE_SUFFIX_TERMS: usize = 6;

#[cfg(feature = "multicore")]
trait PreparedSparseCommitments<C: pasta_curves::arithmetic::CurveAffine> {
    fn prepare_sparse_commitment(&self) -> bool;

    fn commit_sparse(
        &self,
        coefficients: &[(usize, C::Scalar)],
        blind: poly::commitment::Blind<C::Scalar>,
    ) -> Option<C::Curve>;
}

#[cfg(feature = "multicore")]
trait PreparedLookupCommitments<C: pasta_curves::arithmetic::CurveAffine> {
    fn prepared_lagrange_suffix_multiples(&self) -> Option<&[C]>;

    #[cfg(not(feature = "orbits"))]
    fn commit_permuted_u10_table(
        &self,
        prefix: &[C::Scalar],
        suffix: &[C::Scalar],
        blind: poly::commitment::Blind<C::Scalar>,
    ) -> Option<C::Curve>;
}

// Selector families smaller than this are cheaper to evaluate directly.
const MIN_SELECTOR_FAMILY_LEN: usize = 4;

/// Maximum contiguous point runs recorded or retained for one proof layout.
/// Orchard uses three runs regardless of its action count. Capping each layout
/// bounds the 256-slot cache's range data to 128 KiB on 64-bit targets.
#[cfg(feature = "batch")]
const MAX_CACHED_PROOF_POINT_RUNS: usize = 32;

// Signed width nine needs one more cached multiple than unsigned width eight.
#[cfg(feature = "batch")]
const INSTANCE_WINDOW_BITS: usize = 9;
#[cfg(feature = "batch")]
const INSTANCE_WINDOW_ENTRIES_PER_BASE: usize = 1 << (INSTANCE_WINDOW_BITS - 1);
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
// Each cached row retains 256 affine points, so this bounds the Pasta cache at
// one MiB while covering Orchard's ten-row instance columns.
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

/// A doubling-free GLV table for the dense rows of the one-column Orchard
/// instance shape, built lazily for batch verification.
///
/// `dense` evaluates the full-width rows (see
/// [`pasta_curves::arithmetic::PreparedFixedBaseSum`]). As in
/// [`PreparedInstanceTable`], the eight possible Boolean-row contributions are
/// pre-added to `w` in `offsets`, indexed by [`instance_flag_mask`].
#[cfg(feature = "batch")]
struct GlvInstanceTable<C: pasta_curves::arithmetic::CurveAffine> {
    // The table is immutable once built and its methods take `&self`, so a
    // panic cannot leave it in a broken state; asserting unwind safety keeps
    // `Params` unwind safe, as the prepared zero-check caches do.
    dense: core::panic::AssertUnwindSafe<
        Box<dyn pasta_curves::arithmetic::PreparedFixedBaseSum<C::CurveExt>>,
    >,
    offsets: [C::Curve; PREPARED_INSTANCE_OFFSETS],
}

/// The bit mask of a one-column Orchard-shaped instance's Boolean rows, or
/// `None` if any of them is neither zero nor one.
///
/// # Panics
///
/// Panics if `instance` has fewer than [`PREPARED_INSTANCE_ROWS`] rows.
#[cfg(feature = "batch")]
fn instance_flag_mask<F: ff::Field>(instance: &[F]) -> Option<usize> {
    let mut mask = 0;
    let flags = &instance[PREPARED_INSTANCE_DENSE_ROWS
        ..PREPARED_INSTANCE_DENSE_ROWS + PREPARED_INSTANCE_BOOLEAN_ROWS];
    for (flag, scalar) in flags.iter().enumerate() {
        if bool::from(scalar.is_zero()) {
            continue;
        }
        if bool::from((*scalar - F::ONE).is_zero()) {
            mask |= 1 << flag;
        } else {
            return None;
        }
    }
    Some(mask)
}

#[cfg(feature = "batch")]
trait InstanceWindowTable<C: pasta_curves::arithmetic::CurveAffine> {
    fn instance_window_table(&self, base_count: usize) -> std::sync::Arc<Vec<C>>;

    fn prepare_instance_table(&self) -> bool;

    fn prepared_instance_table(&self) -> Option<std::sync::Arc<PreparedInstanceTable<C>>>;

    /// The GLV instance table, built on first use; `None` if the curve has no
    /// GLV backend or the parameters have too few Lagrange bases.
    fn glv_instance_table(&self) -> Option<std::sync::Arc<GlvInstanceTable<C>>>;
}
