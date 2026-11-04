//! Decode the column-major permutation map and encode its integer artifact.
//!
//! A cell stores its target as `column * N + row`. Validation checks the
//! exact length, range, and bijectivity; circuit-specific copy constraints
//! are checked by the prover's embedded-data tests. No field representation
//! is involved in the output, so its registry entry has no stored form.

use bento::bytes_of_slice;
use sensei_shared::{N, PERMUTATION_COLUMN_COUNT};

use crate::{Error, RawStore};

/// Raw little-endian target-cell indices, grouped by source column.
pub(crate) const SIGMA_MAP: &str = "sigma-map.cells";

/// Little-endian target-cell index width.
const CELL_BYTES: usize = 2;

/// Decodes and validates the permutation map: a bijection on the
/// `PERMUTATION_COLUMN_COUNT * N` target cells in column-major indexing.
pub(crate) fn sigma_map(raw: &RawStore) -> Result<Vec<[u16; N]>, Error> {
    let bytes = raw.bytes(SIGMA_MAP)?;
    let cells = PERMUTATION_COLUMN_COUNT * N;
    if bytes.len() != cells * CELL_BYTES {
        return Err(Error::new(format!(
            "raw input {SIGMA_MAP}: expected {} bytes, found {}",
            cells * CELL_BYTES,
            bytes.len()
        )));
    }
    let mut seen = vec![false; cells];
    let mut mapping = Vec::with_capacity(PERMUTATION_COLUMN_COUNT);
    for column_bytes in bytes.chunks_exact(N * CELL_BYTES) {
        let mut column = [0u16; N];
        for (value, record) in column.iter_mut().zip(column_bytes.chunks_exact(CELL_BYTES)) {
            *value = u16::from_le_bytes(record.try_into().expect("2-byte cell"));
            let target = usize::from(*value);
            if target >= cells || seen[target] {
                return Err(Error::new(format!(
                    "raw input {SIGMA_MAP}: target cell {target} out of range or repeated"
                )));
            }
            seen[target] = true;
        }
        mapping.push(column);
    }
    Ok(mapping)
}

/// Generates the exact bytes of the sigma-map artifact.
pub(crate) fn generate(context: &crate::context::Context<'_>) -> Result<Vec<u8>, Error> {
    Ok(bytes_of_slice(context.sigma_map()?).to_vec())
}
