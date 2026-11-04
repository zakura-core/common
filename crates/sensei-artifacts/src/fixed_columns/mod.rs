//! Reconstruct and compress the sparse rows of fixed columns 3 through 11.
//!
//! `window_rows` supplies digit-interpolation coefficients and pinned `z`
//! values; `constants` supplies the cells loaded through copy constraints.
//! This module merges those sources, rejects collisions, and assigns tuple
//! indices in first-use order while walking absolute rows in ascending order.
//! The dense fixed-column layout remains in `sensei_shared::fixed_columns`.

use std::collections::{BTreeMap, HashMap};

use bento::bytes_of_slice;
use sensei_shared::{
    N, RowAssignment,
    fixed_columns::{
        FIXED_TUPLE_ASSIGNMENTS, FIXED_TUPLE_COUNT, TUPLE_FIXED_COLUMN_START, TUPLE_FIXED_COLUMNS,
    },
};
use udon::field::Fp;

use crate::{Error, context::Context, normalize_stored_montgomery};

use self::{constants::global_constant_cells, window_rows::fixed_base_window_rows};

mod constants;
mod poseidon_constants;
mod window_rows;

/// The sparse fixed rows in their stored artifact forms: the first-use
/// dictionary of distinct nonzero row tuples, and the strictly row-ascending
/// assignments referencing it.
pub(crate) struct SparseFixedRows {
    /// Distinct tuples in first-use order; tuple slots start at fixed column 3.
    pub(crate) tuples: Box<[[Fp; TUPLE_FIXED_COLUMNS]; FIXED_TUPLE_COUNT]>,
    /// Absolute rows in ascending order, each referencing an index in `tuples`.
    pub(crate) assignments: Box<[RowAssignment; FIXED_TUPLE_ASSIGNMENTS]>,
}

/// Rebuilds the sparse fixed rows from circuit-description source and
/// compresses them into the frozen dictionary encoding, failing closed on any
/// construction failure, cell collision, or shape change.
pub(crate) fn sparse_fixed_rows() -> Result<SparseFixedRows, Error> {
    // The dense (row -> tuple) view, rows ascending.
    let mut rows: BTreeMap<usize, [Fp; TUPLE_FIXED_COLUMNS]> = BTreeMap::new();
    let window_rows = fixed_base_window_rows()
        .ok_or_else(|| Error::new("window-row construction failed on the pinned inputs"))?;
    for (row, tuple) in window_rows {
        if row >= N || rows.insert(row, tuple).is_some() {
            return Err(Error::new(format!(
                "window row {row} out of range or repeated"
            )));
        }
    }
    for cell in global_constant_cells() {
        let column = cell
            .column
            .checked_sub(TUPLE_FIXED_COLUMN_START)
            .filter(|column| *column < TUPLE_FIXED_COLUMNS)
            .ok_or_else(|| {
                Error::new(format!("constant cell column {} out of range", cell.column))
            })?;
        if cell.row >= N {
            return Err(Error::new(format!(
                "constant cell row {} out of range",
                cell.row
            )));
        }
        let slot = &mut rows
            .entry(cell.row)
            .or_insert([<Fp>::ZERO; TUPLE_FIXED_COLUMNS])[column];
        if !slot.is_zero() {
            return Err(Error::new(format!(
                "constant cell ({}, {}) collides with an existing value",
                cell.row, cell.column
            )));
        }
        *slot = cell.value;
    }

    // First-use dictionary compression, exactly the frozen encoding.
    // Only the BTreeMap determines traversal order. The HashMap is a lookup
    // index and is never iterated, so its random seed cannot affect bytes.
    let mut tuples = Vec::with_capacity(FIXED_TUPLE_COUNT);
    let mut assignments = Vec::with_capacity(FIXED_TUPLE_ASSIGNMENTS);
    let mut indices: HashMap<[[u64; 4]; TUPLE_FIXED_COLUMNS], u16> = HashMap::new();
    for (row, tuple) in rows {
        let key = tuple.map(|value| value.reduce().montgomery_limbs());
        let next = u16::try_from(tuples.len())
            .map_err(|_| Error::new("tuple dictionary exceeds u16 indices"))?;
        let index = *indices.entry(key).or_insert_with(|| {
            tuples.push(tuple);
            next
        });
        let row = u16::try_from(row).expect("rows are bounded by N");
        assignments.push(RowAssignment { row, tuple: index });
    }
    if tuples.len() != FIXED_TUPLE_COUNT || assignments.len() != FIXED_TUPLE_ASSIGNMENTS {
        return Err(Error::new(format!(
            "sparse fixed rows changed shape: {} tuples, {} assignments",
            tuples.len(),
            assignments.len()
        )));
    }
    Ok(SparseFixedRows {
        tuples: tuples
            .into_boxed_slice()
            .try_into()
            .unwrap_or_else(|_| unreachable!("the tuple count was just checked")),
        assignments: assignments
            .into_boxed_slice()
            .try_into()
            .unwrap_or_else(|_| unreachable!("the assignment count was just checked")),
    })
}

/// Generates the exact bytes of the fixed-tuples artifact in the
/// `mont-u64x4` stored form (the fixed layout of [`Fp`]).
pub(crate) fn generate_tuples(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    let mut tuples = context.sparse_rows()?.tuples.clone();
    normalize_stored_montgomery(tuples.as_flattened_mut());
    Ok(bytes_of_slice(&tuples[..]).to_vec())
}

/// Generates the exact bytes of the tuple-assignments artifact.
pub(crate) fn generate_assignments(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    Ok(bytes_of_slice(&context.sparse_rows()?.assignments[..]).to_vec())
}
