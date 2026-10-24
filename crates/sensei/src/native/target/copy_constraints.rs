//! Prepared copy-constraint cycles and active permutation edges.
//!
//! Both views derive from the validated, column-major sigma map. Copy classes
//! serve preflight equality checks; edge schedules omit identity factors while
//! preserving the permutation product for every witness and challenge.

use alloc::vec::Vec;
use sensei_shared::{N, PERMUTATION_CHUNK_LEN, USABLE_ROWS_END};

use super::TargetError;

/// Rows of one permutation chunk carrying at least one nontrivial copy edge.
///
/// A cell whose `sigma_mapping` entry points at itself contributes identical
/// numerator and denominator factors to its chunk's grand product for every
/// witness and challenge, so only the rows and columns listed here have to be
/// materialized when constructing z.
pub(crate) struct ChunkEdgeSchedule {
    /// `(row, mask)` pairs in ascending row order; bit `i` of `mask` marks
    /// chunk column `i` as having `sigma != id` at that row.
    pub(super) active_rows: Vec<(u16, u8)>,
}

impl ChunkEdgeSchedule {
    pub(crate) fn active_rows(&self) -> &[(u16, u8)] {
        &self.active_rows
    }
}

/// Copy classes of the permutation argument: the nontrivial cycles of the
/// prepared sigma permutation, each holding one logical witness value.
///
/// Cells are column-major indices `column * N + row` over the permutation
/// columns. Classes are listed in ascending order of their canonical cell,
/// and each class lists its members in cycle order starting from the
/// canonical (smallest) member, so every value shared through copy
/// constraints has a single canonical source cell. Fixed points
/// (`sigma == id`) carry no copy information and belong to no class.
pub(crate) struct CopyClasses {
    /// Concatenated member lists, each class led by its canonical cell.
    pub(super) members: Vec<u16>,
    /// Class boundaries: class `i` is `members[starts[i]..starts[i + 1]]`.
    pub(super) starts: Vec<u32>,
}

impl CopyClasses {
    pub(crate) fn classes(&self) -> impl Iterator<Item = &[u16]> {
        self.starts
            .windows(2)
            .map(|window| &self.members[window[0] as usize..window[1] as usize])
    }

    #[cfg(test)]
    pub(crate) fn member_count(&self) -> usize {
        self.members.len()
    }
}

/// Decomposes the validated sigma permutation into its nontrivial cycles.
/// Scanning cells in ascending order makes each cycle's first-visited cell
/// its smallest, i.e. the canonical member.
pub(super) fn derive_copy_classes(sigma_mapping: &[[u16; N]]) -> Result<CopyClasses, TargetError> {
    let cell_count = sigma_mapping.len() * N;
    let target_of = |cell: usize| -> Result<usize, TargetError> {
        let target = sigma_mapping
            .get(cell / N)
            .and_then(|column| column.get(cell % N))
            .ok_or(TargetError::Malformed)?;
        let target = usize::from(*target);
        if target >= cell_count {
            return Err(TargetError::Malformed);
        }
        Ok(target)
    };

    let mut visited = alloc::vec![ false; cell_count];
    let mut members = Vec::with_capacity(cell_count);
    let mut starts = alloc::vec![0u32];
    starts.reserve_exact(cell_count / 2);
    for start_cell in 0..cell_count {
        if visited[start_cell] || target_of(start_cell)? == start_cell {
            visited[start_cell] = true;
            continue;
        }
        let mut cell = start_cell;
        loop {
            // The parser validated a bijection, so a cycle can only revisit
            // its own start.
            if visited[cell] {
                return Err(TargetError::Malformed);
            }
            visited[cell] = true;
            members.push(cell as u16);
            cell = target_of(cell)?;
            if cell == start_cell {
                break;
            }
        }
        starts.push(members.len() as u32);
    }
    Ok(CopyClasses { members, starts })
}

pub(super) fn derive_permutation_edge_schedule(
    sigma_mapping: &[[u16; N]],
) -> Result<Vec<ChunkEdgeSchedule>, TargetError> {
    const {
        assert!(PERMUTATION_CHUNK_LEN <= u8::BITS as usize);
    }
    sigma_mapping
        .chunks(PERMUTATION_CHUNK_LEN)
        .enumerate()
        .map(|(chunk_index, chunk)| {
            let mut active_rows = Vec::with_capacity(USABLE_ROWS_END);
            for row in 0..N {
                let mut mask = 0u8;
                for (offset, column) in chunk.iter().enumerate() {
                    let column_index = chunk_index * PERMUTATION_CHUNK_LEN + offset;
                    if usize::from(column[row]) != column_index * N + row {
                        mask |= 1 << offset;
                    }
                }
                if mask != 0 {
                    // The grand-product scan writes blinding rows over the
                    // tail, so copies must stay inside the usable region.
                    if row >= USABLE_ROWS_END {
                        return Err(TargetError::Malformed);
                    }
                    active_rows.push((row as u16, mask));
                }
            }
            Ok(ChunkEdgeSchedule { active_rows })
        })
        .collect()
}
