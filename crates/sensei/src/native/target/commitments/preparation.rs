//! Circuit-specific structured bases for parameter preparation.
//!
//! The parent composes these recipes in [`super::Parameters::over_srs`]. Shared
//! records and their runtime scalar handling stay beside the commitment jobs.

use alloc::vec::Vec;
use sensei_shared::fixed_bases::FIXED_BASE_WINDOW_SIZE;
use sensei_shared::{ADVICE_COLUMNS, N, USABLE_ROWS_END};

use crate::native::commitment::{FixedGenerator, normalized, sum_prepared};
use crate::native::curve::{PreparedAffinePoint, Vesta, VestaAffine, VestaProjective};
use crate::native::field::Fp;
use crate::native::regions::{constant_cells, fixed_base_windows, variable_base_mul};

use super::{BitColumnBases, ConstantColumn, TargetError, WindowSelection, WordColumnBases};

/// Derives every eligible column's constant offset from the Lagrange
/// generators and the writer-derived constant inventory. Only columns in
/// `copied_columns` — those another carve-out already copies for the batch —
/// take part: copying a whole column to save a handful of terms would cost
/// more than it saves. Rows must be distinct usable rows.
pub(super) fn prepare_constant_columns(
    lagrange: &[PreparedAffinePoint<Vesta>],
    copied_columns: &[usize],
) -> Result<Vec<ConstantColumn>, TargetError> {
    let inventory = constant_cells::nonzero_constants();
    if lagrange.len() != N
        || inventory.iter().any(|(column, row, value)| {
            *column >= ADVICE_COLUMNS || *row >= USABLE_ROWS_END || value.is_zero()
        })
    {
        return Err(TargetError::Malformed);
    }
    let mut cells = inventory
        .iter()
        .map(|(column, row, _)| (*column, *row))
        .collect::<Vec<_>>();
    cells.sort_unstable();
    if cells.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(TargetError::Malformed);
    }
    let mut columns = Vec::with_capacity(copied_columns.len());
    for &column in copied_columns {
        if columns
            .iter()
            .any(|existing: &ConstantColumn| existing.column == column)
        {
            continue;
        }
        let cells = inventory
            .iter()
            .filter(|(cell_column, _, _)| *cell_column == column)
            .map(|(_, row, value)| (*row, *value))
            .collect::<Vec<_>>();
        if cells.is_empty() {
            continue;
        }
        let bases = cells
            .iter()
            .map(|(row, _)| lagrange[*row])
            .collect::<Vec<_>>();
        let scalars = cells.iter().map(|(_, value)| *value).collect::<Vec<_>>();
        let offset = sum_prepared(&bases, &scalars).ok_or(TargetError::Malformed)?;
        columns.push(ConstantColumn {
            column,
            cells,
            offset,
        });
    }
    Ok(columns)
}

/// Builds one coordinate column's window selection from the shared window
/// footprint and the writer's window tables: rows must be distinct usable
/// rows matching the embedded base count, disjoint from the column's fold
/// run when it has one.
pub(super) fn prepare_window_selection(
    window_tables: &[[sensei_shared::WindowTableEntry; 8]],
    column: usize,
    bases: &'static [VestaAffine],
    coordinate: impl Fn(&sensei_shared::WindowTableEntry) -> Fp,
) -> Result<WindowSelection, TargetError> {
    use sensei_shared::fixed_bases::{FIXED_BASE_REGIONS, FIXED_BASE_TOTAL_WINDOWS};

    let window_size = FIXED_BASE_WINDOW_SIZE as usize;
    let rows = fixed_base_windows::window_rows();
    if rows.len() != FIXED_BASE_TOTAL_WINDOWS
        || bases.len() != FIXED_BASE_TOTAL_WINDOWS * window_size
        || rows.iter().any(|row| *row >= USABLE_ROWS_END)
    {
        return Err(TargetError::Malformed);
    }
    let mut sorted = rows.clone();
    sorted.sort_unstable();
    if sorted.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(TargetError::Malformed);
    }
    if variable_base_mul::COORDINATE_COLUMNS.contains(&column) {
        let fold_rows = variable_base_mul::coordinate_rows();
        if rows.iter().any(|row| fold_rows.contains(row)) {
            return Err(TargetError::Malformed);
        }
    }

    let mut windows = Vec::with_capacity(FIXED_BASE_TOTAL_WINDOWS);
    let mut flat = 0;
    for (region, _, window_count) in FIXED_BASE_REGIONS {
        let table = crate::native::witness::fixed_base_window_table(window_tables, region);
        for window in 0..window_count {
            if let Some(entries) = table.and_then(|table| table.get(window)) {
                let values: [Fp; FIXED_BASE_WINDOW_SIZE as usize] =
                    core::array::from_fn(|digit| coordinate(&entries[digit]));
                windows.push((rows[flat], values, (flat * window_size) as u32));
            }
            flat += 1;
        }
    }
    Ok(WindowSelection {
        column,
        bases,
        windows,
    })
}

/// Derives every chain column's bases from the Lagrange generators and the
/// shared chain footprint (`H_k = G_{r_k} + 2·H_{k+1}` from the last row
/// down, `K = G_{r_0} + 2·H_1`), checking the footprint's rows are distinct
/// usable rows; every derived point must be nonidentity to have an affine
/// MSM representation (the pinned SRS satisfies this).
pub(super) fn prepare_bit_bases(
    lagrange: &[PreparedAffinePoint<Vesta>],
) -> Result<Vec<BitColumnBases>, TargetError> {
    let chains = variable_base_mul::bit_chains()
        .map(|(column, rows)| (column, rows.iter().collect::<Vec<_>>()));
    if lagrange.len() != N
        || chains.is_empty()
        || chains.iter().any(|(column, rows)| {
            *column >= ADVICE_COLUMNS
                || rows.len() < 2
                || rows.iter().any(|row| *row >= USABLE_ROWS_END)
        })
    {
        return Err(TargetError::Malformed);
    }
    let mut cells = chains
        .iter()
        .flat_map(|(column, rows)| rows.iter().map(move |row| (*column, *row)))
        .collect::<Vec<_>>();
    cells.sort_unstable();
    if cells.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(TargetError::Malformed);
    }

    let derived = (chains.clone())
        .into_iter()
        .map(move |(_, rows)| {
            // Bit bases from the last row down, then the initial-sum base.
            let mut running = VestaProjective::IDENTITY;
            let mut bit_bases = Vec::with_capacity(rows.len());
            for &row in rows.iter().skip(1).rev() {
                running = running.double().add_mixed(&lagrange[row].to_affine());
                bit_bases.push(running);
            }
            bit_bases.reverse();
            let initial = running.double().add_mixed(&lagrange[rows[0]].to_affine());
            let mut points = Vec::with_capacity(rows.len());
            points.push(initial);
            points.extend(bit_bases);
            points
        })
        .collect::<Vec<_>>();

    let mut column_order: Vec<usize> = Vec::with_capacity(ADVICE_COLUMNS);
    let mut points: Vec<Vec<VestaProjective>> = Vec::with_capacity(ADVICE_COLUMNS);
    let mut layouts: Vec<Vec<(Vec<usize>, usize)>> = Vec::with_capacity(ADVICE_COLUMNS);
    for ((column, rows), chain) in chains.iter().zip(derived) {
        let slot = match column_order.iter().position(|existing| existing == column) {
            Some(slot) => slot,
            None => {
                column_order.push(*column);
                points.push(Vec::with_capacity(
                    chains
                        .iter()
                        .filter(|(c, _)| c == column)
                        .map(|(_, rows)| rows.len())
                        .sum(),
                ));
                layouts.push(Vec::with_capacity(
                    chains.iter().filter(|(c, _)| c == column).count(),
                ));
                column_order.len() - 1
            }
        };
        layouts[slot].push((rows.clone(), points[slot].len()));
        points[slot].extend(chain);
    }
    column_order
        .into_iter()
        .zip(points)
        .zip(layouts)
        .map(|((column, points), chains)| {
            let bases = normalized(&points)
                .iter()
                .map(|point| {
                    point
                        .as_affine()
                        .copied()
                        .map(|point| PreparedAffinePoint::from_affine(&point))
                })
                .collect::<Option<Vec<_>>>()
                .ok_or(TargetError::Malformed)?;
            Ok(BitColumnBases {
                column,
                bases,
                chains,
            })
        })
        .collect()
}

/// Derives the weighted word bases of every column a piece schedule
/// touches (`(column, rows)` per piece, radix `2^word_bits`) from the
/// Lagrange generators, checking the schedule's rows are distinct usable
/// rows and its counts match the pinned totals. Each piece's chain is
/// independent; derived chains are grouped by column in schedule order.
/// Every derived point must be nonidentity to have an affine MSM
/// representation (the pinned SRS satisfies this).
pub(super) fn prepare_word_bases(
    lagrange: &[PreparedAffinePoint<Vesta>],
    pieces: Vec<(usize, core::ops::Range<usize>)>,
    word_bits: usize,
    expected_pieces: usize,
    expected_words: usize,
) -> Result<Vec<WordColumnBases>, TargetError> {
    if lagrange.len() != N
        || word_bits == 0
        || word_bits > 10
        || pieces.len() != expected_pieces
        || pieces.iter().map(|(_, rows)| rows.len()).sum::<usize>() != expected_words
        || pieces.iter().any(|(column, rows)| {
            *column >= ADVICE_COLUMNS || rows.is_empty() || rows.end > USABLE_ROWS_END
        })
    {
        return Err(TargetError::Malformed);
    }
    let mut cells = pieces
        .iter()
        .flat_map(|(column, rows)| rows.clone().map(move |row| (*column, row)))
        .collect::<Vec<_>>();
    cells.sort_unstable();
    if cells.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(TargetError::Malformed);
    }

    let chains = (pieces.clone())
        .into_iter()
        .map(move |(_, rows)| {
            let mut points = Vec::with_capacity(rows.len() + 1);
            let mut running = VestaProjective::IDENTITY;
            for row in rows {
                for _ in 0..word_bits {
                    running = running.double();
                }
                running = running.add_mixed(&lagrange[row].to_affine());
                points.push(running);
            }
            for _ in 0..word_bits {
                running = running.double();
            }
            points.push(running);
            points
        })
        .collect::<Vec<_>>();

    // Group by running-sum column, keeping schedule order within a column.
    let mut column_order: Vec<usize> = Vec::with_capacity(ADVICE_COLUMNS);
    let mut points: Vec<Vec<VestaProjective>> = Vec::with_capacity(ADVICE_COLUMNS);
    let mut piece_layouts: Vec<Vec<(core::ops::Range<usize>, usize)>> =
        Vec::with_capacity(ADVICE_COLUMNS);
    for ((column, rows), chain) in pieces.iter().zip(chains) {
        let slot = match column_order.iter().position(|existing| existing == column) {
            Some(slot) => slot,
            None => {
                column_order.push(*column);
                points.push(Vec::with_capacity(
                    pieces
                        .iter()
                        .filter(|(c, _)| c == column)
                        .map(|(_, rows)| rows.len() + 1)
                        .sum(),
                ));
                piece_layouts.push(Vec::with_capacity(
                    pieces.iter().filter(|(c, _)| c == column).count(),
                ));
                column_order.len() - 1
            }
        };
        piece_layouts[slot].push((rows.clone(), points[slot].len()));
        points[slot].extend(chain);
    }
    column_order
        .into_iter()
        .zip(points)
        .zip(piece_layouts)
        .map(|((column, points), pieces)| {
            let bases = normalized(&points)
                .iter()
                .map(|point| {
                    point
                        .as_affine()
                        .copied()
                        .map(|point| PreparedAffinePoint::from_affine(&point))
                })
                .collect::<Option<Vec<_>>>()
                .ok_or(TargetError::Malformed)?;
            Ok(WordColumnBases {
                column,
                word_bits,
                bases,
                pieces,
            })
        })
        .collect()
}

/// Derives `H = Σ_{r ∈ rows} G_r` for the variable-base gadget's repeated
/// coordinate rows from the prepared Lagrange prefix sums
/// (`P[j] = Σ_{i<j} G_i` at index `j − 1`): `H = P[rows.end] − P[rows.start]`.
/// The run must lie inside the usable prefix with a nonempty proper start so
/// both prefixes exist; the pinned SRS gives a non-identity `H` (a test
/// recomputes it from the generators directly), and an identity would have no
/// affine fixed-base preparation, so it is rejected rather than assumed away.
pub(super) fn prepare_repeated_coordinate_base(
    prefix_sums: &[PreparedAffinePoint<Vesta>],
) -> Result<FixedGenerator, TargetError> {
    let rows = variable_base_mul::coordinate_rows();
    if prefix_sums.len() != N
        || rows.start < 1
        || rows.start >= rows.end
        || rows.end > USABLE_ROWS_END
    {
        return Err(TargetError::Dimension);
    }
    let end_prefix = prefix_sums[rows.end - 1].to_affine().to_point();
    let start_prefix = prefix_sums[rows.start - 1].to_affine().neg().to_point();
    let sum = end_prefix.add(&start_prefix).to_point();
    let base = sum.as_affine().ok_or(TargetError::Malformed)?;
    Ok(FixedGenerator::configured(base, 5))
}
