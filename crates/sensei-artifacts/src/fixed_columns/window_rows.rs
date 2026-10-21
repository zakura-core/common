//! Host-only interpolation of the fixed-base sparse rows.
//!
//! Each scheduled window contributes one tuple: eight coefficients for the
//! polynomial taking digit `d` to the candidate point's x-coordinate, then
//! the pinned `z` value used by the window constraints. The resulting row
//! numbers are absolute circuit rows; tuple compression sorts them later.

use sensei_shared::{
    fixed_bases::{
        FIXED_BASE_REGIONS, FIXED_BASE_TOTAL_WINDOWS, FIXED_BASE_WINDOW_SIZE,
        fixed_base_window_candidates, fixed_base_window_offset,
    },
    fixed_columns::TUPLE_FIXED_COLUMNS,
    regions::REGION_STARTS,
};
use udon::{field::Fp, polynomial::InterpolationPlan};

/// Coefficients of the eight Lagrange basis polynomials on digits 0..7.
/// This map is independent of the window's candidate coordinates.
fn digit_interpolation_basis()
-> [[Fp; FIXED_BASE_WINDOW_SIZE as usize]; FIXED_BASE_WINDOW_SIZE as usize] {
    const SIZE: usize = FIXED_BASE_WINDOW_SIZE as usize;
    let digits: [_; SIZE] = core::array::from_fn(|digit| <Fp>::from_u64(digit as u64));
    let mut weights = [<Fp>::ZERO; SIZE];
    let mut scratch = [<Fp>::ZERO; SIZE];
    let plan = InterpolationPlan::prepare(&digits, &mut weights, &mut scratch)
        .expect("distinct interpolation digits and one weight per digit");
    let mut basis = [[<Fp>::ZERO; SIZE]; SIZE];
    for (i, coefficients) in basis.iter_mut().enumerate() {
        let mut values = [<Fp>::ZERO; SIZE];
        values[i] = <Fp>::ONE;
        plan.interpolate(&values, coefficients, &mut scratch)
            .expect("one value, coefficient, and scratch entry per digit");
    }
    basis
}

/// The window rows of fixed columns 3 through 11: for every window of every
/// [`FIXED_BASE_REGIONS`] slot, its absolute row and the row's nine fixed
/// values — the eight ascending interpolation coefficients of the candidate
/// x-coordinates over the digit domain, then the pinned running-sum value
/// `z`. Together with the copy-loaded constants in [`super::constants`],
/// these rows are the entire sparse content of the tuple artifacts.
pub(super) fn fixed_base_window_rows() -> Option<Vec<(usize, [Fp; TUPLE_FIXED_COLUMNS])>> {
    let basis = digit_interpolation_basis();
    let window_size = FIXED_BASE_WINDOW_SIZE as usize;
    let mut rows: Vec<(usize, [Fp; TUPLE_FIXED_COLUMNS])> =
        Vec::with_capacity(FIXED_BASE_TOTAL_WINDOWS);
    for (slot, (region, base, window_count)) in FIXED_BASE_REGIONS.into_iter().enumerate() {
        let region_start = *REGION_STARTS.get(region)?;
        if let Some(previous_slot) =
            FIXED_BASE_REGIONS[..slot]
                .iter()
                .position(|(_, previous_base, previous_count)| {
                    *previous_base == base && *previous_count == window_count
                })
        {
            let source = fixed_base_window_offset(previous_slot);
            // Interpolation depends on the base and window count; the old
            // and new note commitments differ only in their absolute rows.
            for window in 0..window_count {
                rows.push((region_start.checked_add(window)?, rows[source + window].1));
            }
            continue;
        }
        let candidates = fixed_base_window_candidates(base, window_count)?;
        let z_column = base.z_column();
        for window in 0..window_count {
            let mut x_values = [<Fp>::ZERO; FIXED_BASE_WINDOW_SIZE as usize];
            for (digit, slot) in x_values.iter_mut().enumerate() {
                let (x, _) = candidates[window * window_size + digit].coordinates()?;
                *slot = x.into_loose();
            }
            let mut row = [<Fp>::ZERO; TUPLE_FIXED_COLUMNS];
            for (digit, value) in x_values.iter().enumerate() {
                for (coefficient, weight) in row[..window_size].iter_mut().zip(&basis[digit]) {
                    *coefficient = coefficient.add(&value.mul(weight));
                }
            }
            row[window_size] = <Fp>::from_u64(*z_column.get(window)?);
            rows.push((region_start.checked_add(window)?, row));
        }
    }
    Some(rows)
}
