//! Reconstruction of the permutation argument's sigma and identity columns.
//!
//! A sigma-map entry is a flattened destination-cell index in column-major
//! order: `destination_column * N + destination_row`. The generator validates
//! the raw map; this module expands it into field values shared with the prover.
//! Column kinds, copy-constraint classes, and grand-product evaluation belong
//! to the prover.

use alloc::vec::Vec;
use udon::field::Fp;

use crate::{N, PERMUTATION_COLUMN_COUNT};

/// The permutation argument's sigma and identity columns in Lagrange
/// evaluation form: cell `(column, row)` of the identity is
/// `delta^column * omega^row`, and each sigma value is the identity value of
/// the cell its `mapping` entry points at.
///
/// Returns `(sigma_values, identity_values)`, each a contiguous column-major
/// allocation with no separately allocated columns. The prover runs this at load
/// over the embedded sigma map; the sigma-coefficient generator runs the same
/// code on the host over the decoded raw map.
///
/// `omega` is the base domain's primitive `N`th root of unity; `delta`
/// separates the identity columns. The function uses the supplied values
/// directly and does not validate them or check that `mapping` is bijective.
///
/// # Panics
///
/// Panics if any destination index is outside `0..PERMUTATION_COLUMN_COUNT * N`.
pub fn sigma_lagrange_values(
    mapping: &[[u16; N]; PERMUTATION_COLUMN_COUNT],
    omega: &Fp,
    delta: &Fp,
) -> (Vec<[Fp; N]>, Vec<[Fp; N]>) {
    let mut identities = alloc::vec![ [<Fp>::ZERO; N]; PERMUTATION_COLUMN_COUNT];
    let mut delta_power = <Fp>::ONE;
    for column in &mut identities {
        let mut identity = delta_power;
        for value in column {
            *value = identity;
            identity = identity.mul(omega);
        }
        delta_power = delta_power.mul(delta);
    }
    let mut values = alloc::vec![ [<Fp>::ZERO; N]; PERMUTATION_COLUMN_COUNT];
    let flat_identities = identities.as_flattened();
    for (column, mapping) in values.iter_mut().zip(mapping) {
        for (value, index) in column.iter_mut().zip(mapping) {
            *value = flat_identities[usize::from(*index)];
        }
    }
    (values, identities)
}
