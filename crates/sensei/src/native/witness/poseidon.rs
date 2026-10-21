//! Poseidon and nullifier witness rows.
//!
//! Round constants come from the fixed circuit columns. The assignment sequence
//! and arithmetic expressions here follow the frozen full/partial-round layout.

use sensei_shared::fixed_bases::FixedBase;

use crate::Error;
use crate::native::curve::PallasPoint;
use crate::native::field::Fp;
use crate::native::target::N;

use super::fixed_base::write_base_field_fixed_mul;
use super::writer::{RowMap, WitnessWriter};
use super::{
    point_coordinates, power_of_two, write_complete_addition, write_direct, write_region_cells,
};

const POSEIDON_WIDTH: usize = 3;

const POSEIDON_HALF_FULL_ROUNDS: usize = 4;

const POSEIDON_HALF_PARTIAL_ROUNDS: usize = 28;

const POSEIDON_RC_A_FIRST_COLUMN: usize = 5;

const POSEIDON_RC_B_FIRST_COLUMN: usize = 8;

/// Writes the Poseidon hash, fixed-base product, and note-commitment addition
/// used to derive the nullifier. Returns the resulting point's x-coordinate.
pub(super) fn write_nullifier(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    nk: &Fp,
    rho: &Fp,
    psi: &Fp,
    cm: &PallasPoint,
) -> Result<Fp, Error> {
    let poseidon_output = write_poseidon_hash(writer, row_map, nk, rho)?;
    let scalar = poseidon_output.add(psi);
    write_region_cells(
        writer,
        row_map,
        274,
        [(7, 0, poseidon_output), (8, 0, *psi), (6, 0, scalar)],
    )?;

    let product =
        write_base_field_fixed_mul(writer, row_map, 275, 276, FixedBase::NullifierK, &scalar)?;
    let nullifier = write_complete_addition(writer, row_map, 279, cm, &product)?;
    point_coordinates(&nullifier).map(|(x, _)| x)
}

fn write_poseidon_hash(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    nk: &Fp,
    rho: &Fp,
) -> Result<Fp, Error> {
    let capacity = power_of_two(65);
    let initial_state = [<Fp>::ZERO, <Fp>::ZERO, capacity];
    let mut state = [*nk, *rho, capacity];

    write_poseidon_state(writer, row_map, 271, 0, &initial_state)?;
    write_region_cells(
        writer,
        row_map,
        272,
        [
            (6, 0, initial_state[0]),
            (7, 0, initial_state[1]),
            (8, 0, initial_state[2]),
            (6, 1, *nk),
            (7, 1, *rho),
            (6, 2, state[0]),
            (7, 2, state[1]),
            (8, 2, state[2]),
        ],
    )?;

    let target = writer.target;
    let fixed = target.fixed_values();
    let mds = POSEIDON_MDS;
    let mut local_row = 0;
    write_poseidon_state(writer, row_map, 273, local_row, &state)?;

    for _ in 0..POSEIDON_HALF_FULL_ROUNDS {
        let constants =
            poseidon_round_constants(fixed, row_map, 273, local_row, POSEIDON_RC_A_FIRST_COLUMN)?;
        state = poseidon_full_round(&state, &constants, &mds);
        local_row += 1;
        write_poseidon_state(writer, row_map, 273, local_row, &state)?;
    }

    for _ in 0..POSEIDON_HALF_PARTIAL_ROUNDS {
        let constants_a =
            poseidon_round_constants(fixed, row_map, 273, local_row, POSEIDON_RC_A_FIRST_COLUMN)?;
        let constants_b =
            poseidon_round_constants(fixed, row_map, 273, local_row, POSEIDON_RC_B_FIRST_COLUMN)?;
        let partial_sbox = poseidon_pow5(&state[0].add(&constants_a[0]));
        write_direct(writer, row_map, 5, 273, local_row, partial_sbox)?;

        let mut after_a = [
            partial_sbox,
            state[1].add(&constants_a[1]),
            state[2].add(&constants_a[2]),
        ];
        after_a = poseidon_apply_mds(&after_a, &mds);
        state = [
            poseidon_pow5(&after_a[0].add(&constants_b[0])),
            after_a[1].add(&constants_b[1]),
            after_a[2].add(&constants_b[2]),
        ];
        state = poseidon_apply_mds(&state, &mds);
        local_row += 1;
        write_poseidon_state(writer, row_map, 273, local_row, &state)?;
    }

    for _ in 0..POSEIDON_HALF_FULL_ROUNDS {
        let constants =
            poseidon_round_constants(fixed, row_map, 273, local_row, POSEIDON_RC_A_FIRST_COLUMN)?;
        state = poseidon_full_round(&state, &constants, &mds);
        local_row += 1;
        write_poseidon_state(writer, row_map, 273, local_row, &state)?;
    }
    if local_row != 36 {
        return Err(Error::InternalInvariant);
    }

    Ok(state[0])
}

fn write_poseidon_state(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    region: usize,
    local_row: usize,
    state: &[Fp; POSEIDON_WIDTH],
) -> Result<(), Error> {
    write_region_cells(
        writer,
        row_map,
        region,
        [
            (6, local_row, state[0]),
            (7, local_row, state[1]),
            (8, local_row, state[2]),
        ],
    )
}

fn poseidon_round_constants(
    fixed: &[[Fp; N]],
    row_map: &RowMap,
    region: usize,
    local_row: usize,
    first_column: usize,
) -> Result<[Fp; POSEIDON_WIDTH], Error> {
    let row = row_map.absolute_row(region, local_row)?;
    Ok([
        fixed
            .get(first_column)
            .and_then(|column| column.get(row))
            .cloned()
            .ok_or(Error::InternalInvariant)?,
        fixed
            .get(first_column + 1)
            .and_then(|column| column.get(row))
            .cloned()
            .ok_or(Error::InternalInvariant)?,
        fixed
            .get(first_column + 2)
            .and_then(|column| column.get(row))
            .cloned()
            .ok_or(Error::InternalInvariant)?,
    ])
}

/// The Poseidon MDS matrix, single-sourced from the shared expression
/// constants (the gate programs consume the same nine values).
const POSEIDON_MDS: [[Fp; POSEIDON_WIDTH]; POSEIDON_WIDTH] =
    crate::native::generated_expressions::POSEIDON_MDS;

fn poseidon_full_round(
    state: &[Fp; POSEIDON_WIDTH],
    constants: &[Fp; POSEIDON_WIDTH],
    mds: &[[Fp; POSEIDON_WIDTH]; POSEIDON_WIDTH],
) -> [Fp; POSEIDON_WIDTH] {
    let state = core::array::from_fn(|index| {
        let value = state[index].add(&constants[index]);
        poseidon_pow5(&value)
    });
    poseidon_apply_mds(&state, mds)
}

fn poseidon_apply_mds(
    state: &[Fp; POSEIDON_WIDTH],
    mds: &[[Fp; POSEIDON_WIDTH]; POSEIDON_WIDTH],
) -> [Fp; POSEIDON_WIDTH] {
    core::array::from_fn(|row| <Fp>::sum_of_products(&mds[row], state))
}

fn poseidon_pow5(value: &Fp) -> Fp {
    value.square().square().mul(value)
}
