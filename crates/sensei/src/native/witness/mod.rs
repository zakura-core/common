//! Fixed-layout witness construction for the pinned Action circuit: direct
//! writes into dense advice columns with separate structural support masks.
//! Rational numerators are written immediately; their deferred denominators
//! are batch-inverted to finalize the cells in place.
//!
//! The entry points live here; [`synthesis`] owns the Action chain schedule
//! and its ordered merge. [`writer`] owns assignment support, deferred
//! rationals, and finalization. [`WitnessWriter`]
//! defines the storage and support contract: dense values alone cannot
//! distinguish an explicitly assigned zero from an unassigned cell. The gadget
//! modules follow the circuit's arithmetic families: [`fixed_base`],
//! [`variable_base`], [`poseidon`], and [`sinsemilla`]. [`decomposition`] supplies
//! their message pieces, running sums, and canonicity witnesses. Gadgets write
//! through the same dense writer; their row order is the fixed circuit schedule.
//!
//! The `require_statement_*`, `require_merkle_root`, and
//! `require_top_level_relations` checks compare public inputs or flags with the
//! witness and report [`Error::InvalidStatement`]. Failed private relations
//! (for example the derived old address or note commitment) and gadget range
//! checks report [`Error::UnsatisfiedWitness`]; [`super::preflight`] checks the
//! completed columns. Shape and assignment-contract failures remain
//! [`Error::InternalInvariant`] as described by [`super::invariant`].

use alloc::{sync::Arc, vec::Vec};
mod decomposition;
mod fixed_base;
mod poseidon;
mod sinsemilla;
mod synthesis;
mod variable_base;
mod writer;

use crate::Error;
use crate::types::{Action, NativeStatement, ProvingRequest};

use super::curve::PallasPoint;
use super::field::{CanonicalUint, Fp, PallasBase, PallasScalar, PrimeModulus};
use super::preflight::{WitnessFeeds, check_witness_constraints};
use super::prover::AdviceMatrix;
use super::regions::sinsemilla_hashes;
use synthesis::{CHAINS, write_native_witness_into};

pub(crate) use fixed_base::fixed_base_window_table;
pub(crate) use writer::{
    ASSIGNED_WORDS_PER_COLUMN, AdviceValue, NativeWitness, RowMap, WitnessWriter,
};

/// `t_P = p − 2^254`, the Orchard canonicity offset for the Pallas base field:
/// the low 128 bits of the modulus, whose upper limbs are exactly `[0, 2^62]`.
/// Derived from the arithmetic crate's modulus rather than respelled. Every
/// production use turns it into an *at-rest field value* (`Fp` via
/// `from_uniform_bytes`) inside a `piece + 2^k − t_P` canonicity witness.
const T_P: u128 = modulus_low_bits(<PallasBase as PrimeModulus>::MODULUS);

/// `t_Q = q − 2^254`, likewise for the scalar field. Its one production use is
/// as a *canonical integer addend*: `scalar_to_k` forms `k = scalar + t_Q`
/// as a 255-bit integer, never reduced.
const T_Q: u128 = modulus_low_bits(<PallasScalar as PrimeModulus>::MODULUS);

/// A Pasta modulus minus `2^254`: both moduli are `2^254 + t` for a 128-bit
/// `t`, so the difference is exactly the two low limbs.
const fn modulus_low_bits(modulus: [u64; 4]) -> u128 {
    assert!(
        modulus[2] == 0 && modulus[3] == 1u64 << 62,
        "a Pasta modulus is 2^254 plus a 128-bit value"
    );
    ((modulus[1] as u128) << 64) | (modulus[0] as u128)
}

// The protocol's published decimal values, pinned independently of the
// derivation above.
const _: () = {
    assert!(T_P == 45_560_315_531_419_706_090_280_762_371_685_220_353);
    assert!(T_Q == 45_560_315_531_506_369_815_346_746_415_080_538_113);
};

#[cfg(test)]
const SINSEMILLA_TABLE_INDEX_COLUMN: usize = 0;

#[cfg(test)]
const SINSEMILLA_TABLE_X_COLUMN: usize = 1;

#[cfg(test)]
const SINSEMILLA_TABLE_Y_COLUMN: usize = 2;

const SINSEMILLA_WORD_BITS: usize = sinsemilla_hashes::WORD_BITS;

const COMMIT_IVK_WORDS: usize = sinsemilla_hashes::COMMIT_IVK.words();

const NOTE_COMMIT_WORDS: usize = sinsemilla_hashes::OLD_NOTE.words();

const MERKLE_WORDS: usize = sinsemilla_hashes::MERKLE_PIECES[0]
    + sinsemilla_hashes::MERKLE_PIECES[1]
    + sinsemilla_hashes::MERKLE_PIECES[2];

const MERKLE_FIRST_REGION: usize = sinsemilla_hashes::MERKLE_FIRST_REGION;

const MERKLE_REGIONS_PER_LAYER: usize = sinsemilla_hashes::MERKLE_REGIONS_PER_LAYER;

/// Builds complete finalized advice matrices from the circuit-native request,
/// returning them (shared, as the preflight tasks read them) with the witness
/// feeds preflight retained.
pub(crate) fn build_native_witness_matrices(
    target: &super::target::FixedTarget,
    execution: super::worker::Execution<'_>,
    request: &ProvingRequest,
    statements: &[NativeStatement],
    lookup: &super::prover::LookupWorkspace,
) -> Result<(Vec<Arc<AdviceMatrix>>, WitnessFeeds), Error> {
    if statements.len() != request.action_count() {
        return Err(Error::InternalInvariant);
    }
    let actions = request.action_count();
    let active_actions = actions.min(execution.budget.get());
    // Completed Actions retain their main matrices; active Actions can also
    // retain every chain matrix until merge. Action admission is bounded by the
    // task budget, so this covers the maximum live set for this construction.
    execution.provision(
        super::target::N,
        (actions + CHAINS.len() * active_actions) * super::target::ADVICE_COLUMNS,
    );
    let build_matrices =
        || build_action_witness_matrices(target, execution, request.actions(), statements);
    #[cfg(test)]
    let matrices = super::stage_timing::measure_witness(
        super::stage_timing::WitnessStage::Construction,
        build_matrices,
    )?;
    #[cfg(not(test))]
    let matrices = build_matrices()?;
    let feeds =
        check_witness_constraints(execution, target, request, statements, &matrices, lookup)?;
    Ok((matrices, feeds))
}

fn build_action_witness_matrices(
    target: &super::target::FixedTarget,
    execution: super::worker::Execution<'_>,
    actions: &[Action],
    statements: &[NativeStatement],
) -> Result<Vec<Arc<AdviceMatrix>>, Error> {
    if statements.len() != actions.len() {
        return Err(Error::InternalInvariant);
    }
    if actions.len() <= 1 {
        return actions
            .iter()
            .zip(statements)
            .map(|(action, statement)| {
                build_native_witness_of(target, execution, action, statement)
                    .and_then(NativeWitness::into_matrix)
                    .map(Arc::new)
            })
            .collect();
    }

    // Each owned task borrows its Action through the shared handle and
    // carries its (`Copy`) statement record; nothing is cloned but the
    // reference count.
    let jobs = statements.iter().copied().enumerate();
    execution
        .map(jobs, move |(index, statement), execution| {
            build_native_witness_of(target, execution, &actions[index], &statement)
                .and_then(NativeWitness::into_matrix)
                .map(Arc::new)
        })
        .into_iter()
        .collect()
}

/// Runs the complete fixed-purpose witness schedule for one Action against
/// its already-decoded statement record, writing dense advice columns and
/// tracking structural assignment support as defined by [`WitnessWriter`].
/// Finalization batch-inverts deferred rational denominators and divides their
/// cells in place before returning the witness and its support mask.
pub(crate) fn build_native_witness_of(
    target: &super::target::FixedTarget,
    execution: super::worker::Execution<'_>,
    action: &Action,
    statement: &NativeStatement,
) -> Result<NativeWitness, Error> {
    write_native_witness(target, execution, action, statement)?.finish()
}

/// [`build_native_witness_of`] decoding the Action's own statement: the
/// tests' single-Action convenience.
#[cfg(test)]
pub(crate) fn build_native_witness(action: &Action) -> Result<NativeWitness, Error> {
    build_native_witness_of(
        crate::test_codec::target(),
        crate::test_codec::execution(),
        action,
        &action.statement.native(),
    )
}

/// Runs the fixed writer schedule for one Action, leaving cells unfinalized.
fn write_native_witness<'a>(
    target: &'a super::target::FixedTarget,
    execution: super::worker::Execution<'a>,
    action: &Action,
    statement: &NativeStatement,
) -> Result<WitnessWriter<'a>, Error> {
    write_native_witness_into(action, statement, WitnessWriter::new(target, execution))
}

fn require_merkle_root(v_old: u64, root: &Fp, anchor: &Fp) -> Result<(), Error> {
    if v_old == 0 {
        Ok(())
    } else {
        require_statement_value(root, anchor)
    }
}

fn require_top_level_relations(action: &Action) -> Result<(), Error> {
    let statement = &action.statement;
    let witness = &action.witness;
    let same_address = witness.g_d_old == witness.g_d_new && witness.pk_d_old == witness.pk_d_new;
    if top_level_relations_hold(
        witness.v_old,
        witness.v_new,
        statement.enable_spend,
        statement.enable_output,
        statement.disable_cross_address,
        same_address,
    ) {
        Ok(())
    } else {
        Err(Error::InvalidStatement)
    }
}

fn top_level_relations_hold(
    v_old: u64,
    v_new: u64,
    enable_spend: bool,
    enable_output: bool,
    disable_cross_address: bool,
    same_address: bool,
) -> bool {
    (v_old == 0 || enable_spend)
        && (v_new == 0 || enable_output)
        && (!disable_cross_address || same_address)
}

fn point_coordinates(point: &PallasPoint) -> Result<(Fp, Fp), Error> {
    point
        .coordinates()
        .map(|(x, y)| (x.into_loose(), y.into_loose()))
        .ok_or(Error::InternalInvariant)
}

fn write_point(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    region: usize,
    point: &PallasPoint,
) -> Result<(), Error> {
    match point.coordinates() {
        Some((x, y)) => {
            write_direct(writer, row_map, 0, region, 0, x.into_loose())?;
            write_direct(writer, row_map, 1, region, 0, y.into_loose())
        }
        None => {
            writer.write_region_advice(row_map, 0, region, 0, AdviceValue::AssignedZero)?;
            writer.write_region_advice(row_map, 1, region, 0, AdviceValue::AssignedZero)
        }
    }
}

fn write_direct(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    column: usize,
    region: usize,
    local_row: usize,
    value: Fp,
) -> Result<(), Error> {
    writer.write_region_advice(
        row_map,
        column,
        region,
        local_row,
        AdviceValue::Direct(value),
    )
}

fn write_complete_addition(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    region: usize,
    p: &PallasPoint,
    q: &PallasPoint,
) -> Result<PallasPoint, Error> {
    let (x_p, y_p) = point_coordinates_or_zero(p);
    let (x_q, y_q) = point_coordinates_or_zero(q);
    let result = p.add(q).to_point();
    let (x_r, y_r) = point_coordinates_or_zero(&result);

    for (column, local_row, value) in [
        (0, 0, x_p),
        (1, 0, y_p),
        (2, 0, x_q),
        (3, 0, y_q),
        (2, 1, x_r),
        (3, 1, y_r),
    ] {
        write_direct(writer, row_map, column, region, local_row, value)?;
    }
    for (column, value) in complete_addition_rationals(x_p, y_p, x_q, y_q) {
        writer.write_region_advice(row_map, column, region, 0, value)?;
    }
    Ok(result)
}

fn complete_addition_rationals(x_p: Fp, y_p: Fp, x_q: Fp, y_q: Fp) -> [(usize, AdviceValue); 5] {
    let x_difference = x_q.sub(&x_p);
    let lambda = if (x_q).reduce() != (x_p).reduce() {
        rational_or_zero(y_q.sub(&y_p), x_difference)
    } else if !y_p.is_zero() {
        rational_or_zero(x_p.square().triple(), y_p.double())
    } else {
        AdviceValue::Direct(<Fp>::ZERO)
    };
    let delta = if (x_q).reduce() == (x_p).reduce() {
        rational_or_zero(<Fp>::ONE, y_q.add(&y_p))
    } else {
        AdviceValue::Direct(<Fp>::ZERO)
    };
    [
        (4, lambda),
        (5, rational_or_zero(<Fp>::ONE, x_difference)),
        (6, rational_or_zero(<Fp>::ONE, x_p)),
        (7, rational_or_zero(<Fp>::ONE, x_q)),
        (8, delta),
    ]
}

fn rational_or_zero(numerator: Fp, denominator: Fp) -> AdviceValue {
    if denominator.is_zero() {
        AdviceValue::Direct(<Fp>::ZERO)
    } else {
        AdviceValue::Rational {
            numerator,
            denominator,
        }
    }
}

fn point_coordinates_or_zero(point: &PallasPoint) -> (Fp, Fp) {
    point.coordinates().map_or_else(
        || (<Fp>::ZERO, <Fp>::ZERO),
        |(x, y)| (x.into_loose(), y.into_loose()),
    )
}

fn require_statement_point(point: &PallasPoint, x: &Fp, y: &Fp) -> Result<(), Error> {
    let coordinates = point_coordinates_or_zero(point);
    ((coordinates.0).reduce() == (x).reduce() && (coordinates.1).reduce() == (y).reduce())
        .then_some(())
        .ok_or(Error::InvalidStatement)
}

fn require_statement_value(value: &Fp, statement: &Fp) -> Result<(), Error> {
    ((value).reduce() == (statement).reduce())
        .then_some(())
        .ok_or(Error::InvalidStatement)
}

fn signed_difference(old: u64, new: u64) -> (Fp, Fp) {
    if old >= new {
        (<Fp>::from_u64(old - new), <Fp>::ONE)
    } else {
        (<Fp>::from_u64(new - old), <Fp>::ONE.neg())
    }
}

fn bitrange(value: &Fp, start: usize, end: usize) -> Result<Fp, Error> {
    if start >= end || end > 255 {
        return Err(Error::InternalInvariant);
    }
    let integer = value
        .to_canonical_uint()
        .bit_slice(start, end - start)
        .ok_or(Error::InternalInvariant)?;
    <Fp>::from_canonical_uint(integer).ok_or(Error::InternalInvariant)
}

fn combine_subpieces(subpieces: &[(Fp, usize)]) -> Result<Fp, Error> {
    let mut combined = <Fp>::ZERO;
    let mut offset = 0usize;
    for (value, width) in subpieces {
        if *width == 0 || offset >= 64 || offset + width > 255 {
            return Err(Error::InternalInvariant);
        }
        let shift = power_of_two(offset);
        combined = value.mul_add(&shift, &combined);
        offset += width;
    }
    Ok(combined)
}

fn power_of_two(exponent: usize) -> Fp {
    CanonicalUint::power_of_two(exponent)
        .and_then(<Fp>::from_canonical_uint)
        .expect("witness powers of two are below the Pallas base modulus")
}

fn write_short_range_check(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    region: usize,
    value: Fp,
    num_bits: usize,
) -> Result<(), Error> {
    const LOOKUP_BITS: usize = 10;
    if num_bits == 0 || num_bits > LOOKUP_BITS {
        return Err(Error::InternalInvariant);
    }
    if !value.to_canonical_uint().fits_in_bits(num_bits) {
        return Err(Error::UnsatisfiedWitness);
    }
    let shifted = value.mul(&<Fp>::from_u64(1 << (LOOKUP_BITS - num_bits)));
    let inverse = <Fp>::power_of_two_inverse(num_bits as u32);
    write_direct(writer, row_map, 9, region, 0, value)?;
    write_direct(writer, row_map, 9, region, 1, shifted)?;
    write_direct(writer, row_map, 9, region, 2, inverse)
}

fn running_sum_at(value: &Fp, index: usize) -> Result<Fp, Error> {
    // The running sum's final term is just the source shifted past `index` words;
    // read it directly instead of materializing the whole vector to pop the tail.
    // The guard mirrors `running_sum`'s validation for `word_bits == 10`.
    if index == 0 || index.checked_mul(10).is_none_or(|bits| bits > 255) {
        return Err(Error::InternalInvariant);
    }
    <Fp>::from_canonical_uint(value.to_canonical_uint().shr(index * 10))
        .ok_or(Error::InternalInvariant)
}

fn write_region_cells<const LEN: usize>(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    region: usize,
    cells: [(usize, usize, Fp); LEN],
) -> Result<(), Error> {
    // The region start resolves once; the writer's own bounds check covers
    // each `start + local_row` exactly as `absolute_row` did per write.
    let start = row_map.absolute_row(region, 0)?;
    for (column, local_row, value) in cells {
        writer.write_advice(column, start + local_row, AdviceValue::Direct(value))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests;
