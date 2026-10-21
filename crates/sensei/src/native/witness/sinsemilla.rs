//! Sinsemilla hashes for note commitments, incoming viewing keys, and Merkle paths.
//!
//! Each hash consumes the shared message-piece schedule and emits lookup words
//! alongside the curve-accumulator rows. Message decomposition is implemented in
//! the sibling decomposition module.

use sensei_shared::MERKLE_DEPTH;
use sensei_shared::fixed_bases::FixedBase;
use sensei_shared::generators::{
    COMMIT_IVK_M_GENERATOR, MERKLE_CRH_M_GENERATOR, NOTE_COMMIT_M_GENERATOR,
};

use crate::Error;
use crate::native::curve::{PallasAffine, PallasPoint};
use crate::native::field::{Fp, Fq};
use crate::native::regions::sinsemilla_hashes;
use crate::native::target::ADVICE_COLUMNS;

use super::decomposition::{NotePieces, WordStream};
use super::fixed_base::write_full_fixed_mul;
use super::writer::{AdviceValue, RowMap, WitnessWriter};
use super::{
    COMMIT_IVK_WORDS, MERKLE_FIRST_REGION, MERKLE_REGIONS_PER_LAYER, MERKLE_WORDS,
    NOTE_COMMIT_WORDS, SINSEMILLA_WORD_BITS, bitrange, combine_subpieces, point_coordinates,
    running_sum_at, write_complete_addition, write_direct, write_region_cells,
    write_short_range_check,
};

/// Writes each authentication-path layer from leaf to root. Position bits
/// select the left/right ordering, and each hash's x-coordinate feeds the next.
pub(super) fn write_merkle_path(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    leaf: &Fp,
    path: &[Fp],
    position: u32,
) -> Result<Fp, Error> {
    if path.len() != MERKLE_DEPTH {
        return Err(Error::InternalInvariant);
    }

    let mut node = *leaf;
    for (layer, sibling) in path.iter().enumerate() {
        let region = MERKLE_FIRST_REGION + layer * MERKLE_REGIONS_PER_LAYER;
        let column_base = if layer < MERKLE_DEPTH / 2 { 0 } else { 5 };
        let witness_column = if column_base == 0 { 6 } else { 7 };
        let swap = ((position >> layer) & 1) != 0;
        let (left, right) = if swap {
            (*sibling, node)
        } else {
            (node, *sibling)
        };

        write_region_cells(
            writer,
            row_map,
            region,
            [
                (column_base, 0, node),
                (column_base + 1, 0, *sibling),
                (column_base + 2, 0, left),
                (column_base + 3, 0, right),
                (column_base + 4, 0, <Fp>::from_u64(swap.into())),
            ],
        )?;

        let a = combine_subpieces(&[
            (<Fp>::from_u64(layer as u64), 10),
            (bitrange(&left, 0, 240)?, 240),
        ])?;
        let b_1 = bitrange(&left, 250, 255)?;
        let b_2 = bitrange(&right, 0, 5)?;
        let b = combine_subpieces(&[(bitrange(&left, 240, 250)?, 10), (b_1, 5), (b_2, 5)])?;
        let c = bitrange(&right, 5, 255)?;

        write_direct(writer, row_map, witness_column, region + 1, 0, a)?;
        write_short_range_check(writer, row_map, region + 2, b_1, 5)?;
        write_short_range_check(writer, row_map, region + 3, b_2, 5)?;
        write_direct(writer, row_map, witness_column, region + 4, 0, b)?;
        write_direct(writer, row_map, witness_column, region + 5, 0, c)?;

        let pieces = [(a, 25), (b, 2), (c, 25)];
        let schedule = sinsemilla_hashes::merkle_layer(layer);
        if schedule.region != region + sinsemilla_hashes::MERKLE_HASH_REGION_OFFSET
            || schedule.column_base != column_base
        {
            return Err(Error::InternalInvariant);
        }
        let hash = write_sinsemilla_hash(
            writer,
            row_map,
            &schedule,
            MERKLE_CRH_M_GENERATOR,
            &pieces,
            MERKLE_WORDS,
        )?;
        let z1_a = running_sum_at(&a, 1)?;
        let z1_b = running_sum_at(&b, 1)?;
        write_region_cells(
            writer,
            row_map,
            region + 7,
            [
                (column_base, 0, a),
                (column_base + 1, 0, b),
                (column_base + 2, 0, c),
                (column_base + 3, 0, left),
                (column_base + 4, 0, right),
                (column_base, 1, z1_a),
                (column_base + 1, 1, z1_b),
                (column_base + 2, 1, b_1),
                (column_base + 3, 1, b_2),
                (column_base + 4, 1, <Fp>::from_u64(layer as u64)),
            ],
        )?;
        node = point_coordinates(&hash)?.0;
    }

    Ok(node)
}

/// Writes the Sinsemilla message hash for the incoming viewing-key commitment.
/// The caller writes its blinding product and final point addition separately.
pub(super) fn write_commit_ivk_sinsemilla(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    ak: &PallasPoint,
    nk: &Fp,
) -> Result<PallasPoint, Error> {
    const REGION: usize = 292;

    let pieces = commit_ivk_pieces(ak, nk)?;
    let hash_pieces = [(pieces.a, 25), (pieces.b, 1), (pieces.c, 24), (pieces.d, 1)];
    let schedule = sinsemilla_hashes::COMMIT_IVK;
    if schedule.region != REGION || schedule.column_base != 0 {
        return Err(Error::InternalInvariant);
    }
    write_sinsemilla_hash(
        writer,
        row_map,
        &schedule,
        COMMIT_IVK_M_GENERATOR,
        &hash_pieces,
        COMMIT_IVK_WORDS,
    )
}

/// Writes one Sinsemilla hash on its scheduled region and columns. The
/// schedule ([`sinsemilla_hashes`]) is the single description of where each
/// word's running sum lands, shared with the advice commitment's word
/// transform; the caller's pieces must match it width for width.
pub(super) fn write_sinsemilla_hash(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    schedule: &sinsemilla_hashes::HashSchedule,
    q: PallasAffine,
    pieces: &[(Fp, usize)],
    expected_words: usize,
) -> Result<PallasPoint, Error> {
    let region = schedule.region;
    let column_base = schedule.column_base;
    if column_base + 4 >= ADVICE_COLUMNS
        || q != schedule.q
        || pieces.is_empty()
        || expected_words == 0
        || expected_words != schedule.words()
        || pieces.len() != schedule.pieces.len()
        || pieces
            .iter()
            .zip(schedule.pieces)
            .any(|((_, words), scheduled)| words != scheduled)
    {
        return Err(Error::InternalInvariant);
    }
    let mut accumulator = q.to_projective();
    let start = row_map.absolute_row(region, 0)?;
    writer.write_advice(
        column_base,
        start,
        AdviceValue::Direct(q.coordinates().0.into_loose()),
    )?;

    // These typed points also supply the fixed lookup columns; use them
    // directly so each word needs no curve-membership check.
    let generators = writer.target.sinsemilla_generators();
    let mut offset = 0;
    // The inverse of the final accumulator `z`, computed once for the hash's
    // last word: the affine result needs it anyway, so the last word's three
    // cells and the closing y-cell are written directly from it instead of
    // deferring two more denominator entries to the batched inversion.
    let mut final_normalization = None;
    for (piece, num_words) in pieces {
        if *num_words == 0 || offset + num_words > expected_words {
            return Err(Error::InternalInvariant);
        }
        let stream = WordStream::new(piece, SINSEMILLA_WORD_BITS, *num_words)?;
        for (piece_row, word) in stream.enumerate() {
            let (word, sum) = word?;
            let row = start + offset + piece_row;
            let point = generators.get(word).ok_or(Error::InternalInvariant)?;
            let step = accumulator
                .incomplete_double_and_add(point)
                .ok_or(Error::UnsatisfiedWitness)?;
            accumulator = step.point;
            let (x, _, z) = accumulator.coordinates();
            let [lambda_1_numerator, lambda_2_numerator] = step.slope_numerators;

            writer.write_advice(
                column_base + 1,
                row,
                AdviceValue::Direct(point.coordinates().0.into_loose()),
            )?;
            writer.write_advice(schedule.running_sum_column(), row, AdviceValue::Direct(sum))?;
            if offset + piece_row + 1 == expected_words {
                // The hash's final word: `z` is non-zero (checked above), so
                // its inverse exists; λ₁ and λ₂ over `z` and the
                // x-coordinate over `z²` are written as values.
                let z_inverse = z.invert().ok_or(Error::UnsatisfiedWitness)?;
                let z_inverse_squared = z_inverse.square();
                let affine_x = x.mul(&z_inverse_squared).reduce();
                writer.write_advice(
                    column_base + 3,
                    row,
                    AdviceValue::Direct(lambda_1_numerator.mul(&z_inverse)),
                )?;
                writer.write_advice(
                    column_base + 4,
                    row,
                    AdviceValue::Direct(lambda_2_numerator.mul(&z_inverse)),
                )?;
                writer.write_advice(
                    column_base,
                    row + 1,
                    AdviceValue::Direct(affine_x.into_loose()),
                )?;
                final_normalization = Some((z_inverse, z_inverse_squared, affine_x));
            } else {
                // λ₁ and λ₂ over `z`, the x-coordinate over `z²`: one shared
                // denominator entry for the word.
                writer.write_incomplete_double_and_add(
                    [
                        (column_base + 3, row),
                        (column_base + 4, row),
                        (column_base, row + 1),
                    ],
                    [lambda_1_numerator, lambda_2_numerator, *x],
                    *z,
                )?;
            }
        }
        offset += num_words;
    }
    if offset != expected_words {
        return Err(Error::InternalInvariant);
    }
    let (z_inverse, z_inverse_squared, affine_x) =
        final_normalization.ok_or(Error::InternalInvariant)?;
    let (_, y, _) = accumulator.coordinates();
    let affine_y = y.mul(&z_inverse_squared).mul(&z_inverse).reduce();

    // The closing cell `y / z³`, from the same inverse.
    writer.write_advice(
        column_base + 3,
        start + offset,
        AdviceValue::Direct(affine_y.into_loose()),
    )?;
    writer.write_advice(
        column_base + 4,
        start + offset,
        AdviceValue::Direct(<Fp>::ZERO),
    )?;
    writer.write_advice(
        column_base + 1,
        start + offset,
        AdviceValue::Direct(<Fp>::ZERO),
    )?;
    PallasAffine::from_xy(affine_x, affine_y)
        .map(|point| point.to_point())
        .ok_or(Error::UnsatisfiedWitness)
}

/// Writes a note's blinding product, message hash, and final point addition.
/// Region arguments select the old-note or new-note schedule.
#[allow(clippy::too_many_arguments)] // each note schedule supplies its own region coordinates
pub(super) fn write_note_commitment(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    blind_region: usize,
    blind_final_region: usize,
    hash_region: usize,
    addition_region: usize,
    hash_column_base: usize,
    pieces: &NotePieces,
    rcm: &Fq,
) -> Result<PallasPoint, Error> {
    const PIECE_WORDS: [usize; 8] = [25, 1, 25, 6, 1, 25, 25, 1];

    let blind = write_full_fixed_mul(
        writer,
        row_map,
        blind_region,
        blind_final_region,
        FixedBase::NoteCommitR,
        rcm,
    )?;
    let piece_values = [
        pieces.a, pieces.b, pieces.c, pieces.d, pieces.e, pieces.f, pieces.g, pieces.h,
    ];
    let hash_pieces: [(Fp, usize); 8] =
        core::array::from_fn(|index| (piece_values[index], PIECE_WORDS[index]));
    let schedule = [sinsemilla_hashes::OLD_NOTE, sinsemilla_hashes::NEW_NOTE]
        .into_iter()
        .find(|schedule| schedule.region == hash_region && schedule.column_base == hash_column_base)
        .ok_or(Error::InternalInvariant)?;
    let message = write_sinsemilla_hash(
        writer,
        row_map,
        &schedule,
        NOTE_COMMIT_M_GENERATOR,
        &hash_pieces,
        NOTE_COMMIT_WORDS,
    )?;
    write_complete_addition(writer, row_map, addition_region, &message, &blind)
}

/// The Sinsemilla message pieces of `commit_ivk` with their sub-pieces, shared
/// by the hash regions and the canonicity decomposition.
pub(super) struct CommitIvkPieces {
    pub(super) a: Fp,
    pub(super) b: Fp,
    pub(super) c: Fp,
    pub(super) d: Fp,
    pub(super) b_0: Fp,
    pub(super) b_1: Fp,
    pub(super) b_2: Fp,
    pub(super) d_0: Fp,
    pub(super) d_1: Fp,
}

/// Splits `ak`'s x-coordinate and `nk` into the shared hash/decomposition layout.
pub(super) fn commit_ivk_pieces(ak: &PallasPoint, nk: &Fp) -> Result<CommitIvkPieces, Error> {
    let (ak, _) = point_coordinates(ak)?;
    let a = bitrange(&ak, 0, 250)?;
    let b_0 = bitrange(&ak, 250, 254)?;
    let b_1 = bitrange(&ak, 254, 255)?;
    let b_2 = bitrange(nk, 0, 5)?;
    let b = combine_subpieces(&[(b_0, 4), (b_1, 1), (b_2, 5)])?;
    let c = bitrange(nk, 5, 245)?;
    let d_0 = bitrange(nk, 245, 254)?;
    let d_1 = bitrange(nk, 254, 255)?;
    let d = combine_subpieces(&[(d_0, 9), (d_1, 1)])?;
    Ok(CommitIvkPieces {
        a,
        b,
        c,
        d,
        b_0,
        b_1,
        b_2,
        d_0,
        d_1,
    })
}
