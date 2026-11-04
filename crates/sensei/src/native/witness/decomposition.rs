//! Message pieces and circuit-specific canonicity witness rows.
//!
//! Word extraction uses canonical integers, while the assigned sums are field
//! elements. [`bitstream`] owns streaming words and generic running sums; the
//! fixed schedule here determines every piece length and destination. Do not
//! infer support from the particular witness values.

use super::sinsemilla::{CommitIvkPieces, commit_ivk_pieces};
use super::writer::{RowMap, WitnessWriter};
use super::{
    T_P, bitrange, combine_subpieces, point_coordinates, power_of_two, running_sum_at,
    write_direct, write_region_cells, write_short_range_check,
};
use crate::Error;
use crate::native::curve::PallasPoint;
use crate::native::field::Fp;

mod bitstream;

pub(super) use bitstream::{WordStream, fill_words_and_running_sums, write_running_sum};
#[cfg(test)]
pub(super) use bitstream::{decompose_words, running_sum, words_with_running_sums};

/// Writes one of the scheduled range-check / canonicity running-sum streams
/// ([`crate::native::regions::range_running_sums`]), refusing any call the schedule
/// does not list: the advice commitment transposes exactly these streams.
#[allow(clippy::too_many_arguments)] // fixed-layout coordinates are passed individually
pub(super) fn write_scheduled_running_sum(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    column: usize,
    region: usize,
    value: &Fp,
    word_bits: usize,
    num_words: usize,
    strict: bool,
) -> Result<(), Error> {
    if !crate::native::regions::range_running_sums::is_stream(
        column, region, word_bits, num_words, strict,
    ) {
        return Err(Error::InternalInvariant);
    }
    write_running_sum(
        writer, row_map, column, region, value, word_bits, num_words, strict,
    )
}

/// Writes the range and canonicity witnesses for the pieces also consumed by
/// the incoming viewing-key commitment's Sinsemilla hash.
pub(super) fn write_commit_ivk_decomposition(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    ak: &PallasPoint,
    nk: &Fp,
) -> Result<(), Error> {
    let CommitIvkPieces {
        a,
        b,
        c,
        d,
        b_0,
        b_1,
        b_2,
        d_0,
        d_1,
    } = commit_ivk_pieces(ak, nk)?;
    let (ak, _) = point_coordinates(ak)?;

    for (region, piece) in [(283, a), (286, b), (287, c), (289, d)] {
        write_direct(writer, row_map, 6, region, 0, piece)?;
    }
    for (region, short, width) in [(284, b_0, 4), (285, b_2, 5), (288, d_0, 9)] {
        write_short_range_check(writer, row_map, region, short, width)?;
    }

    // `t_P` as a field value for the `piece + 2^k − t_P` canonicity witnesses.
    let t_p = <Fp>::from_bytes_reduced(&T_P.to_le_bytes());
    let a_prime = a.add(&power_of_two(130)).sub(&t_p);
    let b2_c_prime = b_2
        .add(&c.mul(&<Fp>::from_u64(1 << 5)))
        .add(&power_of_two(140))
        .sub(&t_p);
    let z13_a = running_sum_at(&a, 13)?;
    let z13_c = running_sum_at(&c, 13)?;

    // Column 9, regions 294/295: 13/14 ten-bit words, allowing a nonzero remainder.
    write_scheduled_running_sum(writer, row_map, 9, 294, &a_prime, 10, 13, false)?;
    write_scheduled_running_sum(writer, row_map, 9, 295, &b2_c_prime, 10, 14, false)?;

    for (column, local_row, value) in [
        (0, 0, ak),
        (1, 0, a),
        (2, 0, b),
        (3, 0, b_0),
        (4, 0, b_1),
        (5, 0, b_2),
        (6, 0, z13_a),
        (7, 0, a_prime),
        (8, 0, running_sum_at(&a_prime, 13)?),
        (0, 1, *nk),
        (1, 1, c),
        (2, 1, d),
        (3, 1, d_0),
        (4, 1, d_1),
        (6, 1, z13_c),
        (7, 1, b2_c_prime),
        (8, 1, running_sum_at(&b2_c_prime, 14)?),
    ] {
        write_direct(writer, row_map, column, 296, local_row, value)?;
    }

    Ok(())
}

/// Decomposes a note message and writes its range and canonicity witnesses.
/// The returned pieces feed the old-note or new-note commitment hash.
#[allow(clippy::too_many_arguments)] // fixed-layout coordinates are passed individually
pub(super) fn write_note_decomposition(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    first_region: usize,
    piece_column: usize,
    g_d: &PallasPoint,
    pk_d: &PallasPoint,
    value: u64,
    rho: &Fp,
    psi: &Fp,
) -> Result<NotePieces, Error> {
    let (gd_x, gd_y) = point_coordinates(g_d)?;
    let (pk_x, pk_y) = point_coordinates(pk_d)?;
    let value = <Fp>::from_u64(value);

    let a = bitrange(&gd_x, 0, 250)?;
    let b_0 = bitrange(&gd_x, 250, 254)?;
    let b_1 = bitrange(&gd_x, 254, 255)?;
    let b_2 = bitrange(&gd_y, 0, 1)?;
    let b_3 = bitrange(&pk_x, 0, 4)?;
    let b = combine_subpieces(&[(b_0, 4), (b_1, 1), (b_2, 1), (b_3, 4)])?;
    let c = bitrange(&pk_x, 4, 254)?;

    let d_0 = bitrange(&pk_x, 254, 255)?;
    let d_1 = bitrange(&pk_y, 0, 1)?;
    let d_2 = bitrange(&value, 0, 8)?;
    let d_3 = bitrange(&value, 8, 58)?;
    let d = combine_subpieces(&[(d_0, 1), (d_1, 1), (d_2, 8), (d_3, 50)])?;

    let e_0 = bitrange(&value, 58, 64)?;
    let e_1 = bitrange(rho, 0, 4)?;
    let e = combine_subpieces(&[(e_0, 6), (e_1, 4)])?;
    let f = bitrange(rho, 4, 254)?;

    let g_0 = bitrange(rho, 254, 255)?;
    let g_1 = bitrange(psi, 0, 9)?;
    let g_2 = bitrange(psi, 9, 249)?;
    let g = combine_subpieces(&[(g_0, 1), (g_1, 9), (g_2, 240)])?;

    let h_0 = bitrange(psi, 249, 254)?;
    let h_1 = bitrange(psi, 254, 255)?;
    let h = combine_subpieces(&[(h_0, 5), (h_1, 1), (<Fp>::ZERO, 4)])?;

    let pieces = NotePieces {
        gd_x,
        gd_y,
        pk_x,
        pk_y,
        value,
        rho: *rho,
        psi: *psi,
        a,
        b,
        c,
        d,
        e,
        f,
        g,
        h,
        b_0,
        b_1,
        b_3,
        d_0,
        d_2,
        e_0,
        e_1,
        g_0,
        g_1,
        g_2,
        h_0,
        h_1,
    };

    for (offset, piece) in [
        (0, pieces.a),
        (3, pieces.b),
        (4, pieces.c),
        (6, pieces.d),
        (9, pieces.e),
        (10, pieces.f),
        (12, pieces.g),
        (14, pieces.h),
    ] {
        write_direct(
            writer,
            row_map,
            piece_column,
            first_region + offset,
            0,
            piece,
        )?;
    }
    for (offset, short, width) in [
        (1, pieces.b_0, 4),
        (2, pieces.b_3, 4),
        (5, pieces.d_2, 8),
        (7, pieces.e_0, 6),
        (8, pieces.e_1, 4),
        (11, pieces.g_1, 9),
        (13, pieces.h_0, 5),
    ] {
        write_short_range_check(writer, row_map, first_region + offset, short, width)?;
    }

    write_y_canonicity(writer, row_map, first_region + 15, &pieces.gd_y)?;
    write_y_canonicity(writer, row_map, first_region + 20, &pieces.pk_y)?;
    write_note_field_canonicity(writer, row_map, first_region, &pieces)?;
    Ok(pieces)
}

/// Original note coordinates and fields, eight hash pieces (`a` through `h`),
/// and the boundary fragments needed to prove those pieces canonical.
pub(super) struct NotePieces {
    pub(super) gd_x: Fp,
    pub(super) gd_y: Fp,
    pub(super) pk_x: Fp,
    pub(super) pk_y: Fp,
    pub(super) value: Fp,
    pub(super) rho: Fp,
    pub(super) psi: Fp,
    pub(super) a: Fp,
    pub(super) b: Fp,
    pub(super) c: Fp,
    pub(super) d: Fp,
    pub(super) e: Fp,
    pub(super) f: Fp,
    pub(super) g: Fp,
    pub(super) h: Fp,
    pub(super) b_0: Fp,
    pub(super) b_1: Fp,
    pub(super) b_3: Fp,
    pub(super) d_0: Fp,
    pub(super) d_2: Fp,
    pub(super) e_0: Fp,
    pub(super) e_1: Fp,
    pub(super) g_0: Fp,
    pub(super) g_1: Fp,
    pub(super) g_2: Fp,
    pub(super) h_0: Fp,
    pub(super) h_1: Fp,
}

fn write_y_canonicity(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    first_region: usize,
    y: &Fp,
) -> Result<(), Error> {
    let lsb = bitrange(y, 0, 1)?;
    let k_0 = bitrange(y, 1, 10)?;
    let k_2 = bitrange(y, 250, 254)?;
    let k_3 = bitrange(y, 254, 255)?;
    let j = bitrange(y, 0, 250)?;
    // Canonicity witness `j' = j + 2^130 − t_P`, with `t_P` as a field value.
    let j_prime = j
        .add(&power_of_two(130))
        .sub(&<Fp>::from_bytes_reduced(&T_P.to_le_bytes()));
    write_short_range_check(writer, row_map, first_region, k_0, 9)?;
    write_short_range_check(writer, row_map, first_region + 1, k_2, 4)?;
    // Column 9, offsets +2/+3: 25/13 ten-bit words; only `j` must end at zero.
    write_scheduled_running_sum(writer, row_map, 9, first_region + 2, &j, 10, 25, true)?;
    write_scheduled_running_sum(
        writer,
        row_map,
        9,
        first_region + 3,
        &j_prime,
        10,
        13,
        false,
    )?;
    write_region_cells(
        writer,
        row_map,
        first_region + 4,
        [
            (5, 0, *y),
            (6, 0, lsb),
            (7, 0, k_0),
            (8, 0, k_2),
            (9, 0, k_3),
            (5, 1, j),
            (6, 1, running_sum_at(&j, 1)?),
            (7, 1, running_sum_at(&j, 13)?),
            (8, 1, j_prime),
            (9, 1, running_sum_at(&j_prime, 13)?),
        ],
    )
}

fn write_note_field_canonicity(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    first_region: usize,
    pieces: &NotePieces,
) -> Result<(), Error> {
    // `t_P` as a field value for the `piece + 2^k − t_P` canonicity witnesses.
    let t_p = <Fp>::from_bytes_reduced(&T_P.to_le_bytes());
    let a_prime = pieces.a.add(&power_of_two(130)).sub(&t_p);
    let b3_c_prime = pieces
        .b_3
        .add(&pieces.c.mul(&<Fp>::from_u64(1 << 4)))
        .add(&power_of_two(140))
        .sub(&t_p);
    let e1_f_prime = pieces
        .e_1
        .add(&pieces.f.mul(&<Fp>::from_u64(1 << 4)))
        .add(&power_of_two(140))
        .sub(&t_p);
    let g1_g2_prime = pieces
        .g_1
        .add(&pieces.g_2.mul(&<Fp>::from_u64(1 << 9)))
        .add(&power_of_two(130))
        .sub(&t_p);

    let z13_a = running_sum_at(&pieces.a, 13)?;
    let z13_c = running_sum_at(&pieces.c, 13)?;
    let z1_d = running_sum_at(&pieces.d, 1)?;
    let z13_f = running_sum_at(&pieces.f, 13)?;
    let z1_g = running_sum_at(&pieces.g, 1)?;
    let z13_g = running_sum_at(&pieces.g, 13)?;

    // Column 9, offsets +29..=+32: 13/14/14/13 ten-bit words, allowing remainders.
    // Each prime value's running sum is written once; the final-check cells
    // below read the one term they reuse through `running_sum_at`.
    write_scheduled_running_sum(
        writer,
        row_map,
        9,
        first_region + 29,
        &a_prime,
        10,
        13,
        false,
    )?;
    write_scheduled_running_sum(
        writer,
        row_map,
        9,
        first_region + 30,
        &b3_c_prime,
        10,
        14,
        false,
    )?;
    write_scheduled_running_sum(
        writer,
        row_map,
        9,
        first_region + 31,
        &e1_f_prime,
        10,
        14,
        false,
    )?;
    write_scheduled_running_sum(
        writer,
        row_map,
        9,
        first_region + 32,
        &g1_g2_prime,
        10,
        13,
        false,
    )?;

    write_region_cells(
        writer,
        row_map,
        first_region + 33,
        [
            (6, 0, pieces.b),
            (7, 0, pieces.b_0),
            (8, 0, pieces.b_1),
            (7, 1, bitrange(&pieces.gd_y, 0, 1)?),
            (8, 1, pieces.b_3),
        ],
    )?;
    write_region_cells(
        writer,
        row_map,
        first_region + 34,
        [
            (6, 0, pieces.d),
            (7, 0, pieces.d_0),
            (8, 0, bitrange(&pieces.pk_y, 0, 1)?),
            (7, 1, pieces.d_2),
            (8, 1, z1_d),
        ],
    )?;
    write_region_cells(
        writer,
        row_map,
        first_region + 35,
        [(6, 0, pieces.e), (7, 0, pieces.e_0), (8, 0, pieces.e_1)],
    )?;
    write_region_cells(
        writer,
        row_map,
        first_region + 36,
        [
            (6, 0, pieces.g),
            (7, 0, pieces.g_0),
            (6, 1, pieces.g_1),
            (7, 1, z1_g),
        ],
    )?;
    write_region_cells(
        writer,
        row_map,
        first_region + 37,
        [(6, 0, pieces.h), (7, 0, pieces.h_0), (8, 0, pieces.h_1)],
    )?;
    write_region_cells(
        writer,
        row_map,
        first_region + 38,
        [
            (6, 0, pieces.gd_x),
            (7, 0, pieces.b_0),
            (7, 1, pieces.b_1),
            (8, 0, pieces.a),
            (8, 1, a_prime),
            (9, 0, z13_a),
            (9, 1, running_sum_at(&a_prime, 13)?),
        ],
    )?;
    write_region_cells(
        writer,
        row_map,
        first_region + 39,
        [
            (6, 0, pieces.pk_x),
            (7, 0, pieces.b_3),
            (7, 1, pieces.d_0),
            (8, 0, pieces.c),
            (8, 1, b3_c_prime),
            (9, 0, z13_c),
            (9, 1, running_sum_at(&b3_c_prime, 14)?),
        ],
    )?;
    write_region_cells(
        writer,
        row_map,
        first_region + 40,
        [
            (6, 0, pieces.value),
            (7, 0, pieces.d_2),
            (8, 0, z1_d),
            (9, 0, pieces.e_0),
        ],
    )?;
    write_region_cells(
        writer,
        row_map,
        first_region + 41,
        [
            (6, 0, pieces.rho),
            (7, 0, pieces.e_1),
            (7, 1, pieces.g_0),
            (8, 0, pieces.f),
            (8, 1, e1_f_prime),
            (9, 0, z13_f),
            (9, 1, running_sum_at(&e1_f_prime, 14)?),
        ],
    )?;
    write_region_cells(
        writer,
        row_map,
        first_region + 42,
        [
            (6, 0, pieces.psi),
            (6, 1, pieces.h_0),
            (7, 0, pieces.g_1),
            (7, 1, pieces.h_1),
            (8, 0, z1_g),
            (8, 1, g1_g2_prime),
            (9, 0, z13_g),
            (9, 1, running_sum_at(&g1_g2_prime, 13)?),
        ],
    )
}
