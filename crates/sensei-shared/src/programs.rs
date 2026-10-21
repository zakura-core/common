//! The 207 gate and lookup recipes, generic over their arithmetic.
//!
//! The tree algebra preserves operand order, negations, and constant-scaling
//! nodes for the frozen digest and the recursive oracle. The row algebra
//! specializes these same recipes to field arithmetic over validated columns.
//! Sparse gate checks omit only the fixed root factor, using its prepared
//! active rows; program selection occurs outside the row loop.
//!
//! Recipe arguments use distinct index spaces: program indices select an
//! expression in `0..PROGRAM_COUNT`; fixed/advice query indices select slots
//! in [`crate::queries::FIXED_QUERIES`] or [`crate::queries::ADVICE_QUERIES`],
//! which carry the column and rotation; constant indices select entries in
//! [`crate::constants::CONSTANTS`]. A helper's constraint index or matrix row
//! selects within that helper, as documented on the method.

mod algebra;
mod field;
mod trees;

pub use algebra::{Algebra, Value};
pub use trees::expression_programs;

// Frequently repeated constant-pool indices, not field values.
const TWO_INDEX: u8 = 0;
const ONE_INDEX: u8 = 5;
const TWO_POW_130_INDEX: u8 = 16;
// t_P = p - 2^254 for the Pallas base-field modulus p.
const T_P_INDEX: u8 = 17;
const TWO_POW_140_INDEX: u8 = 43;

/// Builds or evaluates the gate or lookup expression at `index` in protocol
/// order, with `index` in `0..PROGRAM_COUNT`
/// ([`crate::expressions::PROGRAM_COUNT`]).
///
/// Callers specialize `index` before entering a gate's row loop. Keeping each
/// body in its own match arm avoids evaluating other constraints in its group.
/// The supplied algebra determines full evaluation versus the sparse gate
/// zero-test interpretation described by [`Algebra::gated`].
///
/// # Panics
///
/// Panics if `index >= PROGRAM_COUNT`.
#[inline(always)]
pub fn expression<A: Algebra>(a: &A, index: usize) -> A::Value {
    // Witness/layout paths below are relative to crates/sensei/src/native/.
    match index {
        // 0..=3: statement and cross-address relations (witness/synthesis.rs).
        0..=3 => a.gated(
            || a.selector(18, &[0, 1, 2, 3, 4]),
            match index {
                0 => a.sub(
                    a.sub(a.advice(0), a.advice(1)),
                    a.advice(2).mul(a.advice(3)),
                ),
                1 => a.advice(0).mul(a.sub(a.advice(4), a.advice(5))),
                2 => a.advice(0).mul(a.sub(a.constant(ONE_INDEX), a.advice(6))),
                3 => a.advice(1).mul(a.sub(a.constant(ONE_INDEX), a.advice(7))),
                _ => unreachable!(),
            },
        ),
        // 4: nullifier scalar addition (witness/poseidon.rs::write_nullifier).
        4 => a.gated(
            || a.selector(18, &[5, 1, 2, 3, 4]),
            a.sub(a.advice(7).add(a.advice(8)), a.advice(6)),
        ),
        // 5: short range check (witness/mod.rs::write_short_range_check).
        5 => a.gated(
            || a.selector(18, &[5, 0, 2, 3, 4]),
            a.sub(
                a.advice(11).multiply_constant(6).mul(a.advice(10)),
                a.advice(9),
            ),
        ),
        // 6..=8: point membership, allowing identity at 6..=7 (witness/mod.rs::write_point).
        6..=7 => a.gated(
            // Retain the reviewed selector * (coordinate * curve) root split.
            || a.selector(19, &[0, 1, 2]),
            a.advice((index - 6) as u8).mul(a.on_curve(0, 1)),
        ),
        8 => a.gated(|| a.selector(19, &[5, 1, 2]), a.on_curve(0, 1)),
        // 9..=10: incomplete addition (witness/fixed_base.rs::write_fixed_incomplete_region).
        9..=10 => a.gated(
            || a.selector(19, &[5, 0, 2]),
            match index - 9 {
                0 => a.sub(
                    a.advice(12)
                        .add(a.advice(2))
                        .add(a.advice(0))
                        .mul(a.sub(a.advice(0), a.advice(2)))
                        .mul(a.sub(a.advice(0), a.advice(2))),
                    a.square(a.sub(a.advice(1), a.advice(3))),
                ),
                1 => a.sub(
                    a.advice(13)
                        .add(a.advice(3))
                        .mul(a.sub(a.advice(0), a.advice(2))),
                    a.sub(a.advice(1), a.advice(3))
                        .mul(a.sub(a.advice(2), a.advice(12))),
                ),
                _ => unreachable!(),
            },
        ),
        // 11..=22: complete addition (witness/mod.rs::write_complete_addition).
        11..=22 => a.gated(
            || a.selector(19, &[5, 0, 1]),
            match index - 11 {
                0 => a.sub(a.advice(2), a.advice(0)).mul(a.sub(
                    a.sub(a.advice(2), a.advice(0)).mul(a.advice(4)),
                    a.sub(a.advice(3), a.advice(1)),
                )),
                1 => a
                    .sub(
                        a.constant(ONE_INDEX),
                        a.sub(a.advice(2), a.advice(0)).mul(a.advice(5)),
                    )
                    .mul(a.sub(
                        a.constant(TWO_INDEX).mul(a.advice(1)).mul(a.advice(4)),
                        a.constant(1).mul(a.square(a.advice(0))),
                    )),
                2 => a
                    .advice(0)
                    .mul(a.advice(2))
                    .mul(a.sub(a.advice(2), a.advice(0)))
                    .mul(a.sub(
                        a.sub(a.sub(a.square(a.advice(4)), a.advice(0)), a.advice(2)),
                        a.advice(12),
                    )),
                3 => a
                    .advice(0)
                    .mul(a.advice(2))
                    .mul(a.sub(a.advice(2), a.advice(0)))
                    .mul(a.sub(
                        a.sub(
                            a.advice(4).mul(a.sub(a.advice(0), a.advice(12))),
                            a.advice(1),
                        ),
                        a.advice(13),
                    )),
                4 => a
                    .advice(0)
                    .mul(a.advice(2))
                    .mul(a.advice(3).add(a.advice(1)))
                    .mul(a.sub(
                        a.sub(a.sub(a.square(a.advice(4)), a.advice(0)), a.advice(2)),
                        a.advice(12),
                    )),
                5 => a
                    .advice(0)
                    .mul(a.advice(2))
                    .mul(a.advice(3).add(a.advice(1)))
                    .mul(a.sub(
                        a.sub(
                            a.advice(4).mul(a.sub(a.advice(0), a.advice(12))),
                            a.advice(1),
                        ),
                        a.advice(13),
                    )),
                6 => a
                    .sub(a.constant(ONE_INDEX), a.advice(0).mul(a.advice(6)))
                    .mul(a.sub(a.advice(12), a.advice(2))),
                7 => a
                    .sub(a.constant(ONE_INDEX), a.advice(0).mul(a.advice(6)))
                    .mul(a.sub(a.advice(13), a.advice(3))),
                8 => a
                    .sub(a.constant(ONE_INDEX), a.advice(2).mul(a.advice(7)))
                    .mul(a.sub(a.advice(12), a.advice(0))),
                9 => a
                    .sub(a.constant(ONE_INDEX), a.advice(2).mul(a.advice(7)))
                    .mul(a.sub(a.advice(13), a.advice(1))),
                10 => a
                    .sub(
                        a.sub(
                            a.constant(ONE_INDEX),
                            a.sub(a.advice(2), a.advice(0)).mul(a.advice(5)),
                        ),
                        a.advice(3).add(a.advice(1)).mul(a.advice(8)),
                    )
                    .mul(a.advice(12)),
                11 => a
                    .sub(
                        a.sub(
                            a.constant(ONE_INDEX),
                            a.sub(a.advice(2), a.advice(0)).mul(a.advice(5)),
                        ),
                        a.advice(3).add(a.advice(1)).mul(a.advice(8)),
                    )
                    .mul(a.advice(13)),
                _ => unreachable!(),
            },
        ),
        // 23..=54: variable-base high/low chains, overflow and tail-bit selection.
        // See witness/variable_base.rs and regions/variable_base_mul.rs.
        23 => a.gated(
            || a.selector(18, &[5, 0, 1, 3, 4]),
            a.sub(
                a.advice(4),
                a.slope_product(14, 15, 13, 16).multiply_constant(7),
            ),
        ),
        24..=29 => a.gated(
            || a.selector(18, &[5, 0, 1, 2, 4]),
            match index - 24 {
                0 => a.sub(a.advice(0), a.advice(16)),
                1 => a.sub(a.advice(1), a.advice(17)),
                offset => a.incomplete_addition(
                    offset - 2,
                    [4, 5, 3, 13],
                    || a.digit(9, 11, 0),
                    || a.slope_product(14, 15, 13, 16).multiply_constant(7),
                ),
            },
        ),
        30..=33 => a.gated(
            || a.selector(18, &[5, 0, 1, 2, 3]),
            a.incomplete_addition(
                index - 30,
                [4, 5, 3, 13],
                || a.digit(9, 11, 0),
                || a.advice(14),
            ),
        ),
        34 => a.gated(
            || a.selector(20, &[0, 1, 2, 3]),
            a.sub(
                a.advice(8),
                a.slope_product(19, 12, 18, 16).multiply_constant(7),
            ),
        ),
        35..=40 => a.gated(
            || a.selector(20, &[5, 1, 2, 3]),
            match index - 35 {
                0 => a.sub(a.advice(0), a.advice(16)),
                1 => a.sub(a.advice(1), a.advice(17)),
                offset => a.incomplete_addition(
                    offset - 2,
                    [8, 2, 7, 18],
                    || a.digit(6, 20, 0),
                    || a.slope_product(19, 12, 18, 16).multiply_constant(7),
                ),
            },
        ),
        41..=44 => a.gated(
            || a.selector(20, &[5, 0, 2, 3]),
            a.incomplete_addition(
                index - 41,
                [8, 2, 7, 18],
                || a.digit(6, 20, 0),
                || a.advice(19),
            ),
        ),
        45..=46 => a.gated(
            || a.selector(20, &[5, 0, 1, 3]),
            match index - 45 {
                0 => a.boolean(a.sub(a.advice(10), a.constant(TWO_INDEX).mul(a.advice(11)))),
                1 => a.select(
                    a.sub(a.advice(10), a.constant(TWO_INDEX).mul(a.advice(11))),
                    a.sub(a.advice(9), a.advice(21)),
                    a.advice(9).add(a.advice(21)),
                ),
                _ => unreachable!(),
            },
        ),
        47..=51 => a.gated(
            || a.selector(20, &[5, 0, 1, 2]),
            match index - 47 {
                0 => a.sub(
                    a.advice(8),
                    a.advice(7)
                        .add(a.advice(23).mul(a.constant(8).mul(a.constant(9)))),
                ),
                1 => a.sub(a.sub(a.advice(20), a.advice(7)), a.constant(10)),
                2 => a.advice(23).mul(a.sub(a.advice(6), a.constant(8))),
                3 => a.advice(23).mul(a.advice(18)),
                4 => a
                    .sub(a.constant(ONE_INDEX), a.advice(23))
                    .mul(a.sub(a.constant(ONE_INDEX), a.advice(6).mul(a.advice(22))))
                    .mul(a.advice(18)),
                _ => unreachable!(),
            },
        ),
        52..=54 => a.gated(
            || a.selector(21, &[0, 1, 2]),
            match index - 52 {
                0 => a.boolean(a.digit(10, 9, 0)),
                1 => a.select(
                    a.digit(10, 9, 0),
                    a.advice(0),
                    a.sub(a.advice(0), a.advice(16)),
                ),
                2 => a.select(
                    a.digit(10, 9, 0),
                    a.advice(1),
                    a.advice(1).add(a.advice(17)),
                ),
                _ => unreachable!(),
            },
        ),
        // 55..=62: fixed-base windows, with running-sum digits at 55..=58 and explicit
        // digits at 59..=62 (witness/fixed_base.rs::write_fixed_incomplete_region).
        55..=58 => a.gated(
            || a.fixed(22),
            match index - 55 {
                0 => a.vanishing(a.digit(4, 14, 11), &[5, 0, 1, 2, 3, 4, 12]),
                1 => a.interpolate_x(a.digit(4, 14, 11)),
                2 => a.sub(a.sub(a.square(a.advice(5)), a.advice(1)), a.fixed(2)),
                3 => a.on_curve(0, 1),
                _ => unreachable!(),
            },
        ),
        59..=62 => a.gated(
            || a.fixed(23),
            match index - 59 {
                0 => a.interpolate_x(a.advice(4)),
                1 => a.sub(a.sub(a.square(a.advice(5)), a.advice(1)), a.fixed(2)),
                2 => a.on_curve(0, 1),
                3 => a.vanishing(a.advice(4), &[5, 0, 1, 2, 3, 4, 12]),
                _ => unreachable!(),
            },
        ),
        // 63..=66: short fixed-base sign (witness/fixed_base.rs::write_short_fixed_mul).
        63..=66 => a.gated(
            || a.selector(21, &[5, 1, 2]),
            match index - 63 {
                0 => a.boolean(a.advice(5)),
                1 => a.sub(a.square(a.advice(4)), a.constant(ONE_INDEX)),
                2 => a
                    .sub(a.advice(1), a.advice(3))
                    .mul(a.advice(1).add(a.advice(3))),
                3 => a.sub(a.advice(4).mul(a.advice(1)), a.advice(3)),
                _ => unreachable!(),
            },
        ),
        // 67..=74: base-field scalar canonicity
        // (witness/fixed_base.rs::write_base_field_fixed_mul).
        67..=74 => a.gated(
            || a.selector(21, &[5, 0, 2]),
            match index - 67 {
                0 => a.advice(8).mul(a.advice(7)),
                1 => a
                    .advice(8)
                    .mul(a.sub(a.advice(18), a.advice(24).mul(a.constant(14)))),
                2 => a.advice(8).mul(a.boolean(a.digit(19, 18, 11))),
                3 => a.advice(8).mul(a.advice(22)),
                4 => a.vanishing(a.advice(7), &[5, 0, 1]),
                5 => a.boolean(a.advice(8)),
                6 => a.sub(a.advice(24), a.linear(7, &[(8, 2)])),
                7 => a.sub(
                    a.advice(6),
                    a.sub(
                        a.digit(20, 24, 15).add(a.constant(TWO_POW_130_INDEX)),
                        a.constant(T_P_INDEX),
                    ),
                ),
                _ => unreachable!(),
            },
        ),
        // 75..=84: Poseidon full rounds, paired partial rounds, then input padding
        // (witness/poseidon.rs::write_poseidon_hash).
        75..=77 => a.gated(
            || a.selector(21, &[5, 0, 1]),
            a.poseidon_full_round_body((index - 75) as u8),
        ),
        78..=81 => a.gated(
            || a.selector(24, &[0, 1, 2]),
            if index == 78 {
                a.sub(a.pow5(a.advice(6).add(a.fixed(4))), a.advice(5))
            } else {
                let row = (index - 79) as u8;
                let input = a
                    .mix(
                        [
                            a.advice(5),
                            a.advice(7).add(a.fixed(5)),
                            a.advice(8).add(a.fixed(6)),
                        ],
                        18 + 3 * row,
                    )
                    .add(a.fixed(7 + row));
                a.sub(
                    if row == 0 { a.pow5(input) } else { input },
                    a.mix([a.advice(22), a.advice(18), a.advice(19)], 27 + 3 * row),
                )
            },
        ),
        82..=84 => a.gated(
            || a.selector(24, &[5, 1, 2]),
            match index - 82 {
                0 => a.sub(a.advice(20).add(a.advice(6)), a.advice(22)),
                1 => a.sub(a.advice(23).add(a.advice(7)), a.advice(18)),
                2 => a.sub(a.advice(24), a.advice(19)),
                _ => unreachable!(),
            },
        ),
        // 85..=87: Sinsemilla initialization and steps on advice columns 0..=4
        // (witness/sinsemilla.rs::write_sinsemilla_hash).
        85 => a.gated(
            || a.selector(24, &[5, 0, 2]),
            a.sub(a.fixed(0).multiply_constant(0), a.slope_product(3, 4, 0, 1)),
        ),
        86..=87 => a.gated(
            || a.fixed(16),
            match index - 86 {
                0 => a.sub(
                    a.square(a.advice(4)),
                    a.advice(16).add(a.secant_x(3, 0, 1)).add(a.advice(0)),
                ),
                1 => a.sub(
                    a.advice(4)
                        .multiply_constant(2)
                        .mul(a.sub(a.advice(0), a.advice(16))),
                    a.slope_product(3, 4, 0, 1)
                        .multiply_constant(0)
                        .add(
                            a.sub(
                                a.constant(TWO_INDEX),
                                a.fixed(10).mul(a.sub(a.fixed(10), a.constant(ONE_INDEX))),
                            )
                            .mul(a.slope_product(13, 14, 16, 17)),
                        )
                        .add(
                            a.fixed(10)
                                .mul(a.sub(a.fixed(10), a.constant(ONE_INDEX)))
                                .multiply_constant(0)
                                .mul(a.advice(13)),
                        ),
                ),
                _ => unreachable!(),
            },
        ),
        // 88..=94: Merkle swap and decomposition on advice columns 0..=4
        // (witness/sinsemilla.rs::write_merkle_path).
        88..=90 => a.gated(
            || a.selector(24, &[5, 0, 1]),
            match index - 88 {
                0 => a.sub(a.advice(2), a.select(a.advice(4), a.advice(1), a.advice(0))),
                1 => a.sub(a.advice(3), a.select(a.advice(4), a.advice(0), a.advice(1))),
                2 => a.boolean(a.advice(4)),
                _ => unreachable!(),
            },
        ),
        91..=94 => a.gated(
            || a.selector(25, &[0, 1, 2, 3, 4]),
            match index - 91 {
                0 => a.sub(a.digit(0, 16, 6), a.advice(14)),
                1 => a.sub(
                    a.advice(16).add(
                        a.digit(1, 17, 6)
                            .add(a.advice(12).multiply_constant(6))
                            .multiply_constant(36),
                    ),
                    a.advice(3),
                ),
                2 => a.sub(a.linear(13, &[(2, 37)]), a.advice(4)),
                3 => a.sub(a.advice(17), a.linear(12, &[(13, 37)])),
                _ => unreachable!(),
            },
        ),
        // 95..=97: Sinsemilla initialization and steps on advice columns 5..=9
        // (witness/sinsemilla.rs::write_sinsemilla_hash).
        95 => a.gated(
            || a.selector(25, &[5, 1, 2, 3, 4]),
            a.sub(a.fixed(3).multiply_constant(0), a.slope_product(8, 9, 5, 6)),
        ),
        96..=97 => a.gated(
            || a.fixed(17),
            match index - 96 {
                0 => a.sub(
                    a.square(a.advice(9)),
                    a.advice(15).add(a.secant_x(8, 5, 6)).add(a.advice(5)),
                ),
                1 => a.sub(
                    a.advice(9)
                        .multiply_constant(2)
                        .mul(a.sub(a.advice(5), a.advice(15))),
                    a.slope_product(8, 9, 5, 6)
                        .multiply_constant(0)
                        .add(
                            a.sub(
                                a.constant(TWO_INDEX),
                                a.fixed(13).mul(a.sub(a.fixed(13), a.constant(ONE_INDEX))),
                            )
                            .mul(a.slope_product(19, 10, 15, 22)),
                        )
                        .add(
                            a.fixed(13)
                                .mul(a.sub(a.fixed(13), a.constant(ONE_INDEX)))
                                .multiply_constant(0)
                                .mul(a.advice(19)),
                        ),
                ),
                _ => unreachable!(),
            },
        ),
        // 98..=104: Merkle swap and decomposition on advice columns 5..=9
        // (witness/sinsemilla.rs::write_merkle_path).
        98..=100 => a.gated(
            || a.selector(26, &[0, 1, 2, 3, 4, 12]),
            match index - 98 {
                0 => a.sub(a.advice(7), a.select(a.advice(9), a.advice(6), a.advice(5))),
                1 => a.sub(a.advice(8), a.select(a.advice(9), a.advice(5), a.advice(6))),
                2 => a.boolean(a.advice(9)),
                _ => unreachable!(),
            },
        ),
        101..=104 => a.gated(
            || a.selector(26, &[5, 1, 2, 3, 4, 12]),
            match index - 101 {
                0 => a.sub(a.digit(5, 15, 6), a.advice(10)),
                1 => a.sub(
                    a.advice(15).add(
                        a.digit(6, 22, 6)
                            .add(a.advice(18).multiply_constant(6))
                            .multiply_constant(36),
                    ),
                    a.advice(8),
                ),
                2 => a.sub(a.linear(19, &[(7, 37)]), a.advice(9)),
                3 => a.sub(a.advice(22), a.linear(18, &[(19, 37)])),
                _ => unreachable!(),
            },
        ),
        // 105..=118: commit_ivk message decomposition and canonicity
        // (witness/decomposition.rs::write_commit_ivk_decomposition).
        105..=118 => a.gated(
            || a.selector(25, &[5, 0, 2, 3, 4]),
            match index - 105 {
                0 => a.boolean(a.advice(4)),
                1 => a.boolean(a.advice(14)),
                2 => a.sub(a.advice(2), a.linear(3, &[(4, 38), (5, 37)])),
                3 => a.sub(a.advice(12), a.linear(13, &[(14, 39)])),
                4 => a.sub(a.linear(1, &[(3, 40), (4, 41)]), a.advice(0)),
                5 => a.sub(a.linear(5, &[(17, 37), (13, 42), (14, 41)]), a.advice(16)),
                6 => a.advice(4).mul(a.advice(3)),
                7 => a.advice(4).mul(a.advice(6)),
                8 => a.sub(
                    a.sub(
                        a.advice(1).add(a.constant(TWO_POW_130_INDEX)),
                        a.constant(T_P_INDEX),
                    ),
                    a.advice(7),
                ),
                9 => a.advice(4).mul(a.advice(8)),
                10 => a.advice(14).mul(a.advice(13)),
                11 => a.advice(14).mul(a.advice(22)),
                12 => a.sub(
                    a.sub(
                        a.linear(5, &[(17, 37)]).add(a.constant(TWO_POW_140_INDEX)),
                        a.constant(T_P_INDEX),
                    ),
                    a.advice(18),
                ),
                13 => a.advice(14).mul(a.advice(19)),
                _ => unreachable!(),
            },
        ),
        // 119..=155: old-note message decomposition and canonicity (Algebra::range_body;
        // witness/decomposition.rs::write_note_decomposition).
        119..=121 => a.gated(
            || a.selector(25, &[5, 0, 1, 3, 4]),
            a.range_body(index - 119),
        ),
        122..=124 => a.gated(
            || a.selector(25, &[5, 0, 1, 2, 4]),
            a.range_body(index - 119),
        ),
        125 => a.gated(
            || a.selector(25, &[5, 0, 1, 2, 3]),
            a.range_body(index - 119),
        ),
        126..=127 => a.gated(
            || a.selector(26, &[5, 0, 2, 3, 4, 12]),
            a.range_body(index - 119),
        ),
        128..=129 => a.gated(
            || a.selector(26, &[5, 0, 1, 3, 4, 12]),
            a.range_body(index - 119),
        ),
        130..=134 => a.gated(
            || a.selector(26, &[5, 0, 1, 2, 4, 12]),
            a.range_body(index - 119),
        ),
        135..=138 => a.gated(
            || a.selector(26, &[5, 0, 1, 2, 3, 12]),
            a.range_body(index - 119),
        ),
        139 => a.gated(
            || a.selector(26, &[5, 0, 1, 2, 3, 4]),
            a.range_body(index - 119),
        ),
        140..=143 => a.gated(
            || a.selector(27, &[0, 1, 2, 3, 4, 12]),
            a.range_body(index - 119),
        ),
        144..=148 => a.gated(
            || a.selector(27, &[5, 1, 2, 3, 4, 12]),
            a.range_body(index - 119),
        ),
        149..=155 => a.gated(
            || a.selector(27, &[5, 0, 2, 3, 4, 12]),
            a.range_body(index - 119),
        ),
        // 156..=192: new-note counterpart of 119..=155, using the same range_body
        // and witness/decomposition.rs::write_note_decomposition.
        156..=158 => a.gated(
            || a.selector(27, &[5, 0, 1, 3, 4, 12]),
            a.range_body(index - 156),
        ),
        159..=161 => a.gated(
            || a.selector(27, &[5, 0, 1, 2, 4, 12]),
            a.range_body(index - 156),
        ),
        162 => a.gated(
            || a.selector(27, &[5, 0, 1, 2, 3, 12]),
            a.range_body(index - 156),
        ),
        163..=164 => a.gated(
            || a.selector(27, &[5, 0, 1, 2, 3, 4]),
            a.range_body(index - 156),
        ),
        165..=166 => a.gated(
            || a.selector(28, &[0, 1, 2, 3, 4, 12]),
            a.range_body(index - 156),
        ),
        167..=171 => a.gated(
            || a.selector(28, &[5, 1, 2, 3, 4, 12]),
            a.range_body(index - 156),
        ),
        172..=175 => a.gated(
            || a.selector(28, &[5, 0, 2, 3, 4, 12]),
            a.range_body(index - 156),
        ),
        176 => a.gated(
            || a.selector(28, &[5, 0, 1, 3, 4, 12]),
            a.range_body(index - 156),
        ),
        177..=180 => a.gated(
            || a.selector(28, &[5, 0, 1, 2, 4, 12]),
            a.range_body(index - 156),
        ),
        181..=185 => a.gated(
            || a.selector(28, &[5, 0, 1, 2, 3, 12]),
            a.range_body(index - 156),
        ),
        186..=192 => a.gated(
            || a.selector(28, &[5, 0, 1, 2, 3, 4]),
            a.range_body(index - 156),
        ),
        // 193..=194: range-check lookup input/table (witness/decomposition.rs running
        // sums and witness/mod.rs::write_short_range_check).
        193 => a.gated(
            || a.fixed(14),
            a.select(a.fixed(15), a.digit(9, 10, 6), a.advice(9)),
        ),
        194 => a.fixed(1),
        // 195..=206: Sinsemilla lookup inputs/tables for advice columns 0..=4, then
        // 5..=9 (witness/sinsemilla.rs::write_sinsemilla_hash).
        195..=206 => {
            let (q, control, [x, y, slope, next_slope, input, word]) = if index < 201 {
                (16, 10, [0, 1, 3, 4, 2, 12])
            } else {
                (17, 13, [5, 6, 8, 9, 7, 18])
            };
            match (index - 195) % 6 {
                0 => a.fixed(q).mul(
                    a.sub(
                        a.advice(input),
                        a.sub(
                            a.fixed(control),
                            a.fixed(control)
                                .mul(a.sub(a.fixed(control), a.constant(ONE_INDEX))),
                        )
                        .mul(a.advice(word))
                        .multiply_constant(6),
                    ),
                ),
                1 => a.fixed(q).mul(a.advice(y)).add(
                    a.sub(a.constant(ONE_INDEX), a.fixed(q))
                        .multiply_constant(47),
                ),
                2 => a
                    .fixed(q)
                    .mul(
                        a.sub(
                            a.slope_product(slope, next_slope, x, y)
                                .multiply_constant(7),
                            a.advice(slope).mul(a.sub(a.advice(x), a.advice(y))),
                        ),
                    )
                    .add(
                        a.sub(a.constant(ONE_INDEX), a.fixed(q))
                            .multiply_constant(48),
                    ),
                3 => a.fixed(1),
                4 => a.fixed(11),
                5 => a.fixed(12),
                _ => unreachable!(),
            }
        }
        _ => unreachable!(),
    }
}
