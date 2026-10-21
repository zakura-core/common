//! Circuit-layout invariants, sparse copy/lookup censuses, and prepared storage.

use alloc::vec::Vec;

use crate::native::evaluation::query_value;
use crate::native::field::Fp;
use crate::native::fixed_columns::{FIXED_TUPLE_COUNT, SINSEMILLA_TABLE_ROWS, TUPLE_FIXED_COLUMNS};
use crate::native::generated_expressions::{QueryKind, evaluate, program_trees};

use super::super::{
    EXTENDED_N, FIXED_COLUMNS, FIXED_QUERIES, FIXED_TUPLES, N, PERMUTATION_COLUMN_COUNT, SIGMA_MAP,
    TUPLE_ASSIGNMENTS,
};

/// The embedded sigma map is a bijection on the permutation cells: the
/// property the retired load-time validation enforced, now pinned here.
#[test]
fn embedded_sigma_map_is_a_bijection() {
    let mut seen = alloc::vec![ false; PERMUTATION_COLUMN_COUNT * N];
    for index in SIGMA_MAP.iter().flatten() {
        let seen = seen
            .get_mut(usize::from(*index))
            .expect("every index targets a permutation cell");
        assert!(!*seen, "duplicate sigma target");
        *seen = true;
    }
    assert!(seen.iter().all(|seen| *seen));
}

/// Storage census separates embedded payloads from owned preparation.
#[test]
fn prepared_extended_domain_byte_census() {
    let target = crate::test_codec::target();
    let on_demand = crate::tuning::GATE_SELECTORS == crate::tuning::OptionalPreparation::OnDemand;
    assert_eq!(target.gate_selectors().is_none(), on_demand);
    assert_eq!(
        target.gate_selectors().map_or(0, size_of_val),
        if on_demand { 0 } else { 26_214_400 }
    );
    let fixed = target.fixed_polynomials().cosets();
    let sigma = target.sigma_polynomials().cosets();
    assert_eq!(fixed.len() * EXTENDED_N * size_of::<Fp>(), 15_204_352);
    assert_eq!(sigma.len() * EXTENDED_N * size_of::<Fp>(), 7_864_320);
    #[cfg(embed_fixed_cosets)]
    {
        let super::super::CosetColumns::Embedded(columns) = fixed else {
            panic!("embedded cosets must be borrowed")
        };
        assert!(core::ptr::eq(*columns, &super::super::FIXED_COSETS[..]));
    }
    #[cfg(embed_sigma_cosets)]
    {
        let super::super::CosetColumns::Embedded(columns) = sigma else {
            panic!("embedded cosets must be borrowed")
        };
        assert!(core::ptr::eq(*columns, &super::super::SIGMA_COSETS[..]));
    }
}

/// The precomputed active-row lists match a per-row evaluation of each
/// gate expression's fixed root factor; expressions without a factor
/// carry no list.
#[test]
fn gate_active_rows_match_per_row_factor_evaluation() {
    let target = crate::test_codec::target();
    for gate in target.gates() {
        for expression in gate.indices() {
            let factor = program_trees(expression).unwrap().fixed_factor();
            let rows = target.gate_active_rows(expression);
            let Some(factor) = factor else {
                assert!(rows.is_none(), "expression {expression}");
                continue;
            };
            let expected = (0..N)
                .filter(|&row| {
                    !evaluate(factor, &mut |kind, index| {
                        assert!(matches!(kind, QueryKind::Fixed));
                        query_value(&FIXED_QUERIES, index, target.fixed_values(), row)
                    })
                    .unwrap()
                    .is_zero()
                })
                .map(|row| row as u16)
                .collect::<Vec<_>>();
            assert_eq!(rows.unwrap(), expected, "expression {expression}");
        }
    }
}

/// The structural invariants of the embedded sparse fixed data that the
/// retired load-time parser enforced: distinct nonzero tuples, strictly
/// increasing in-range assignment rows, in-range tuple indices in
/// dictionary order of first reference, and every tuple referenced.
#[test]
fn embedded_fixed_tuples_hold_their_invariants() {
    use alloc::collections::BTreeSet;

    let mut encodings = BTreeSet::new();
    for tuple in FIXED_TUPLES {
        assert!(!tuple.iter().all(<Fp>::is_zero), "zero tuple");
        assert!(
            encodings.insert(tuple.map(|value| value.to_bytes())),
            "duplicate tuple"
        );
    }

    let mut referenced = [false; FIXED_TUPLE_COUNT];
    let mut previous_row = None;
    let mut next_new_tuple = 0;
    for assignment in TUPLE_ASSIGNMENTS {
        let row = usize::from(assignment.row);
        let tuple_index = usize::from(assignment.tuple);
        assert!(row < N, "assignment row out of range");
        assert!(
            previous_row.is_none_or(|previous| row > previous),
            "assignment rows not strictly increasing"
        );
        assert!(tuple_index < FIXED_TUPLE_COUNT, "tuple index out of range");
        if !referenced[tuple_index] {
            assert_eq!(
                tuple_index, next_new_tuple,
                "tuples not in dictionary order of first reference"
            );
            referenced[tuple_index] = true;
            next_new_tuple += 1;
        }
        previous_row = Some(row);
    }
    assert!(referenced.iter().all(|referenced| *referenced));
}

/// The source-owned control and selector layout is well formed: patterns
/// cover exactly the structured columns in order, and spans are ordered,
/// in range, and distinct from their column's small default value.
#[test]
fn structured_fixed_layout_is_well_formed() {
    use crate::native::fixed_columns::{STRUCTURED_FIXED_COLUMN_START, STRUCTURED_FIXED_COLUMNS};

    assert_eq!(
        STRUCTURED_FIXED_COLUMN_START + STRUCTURED_FIXED_COLUMNS.len(),
        FIXED_COLUMNS
    );
    for (index, pattern) in STRUCTURED_FIXED_COLUMNS.iter().enumerate() {
        assert_eq!(
            usize::from(pattern.column),
            STRUCTURED_FIXED_COLUMN_START + index
        );
        assert!(pattern.default <= 7);
        let mut previous_end = 0;
        for span in pattern.spans {
            let start = usize::from(span.start);
            let end = usize::from(span.end);
            assert!(start < end && end <= N && start >= previous_end);
            assert!(span.value <= 7 && span.value != pattern.default);
            previous_end = end;
        }
    }
}

/// The copy graph's structural sparsity, derived from the
/// committed `sigma_mapping` data. Cell `(column, row)` is encoded as
/// `column * N + row`; a fixed point (`sigma == id`) contributes a ratio
/// of exactly one to its chunk's grand product regardless of the witness.
#[test]
fn permutation_sigma_structural_census() {
    use super::super::{PERMUTATION_CHUNK_LEN, USABLE_ROWS_END};

    let target = crate::test_codec::target();
    let mapping = target.sigma_mapping();
    let columns = mapping.len();
    assert_eq!(columns, target.permutation_columns().len());
    assert_eq!(columns, 15);

    let mut fixed_points = 0usize;
    let mut row_edges = alloc::vec![ 0usize; N];
    for (column_index, column) in mapping.iter().enumerate() {
        assert_eq!(column.len(), N);
        for (row, &index) in column.iter().enumerate() {
            if usize::from(index) == column_index * N + row {
                fixed_points += 1;
            } else {
                row_edges[row] += 1;
            }
        }
    }
    // Copies never touch the blinding tail: every cell at or beyond
    // USABLE_ROWS_END is a fixed point.
    for &edges in &row_edges[USABLE_ROWS_END..] {
        assert_eq!(edges, 0);
    }
    let nontrivial_edges = columns * N - fixed_points;
    let zero_edge_rows = (0..USABLE_ROWS_END)
        .filter(|&row| row_edges[row] == 0)
        .count();

    // Per z-chunk ratio-one rows (all chunk columns fixed points) and
    // their maximal runs within the usable region.
    let column_indices = (0..columns).collect::<Vec<_>>();
    let mut chunk_census = Vec::new();
    for chunk in column_indices.chunks(PERMUTATION_CHUNK_LEN) {
        let ratio_one = |row: usize| {
            chunk
                .iter()
                .all(|&column| usize::from(mapping[column][row]) == column * N + row)
        };
        let mut rows = 0usize;
        let mut runs = 0usize;
        let mut longest = 0usize;
        let mut current = 0usize;
        for row in 0..USABLE_ROWS_END {
            if ratio_one(row) {
                if current == 0 {
                    runs += 1;
                }
                current += 1;
                rows += 1;
                longest = longest.max(current);
            } else {
                current = 0;
            }
        }
        chunk_census.push((rows, runs, longest));
    }

    assert_eq!(fixed_points, 29_061);
    assert_eq!(nontrivial_edges, 1_659);
    assert_eq!(zero_edge_rows, 1_385);
    // (ratio-one rows, maximal runs, longest run) per chunk. The third
    // chunk has no nontrivial edges anywhere: its grand product ratio is
    // one on every usable row.
    assert_eq!(
        chunk_census,
        alloc::vec![(1_776, 56, 268), (1_419, 141, 263), (2_042, 1, 2_042)]
    );
}

/// The prepared copy classes are exactly the nontrivial
/// sigma cycles — disjoint, canonical-first, in cycle order, covering
/// every nontrivial cell and staying inside the usable region.
#[test]
fn copy_classes_partition_nontrivial_sigma_cycles() {
    use super::super::USABLE_ROWS_END;

    let target = crate::test_codec::target();
    let mapping = target.sigma_mapping();
    let sigma = |cell: u16| mapping[usize::from(cell) / N][usize::from(cell) % N];

    let mut seen = alloc::collections::BTreeSet::new();
    let mut previous_canonical = None;
    let mut class_count = 0usize;
    for class in target.copy_classes().classes() {
        class_count += 1;
        assert!(class.len() >= 2, "a copy class has at least two members");
        let canonical = class[0];
        assert!(
            previous_canonical.is_none_or(|previous| previous < canonical),
            "classes are in ascending canonical order"
        );
        previous_canonical = Some(canonical);
        for (position, &cell) in class.iter().enumerate() {
            assert!(seen.insert(cell), "classes are disjoint");
            assert!(canonical <= cell, "the canonical member is the smallest");
            assert!(
                usize::from(cell) % N < USABLE_ROWS_END,
                "copies never touch the blinding tail"
            );
            // Members are in cycle order: sigma advances to the next.
            assert_eq!(sigma(cell), class[(position + 1) % class.len()]);
        }
    }

    // The members are exactly the nontrivial cells of the census above.
    assert_eq!(target.copy_classes().member_count(), 1_659);
    for (column_index, column) in mapping.iter().enumerate() {
        for (row, &index) in column.iter().enumerate() {
            let cell = (column_index * N + row) as u16;
            assert_eq!(
                seen.contains(&cell),
                usize::from(index) != column_index * N + row
            );
        }
    }
    // Verified against the committed data file: 733 cycles, mostly pairs
    // (571 of size 2, 156 of size 3, 3 of size 4, 2 of size 10, 1 of 17).
    assert_eq!(class_count, 733);
    let largest = target
        .copy_classes()
        .classes()
        .map(<[u16]>::len)
        .max()
        .unwrap();
    assert_eq!(largest, 17);
}

/// Sizes and duplicate-value structure of the fixed columns
/// that host lookup tables, derived from the committed fixed values.
#[test]
fn fixed_lookup_table_structural_census() {
    use alloc::collections::BTreeSet;

    use super::super::USABLE_ROWS_END;
    use crate::native::fixed_columns::{
        FIXED_TUPLE_ASSIGNMENTS, SINSEMILLA_COORDINATE_COLUMNS, TUPLE_FIXED_COLUMN_START,
    };

    let target = crate::test_codec::target();
    let fixed = target.fixed_values();
    assert_eq!(fixed.len(), FIXED_COLUMNS);

    // Column 0: the 10-bit Sinsemilla index table; the unused half of the
    // column (including the blinding tail) is zero.
    for (row, value) in fixed[0].iter().enumerate() {
        if row < SINSEMILLA_TABLE_ROWS {
            assert!((value).reduce() == (<Fp>::from_u64(row as u64)).reduce());
        } else {
            assert!(value.is_zero());
        }
    }

    // Columns 1 and 2: generator coordinates; rows after the table repeat
    // the first entry up to the blinding tail, which is zero. Together
    // with column 0's zeros, every padded usable row repeats row 0's
    // (index, x, y) tuple exactly.
    for column in &fixed[1..=SINSEMILLA_COORDINATE_COLUMNS] {
        for (row, value) in column.iter().enumerate().skip(SINSEMILLA_TABLE_ROWS) {
            if row < USABLE_ROWS_END {
                assert!((value).reduce() == (column[0]).reduce());
            } else {
                assert!(value.is_zero());
            }
        }
    }
    let distinct_generator_tuples = (0..SINSEMILLA_TABLE_ROWS)
        .map(|row| (fixed[1][row].to_bytes(), fixed[2][row].to_bytes()))
        .collect::<BTreeSet<_>>()
        .len();
    assert_eq!(distinct_generator_tuples, SINSEMILLA_TABLE_ROWS);

    // Tuple-dictionary columns 3..=11: sparse rows drawn from a small
    // dictionary of distinct nonzero tuples; all other rows are zero.
    let tuple_columns = TUPLE_FIXED_COLUMN_START..TUPLE_FIXED_COLUMN_START + TUPLE_FIXED_COLUMNS;
    let nonzero_rows = (0..N)
        .filter(|&row| {
            tuple_columns
                .clone()
                .any(|column| !fixed[column][row].is_zero())
        })
        .collect::<Vec<_>>();
    assert_eq!(nonzero_rows.len(), FIXED_TUPLE_ASSIGNMENTS);
    assert!(nonzero_rows.iter().all(|&row| row < USABLE_ROWS_END));
    let distinct_tuples = nonzero_rows
        .iter()
        .map(|&row| {
            tuple_columns
                .clone()
                .map(|column| fixed[column][row].to_bytes())
                .collect::<Vec<_>>()
        })
        .collect::<BTreeSet<_>>()
        .len();
    assert_eq!(distinct_tuples, FIXED_TUPLE_COUNT);
}
