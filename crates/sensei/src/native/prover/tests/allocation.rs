//! Sharing, validated storage boundaries, and scratch reuse.

use crate::Error;
use crate::native::prover;
use crate::native::test_support::reduced_values;
use alloc::{sync::Arc, vec::Vec};

#[test]
fn identical_lookup_tables_share_preparation_and_cosets() {
    let preparation = crate::test_codec::target().lookup_preparation();
    let table_sources = preparation.sources();
    use prover::{EXTENDED_N, Fp};

    assert_eq!(*table_sources, [0, 1, 1]);
    let sides = &preparation.sides;
    assert!(Arc::ptr_eq(
        sides[1].as_ref().unwrap(),
        sides[2].as_ref().unwrap()
    ));
    assert!(!Arc::ptr_eq(
        sides[0].as_ref().unwrap(),
        sides[1].as_ref().unwrap()
    ));
    let indices = &preparation.tables;
    assert!(Arc::ptr_eq(
        indices[1].as_ref().unwrap(),
        indices[2].as_ref().unwrap()
    ));

    let coset = |value: Fp| {
        prover::extended_coset_from_dense_rows(alloc::vec![ value; EXTENDED_N]).unwrap()
    };
    let tables = prover::lookup::share_compressed_tables(
        table_sources,
        alloc::vec![coset(<Fp>::ONE), coset(<Fp>::from_u64(7))],
    )
    .unwrap();
    assert_eq!(tables.len(), 3);
    assert!(!Arc::ptr_eq(&tables[0], &tables[1]));
    assert!(Arc::ptr_eq(&tables[1], &tables[2]));
    assert!(
        tables[0]
            .iter()
            .all(|value| (value).reduce() == (<Fp>::ONE).reduce())
    );
    assert!(
        tables[2]
            .iter()
            .all(|value| (value).reduce() == (<Fp>::from_u64(7)).reduce())
    );

    // A malformed column cannot become a coset record at all; missing,
    // extra, and forward-referencing inventories must fail before a lookup
    // can consume the wrong table.
    assert!(
        prover::extended_coset_from_dense_rows(alloc::vec![ <Fp>::ONE; EXTENDED_N - 1]).is_err()
    );
    for (sources, columns) in [
        (alloc::vec![0, 1, 1], alloc::vec![coset(<Fp>::ONE)]),
        (
            alloc::vec![0, 0],
            alloc::vec![coset(<Fp>::ONE), coset(<Fp>::ONE)],
        ),
        (alloc::vec![1, 1], alloc::vec![coset(<Fp>::ONE)]),
    ] {
        assert!(prover::lookup::share_compressed_tables(&sources, columns).is_err());
    }
}

/// A mis-shaped validated construction names the contract it broke for
/// the harness while callers see only the public error.
#[test]
fn validated_boundaries_record_their_failed_invariant() {
    use crate::native::invariant::{Invariant, take_last_failed};
    let _ = take_last_failed();
    let short = prover::SharedPoly::new(alloc::vec![ <prover::Fp>::ZERO; prover::N - 1]);
    assert!(matches!(
        prover::LagrangeColumn::new(short.clone()),
        Err(crate::Error::InternalInvariant)
    ));
    assert_eq!(take_last_failed(), Some(Invariant::BaseDomainLength));
    assert!(prover::BaseCoefficients::new(short).is_err());
    assert_eq!(take_last_failed(), Some(Invariant::BaseDomainLength));
    assert!(
        prover::extended_coset_from_dense_rows(alloc::vec![ <prover::Fp>::ZERO; prover::N])
            .is_err()
    );
    assert_eq!(take_last_failed(), Some(Invariant::ExtendedDomainLength));
    let target = crate::test_codec::target();
    let columns: Vec<Vec<prover::Fp>> = Vec::new();
    assert!(
        crate::native::evaluation::query_value(target.queries().advice(), 0, &columns, 0).is_err()
    );
    assert_eq!(take_last_failed(), Some(Invariant::ColumnShape));
    assert!(
        crate::native::evaluation::query_value(target.queries().advice(), 10_000, &columns, 0)
            .is_err()
    );
    assert_eq!(take_last_failed(), Some(Invariant::MissingQuery));
}

#[test]
fn deferred_fold_reuses_unique_storage_and_rejects_shared_storage() {
    use prover::opening::parallel_deferred_horner_fold;
    use prover::{Fp, N, SharedPoly};
    let polynomial = SharedPoly::new(alloc::vec![Fp::ONE; N]);
    let address = polynomial.as_ptr();
    let alias = polynomial.clone();
    assert!(matches!(
        parallel_deferred_horner_fold(crate::test_codec::execution(), alias, &[], &Fp::ONE),
        Err(Error::InternalInvariant)
    ));
    let result =
        parallel_deferred_horner_fold(crate::test_codec::execution(), polynomial, &[], &Fp::ZERO)
            .unwrap();
    assert_eq!(result.as_ptr(), address);
    assert!(
        result
            .iter()
            .all(|value| value.reduce() == <Fp>::ONE.reduce())
    );
}

#[test]
fn grouped_batch_inversion_retains_zeroes_and_reuses_scratch() {
    let mut groups = alloc::vec![
        alloc::vec![<prover::Fp>::from_u64(3), <prover::Fp>::ZERO],
        Vec::new(),
        alloc::vec![<prover::Fp>::from_u64(7), <prover::Fp>::ONE],
    ];
    let mut scratch = Vec::new();
    prover::products::batch_invert_groups(&mut groups, &mut scratch);
    assert_eq!(
        reduced_values(&(groups[0][0].mul(&<prover::Fp>::from_u64(3)))),
        reduced_values(&(<prover::Fp>::ONE))
    );
    assert_eq!(
        reduced_values(&(groups[0][1])),
        reduced_values(&(<prover::Fp>::ZERO))
    );
    assert_eq!(
        reduced_values(&(groups[2][0].mul(&<prover::Fp>::from_u64(7)))),
        reduced_values(&(<prover::Fp>::ONE))
    );
    assert_eq!(
        reduced_values(&(groups[2][1])),
        reduced_values(&(<prover::Fp>::ONE))
    );

    let capacity = scratch.capacity();
    let mut second = alloc::vec![alloc::vec![<prover::Fp>::from_u64(11)], Vec::new()];
    prover::products::batch_invert_groups(&mut second, &mut scratch);
    assert_eq!(
        reduced_values(&(second[0][0].mul(&<prover::Fp>::from_u64(11)))),
        reduced_values(&(<prover::Fp>::ONE))
    );
    assert_eq!(scratch.capacity(), capacity);

    for length in 0..=9u64 {
        let originals = (0..length)
            .map(|index| {
                if index % 3 == 1 {
                    <prover::Fp>::ZERO
                } else {
                    <prover::Fp>::from_u64(index + 2)
                }
            })
            .collect::<Vec<_>>();
        let midpoint = originals.len() / 2;
        let mut groups = alloc::vec![
            originals[..midpoint].to_vec(),
            Vec::new(),
            originals[midpoint..].to_vec(),
        ];
        prover::products::batch_invert_groups(&mut groups, &mut scratch);
        let inverted = groups.into_iter().flatten().collect::<Vec<_>>();
        for (original, inverse) in originals.iter().zip(inverted) {
            if original.is_zero() {
                assert!(inverse.is_zero());
            } else {
                assert_eq!(
                    reduced_values(&(original.mul(&inverse))),
                    reduced_values(&(<prover::Fp>::ONE))
                );
            }
        }
    }
}
