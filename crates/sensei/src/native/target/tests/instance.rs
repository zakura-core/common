//! Instance interpolation, boundary transforms, and direct domain-vector oracles.

use crate::native::test_support::reduced_values;

use alloc::vec::Vec;

use crate::native::field::Fp;
use crate::native::polynomial::{
    FpCosetTiles, base_lagrange_to_extended_coset, coset_ifft, evaluate as evaluate_polynomial,
    fft, ifft,
};

use super::super::{
    BLINDING_FACTORS, EXTENDED_N, INSTANCE_VALUE_COUNT, K, N, TargetError, boundary_polynomial,
};

/// The embedded instance bases are exactly the load-time derivation —
/// both settings of the dial produce the same field values.
#[cfg(embed_instance_bases)]
#[test]
fn embedded_instance_bases_match_derivation() {
    let derived = super::super::PreparedInstance::derive().unwrap();
    assert_eq!(
        reduced_values(derived.coefficients.rows()),
        reduced_values(super::super::INSTANCE_BASES)
    );
}

#[test]
fn instance_progressions_match_unit_vector_inverse_transforms() {
    let instance = super::super::PreparedInstance::derive().unwrap();
    for basis in 0..INSTANCE_VALUE_COUNT {
        let mut reference = alloc::vec![<Fp>::ZERO; N];
        reference[basis] = <Fp>::ONE;
        assert!(ifft(&mut reference));
        for (row, value) in instance.coefficients.rows().iter().zip(reference) {
            assert_eq!(row[basis].reduce(), value.reduce(), "basis {basis}");
        }
    }
}

#[test]
fn derived_boundaries_match_indicator_transforms() {
    let derived = super::super::Boundaries::derive().unwrap();
    for (values, rows) in [
        (derived.l_0(), vec![0]),
        (derived.l_last(), vec![super::super::USABLE_ROWS_END]),
        (
            derived.active_rows(),
            (0..super::super::USABLE_ROWS_END).collect(),
        ),
    ] {
        assert_eq!(
            reduced_values(values),
            reduced_values(&boundary_polynomial(rows).unwrap()),
        );
    }
}

/// The embedded boundary polynomials are exactly the load-time
/// transforms — both settings of the dial produce the same field values.
#[cfg(embed_boundaries)]
#[test]
fn embedded_boundaries_match_derivation() {
    let derived = super::super::Boundaries::derive().unwrap();
    let embedded = super::super::BOUNDARY_POLYNOMIALS;
    assert_eq!(reduced_values(derived.l_0()), reduced_values(&embedded[0]));
    assert_eq!(
        reduced_values(derived.l_last()),
        reduced_values(&embedded[1])
    );
    assert_eq!(
        reduced_values(derived.active_rows()),
        reduced_values(&embedded[2])
    );
}

#[test]
fn common_target_polynomial_vectors_match_direct_definitions() {
    let target = crate::test_codec::target();
    let boundaries = target.boundaries();
    let l_blind = boundary_polynomial((N - BLINDING_FACTORS)..N).unwrap();
    for (((last, blind), active), row) in boundaries
        .l_last()
        .iter()
        .zip(&l_blind)
        .zip(boundaries.active_rows())
        .zip(0..EXTENDED_N)
    {
        assert_eq!(
            (*active).reduce(),
            (<Fp>::ONE.sub(&last.add(blind))).reduce(),
            "active-row mask differs at row {row}"
        );
    }

    let identities = target.permutation_identities();
    let mut delta_power = <Fp>::ONE;
    for (column_index, (values, delta)) in identities
        .values()
        .iter()
        .zip(identities.deltas())
        .enumerate()
    {
        assert_eq!(
            (*delta).reduce(),
            (delta_power).reduce(),
            "delta differs at column {column_index}"
        );
        let mut ordinary_point = delta_power;
        for (row, value) in values.iter().enumerate() {
            assert_eq!(
                (*value).reduce(),
                (ordinary_point).reduce(),
                "ordinary identity differs at column {column_index}, row {row}"
            );
            ordinary_point = ordinary_point.mul(target.domain().omega());
        }
        delta_power = delta_power.mul(target.domain().permutation_delta());
    }
}

/// Deterministic full-width field elements for the arbitrary-input oracles.
fn arbitrary_instance_prefix(seed: u64) -> Vec<Fp> {
    let step = <Fp>::root_of_unity(K).unwrap().add(&<Fp>::ZETA);
    let mut value = <Fp>::from_u64(seed | 1).pow_u64(u64::MAX - seed);
    (0..INSTANCE_VALUE_COUNT)
        .map(|_| {
            value = value.mul(&step).square().add(&<Fp>::from_u64(seed));
            value
        })
        .collect()
}

/// The prepared instance forms equal the dense oracle — the zero-padded
/// prefix's inverse transform and its dense coset transform — for every basis
/// vector, the zero prefix, small and full-width arbitrary prefixes, and a
/// prefix with interior zeros: full coefficient vectors, the residue-major
/// record, and rotated row reads; other prefix lengths are dimension errors.
#[test]
fn prepared_instance_forms_match_dense_transforms() {
    let target = crate::test_codec::target();
    let instance = target.prepared_instance();
    let mut inputs = alloc::vec![alloc::vec![ <Fp>::ZERO; INSTANCE_VALUE_COUNT]];
    inputs.reserve_exact(INSTANCE_VALUE_COUNT + 4);
    for row in 0..INSTANCE_VALUE_COUNT {
        let mut basis = alloc::vec![ <Fp>::ZERO; INSTANCE_VALUE_COUNT];
        basis[row] = <Fp>::ONE;
        inputs.push(basis);
    }
    inputs.push(
        (0..INSTANCE_VALUE_COUNT)
            .map(|index| <Fp>::from_u64((index * index * 13 + index * 7 + 3) as u64))
            .collect(),
    );
    inputs.push(arbitrary_instance_prefix(0x5eed));
    inputs.push(arbitrary_instance_prefix(0xa11ce));
    let mut sparse = arbitrary_instance_prefix(7);
    for value in sparse.iter_mut().step_by(2) {
        *value = <Fp>::ZERO;
    }
    inputs.push(sparse);

    for prefix in &inputs {
        let coset = instance
            .coset(
                prefix,
                crate::test_codec::target().fft(),
                crate::test_codec::execution(),
            )
            .unwrap();
        let coefficients: Vec<_> = instance
            .coefficient_rows()
            .iter()
            .map(|row| Fp::sum_of_products(row, prefix.as_slice().try_into().unwrap()))
            .collect();
        let mut dense = prefix.clone();
        dense.resize(N, <Fp>::ZERO);
        let mut expected_coefficients = dense.clone();
        assert!(ifft(&mut expected_coefficients));
        assert!(base_lagrange_to_extended_coset(&mut dense));
        assert_eq!(
            reduced_values(&(coefficients)),
            reduced_values(&(expected_coefficients))
        );
        // Sparse evaluations use domain-aware Lagrange weights, including
        // populated and zero-tail nodes where rational formulas have poles.
        for point in [Fp::ZERO, Fp::from_u64(7), <Fp>::from_u64(1234567).square()]
            .into_iter()
            .chain(
                (0..=INSTANCE_VALUE_COUNT)
                    .chain([N - 1])
                    .map(|row| target.domain().omega().pow_u64(row as u64)),
            )
        {
            let weights = instance.evaluation_weights(&point).unwrap();
            let actual = Fp::sum_of_products(&weights, prefix.as_slice().try_into().unwrap());
            let expected = expected_coefficients
                .iter()
                .rev()
                .fold(Fp::ZERO, |acc, value| acc.mul_add(&point, value));
            assert_eq!(actual.reduce(), expected.reduce());
        }
        assert_eq!(
            reduced_values(&(coset.to_dense_rows())),
            reduced_values(&(dense))
        );
        let expected_tiles = FpCosetTiles::from_dense_rows(&dense).unwrap();
        assert!(
            coset
                .iter()
                .map(reduced_values)
                .eq(expected_tiles.iter().map(reduced_values))
        );
        let view = coset.view();
        for row in [
            0,
            1,
            7,
            8,
            9,
            N - 1,
            N,
            EXTENDED_N / 2 + 3,
            EXTENDED_N - 8 * (BLINDING_FACTORS + 1),
            EXTENDED_N - 9,
            EXTENDED_N - 1,
        ] {
            let next = (row + 8) % EXTENDED_N;
            let previous = (row + EXTENDED_N - 8) % EXTENDED_N;
            let tail = (row + EXTENDED_N - 8 * (BLINDING_FACTORS + 1)) % EXTENDED_N;
            assert_eq!((view.at_extended_row(row)).reduce(), (dense[row]).reduce());
            assert_eq!((coset[next]).reduce(), (dense[next]).reduce());
            assert_eq!((view[previous]).reduce(), (dense[previous]).reduce());
            assert_eq!((view[tail]).reduce(), (dense[tail]).reduce());
        }
    }

    for length in [0, INSTANCE_VALUE_COUNT - 1, INSTANCE_VALUE_COUNT + 1, N] {
        assert!(matches!(
            instance.coset(
                &alloc::vec![ <Fp>::ONE; length],
                crate::test_codec::target().fft(),
                crate::test_codec::execution()
            ),
            Err(TargetError::Dimension)
        ));
    }
}

/// The fixed-support factorization behind the instance coset, checked
/// independently of the prepared map: the support coset is `(x^N − 1) / H(x)`
/// at every extended-coset point; its interpolated coefficients are monic of
/// degree `N − m`, vanish on every unpopulated row and take the derivative
/// value `N ω^{−j} / ∏_{i≠j} (ω^j − ω^i)` on the populated ones; and for
/// arbitrary prefixes the dense coefficients divide exactly by `S` with a
/// degree-below-`m` quotient equal to the map's output, whose product with
/// `S` reproduces the dense coset row by row.
#[test]
fn instance_support_factorization_matches_dense_interpolation() {
    let target = crate::test_codec::target();
    let instance = target.prepared_instance();
    let omega = <Fp>::root_of_unity(K).unwrap();
    let extended_omega = <Fp>::root_of_unity(sensei_shared::EXTENDED_K).unwrap();
    let zeta = <Fp>::ZETA;
    let supported: Vec<Fp> = (0..INSTANCE_VALUE_COUNT)
        .map(|row| omega.pow_u64(row as u64))
        .collect();

    let support = instance.support.to_dense_rows();
    assert_eq!(support.len(), EXTENDED_N);
    let mut point = zeta;
    for (row, value) in support.iter().enumerate() {
        let numerator = point.pow_u64(N as u64).sub(&<Fp>::ONE);
        let denominator = supported
            .iter()
            .fold(<Fp>::ONE, |product, root| product.mul(&point.sub(root)));
        assert_eq!(
            (*value).reduce(),
            (numerator.mul(&denominator.invert().unwrap())).reduce(),
            "row {row}"
        );
        point = point.mul(&extended_omega);
    }

    let mut support_coefficients = support.clone();
    assert!(coset_ifft(&mut support_coefficients));
    assert!(
        support_coefficients[N - INSTANCE_VALUE_COUNT + 1..]
            .iter()
            .all(<Fp>::is_zero)
    );
    assert_eq!(
        (support_coefficients[N - INSTANCE_VALUE_COUNT]).reduce(),
        (<Fp>::ONE).reduce()
    );
    support_coefficients.truncate(N);
    let mut support_on_rows = support_coefficients.clone();
    assert!(fft(&mut support_on_rows));
    for (row, value) in support_on_rows.iter().enumerate() {
        if row < INSTANCE_VALUE_COUNT {
            let root = supported[row];
            let mut expected = <Fp>::from_u64(N as u64).mul(&root.invert().unwrap());
            for (other_row, other) in supported.iter().enumerate() {
                if other_row != row {
                    expected = expected.mul(&root.sub(other).invert().unwrap());
                }
            }
            assert_eq!((*value).reduce(), (expected).reduce(), "row {row}");
        } else {
            assert!(value.is_zero(), "row {row}");
        }
    }

    let mut basis = alloc::vec![ <Fp>::ZERO; INSTANCE_VALUE_COUNT];
    basis[3] = <Fp>::ONE;
    for prefix in [
        arbitrary_instance_prefix(1),
        arbitrary_instance_prefix(2),
        basis,
        alloc::vec![ <Fp>::ZERO; INSTANCE_VALUE_COUNT],
    ] {
        let mut dense = prefix.clone();
        dense.resize(N, <Fp>::ZERO);
        let mut coefficients = dense.clone();
        assert!(ifft(&mut coefficients));
        assert!(base_lagrange_to_extended_coset(&mut dense));

        let mut remainder = coefficients;
        let mut quotient = alloc::vec![ <Fp>::ZERO; INSTANCE_VALUE_COUNT];
        for degree in (0..INSTANCE_VALUE_COUNT).rev() {
            let lead = remainder[degree + N - INSTANCE_VALUE_COUNT];
            quotient[degree] = lead;
            for (offset, divisor) in support_coefficients[..=N - INSTANCE_VALUE_COUNT]
                .iter()
                .enumerate()
            {
                remainder[degree + offset] = remainder[degree + offset].sub(&lead.mul(divisor));
            }
        }
        assert!(remainder.iter().all(<Fp>::is_zero));

        let values: &[Fp; INSTANCE_VALUE_COUNT] = prefix.as_slice().try_into().unwrap();
        let mapped: Vec<Fp> = instance
            .interpolation
            .iter()
            .map(|row| <Fp>::sum_of_products(row, values))
            .collect();
        assert_eq!(reduced_values(&(mapped)), reduced_values(&(quotient)));

        let mut point = zeta;
        for row in 0..EXTENDED_N {
            assert_eq!(
                (support[row].mul(&evaluate_polynomial(&quotient, &point))).reduce(),
                (dense[row]).reduce(),
                "row {row}"
            );
            point = point.mul(&extended_omega);
        }
    }
}
