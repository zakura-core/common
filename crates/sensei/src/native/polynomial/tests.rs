use crate::native::test_support::reduced_values;

use udon::field::{PallasBase, PallasScalar, PastaField};
// Circuit polynomial identities and residue layout checks against Udon transforms.
use super::{
    EXTENDED_LOG_SIZE, FpCosetTiles, base_coefficients_to_extended_coset,
    base_lagrange_to_extended_coset, coset_fft, coset_fft_with_nonzero_prefix, coset_ifft,
    evaluate, quotient_numerator_to_coefficients, short_coefficients_times_factor_coset_tiles,
    synthetic_division, synthetic_division_in_place,
};
use crate::native::field::Fp;
use alloc::{sync::Arc, vec::Vec};

#[test]
fn horner_and_synthetic_division_are_consistent() {
    let polynomial: Vec<_> = [9u64, 4, 7, 2, 11]
        .into_iter()
        .map(<Fp>::from_u64)
        .collect();
    let point = <Fp>::from_u64(13);
    let expected = evaluate(&polynomial, &point);
    let (quotient, evaluation) = synthetic_division(&polynomial, &point);
    assert_eq!((evaluation).reduce(), (expected).reduce());

    for sample in 0..20 {
        let x = <Fp>::from_u64(sample);
        let reconstructed = evaluate(&quotient, &x).mul(&x.sub(&point)).add(&evaluation);
        assert_eq!(
            (reconstructed).reduce(),
            (evaluate(&polynomial, &x)).reduce()
        );
    }

    assert_eq!(
        reduced_values(&(synthetic_division::<crate::native::field::PallasBase>(&[], &point))),
        reduced_values(&(Vec::<Fp>::new(), <Fp>::ZERO))
    );
}

#[test]
fn in_place_synthetic_division_matches_allocating_division() {
    let point = <Fp>::from_u64(13);
    for length in 0..20 {
        let polynomial: Vec<_> = (0..length)
            .map(|index| <Fp>::from_u64(index * index * 17 + index * 3 + 9))
            .collect();
        let expected = synthetic_division(&polynomial, &point);
        let mut actual = polynomial;
        let evaluation = synthetic_division_in_place(&mut actual, &point);
        assert_eq!(
            reduced_values(&(actual, evaluation)),
            reduced_values(&(expected))
        );
    }
}

#[test]
fn sparse_vanishing_division_matches_pointwise_division() {
    let block_len = 4;
    let mut numerator: Vec<_> = (0..32)
        .map(|index| <Fp>::from_u64(index * index * 11 + index * 7 + 3))
        .collect();
    let actual = quotient_numerator_to_coefficients(numerator.clone(), block_len).unwrap();

    let root = <Fp>::root_of_unity(numerator.len().ilog2()).unwrap();
    let mut point = <Fp>::ZETA;
    for value in &mut numerator {
        let denominator = point.pow_u64(block_len as u64).sub(&<Fp>::ONE);
        *value = value.mul(&denominator.invert().unwrap());
        point = point.mul(&root);
    }
    assert!(coset_ifft(&mut numerator));
    assert_eq!(reduced_values(&(actual)), reduced_values(&(numerator)));
}

/// On each stride-8 sub-coset of the extended coset the
/// vanishing polynomial `Z_H = X^N − 1` is the constant `ζ^N·μ^r − 1`
/// with `μ = g^N` a primitive 8th root of unity, so dividing by `Z_H` is
/// one constant inverse per sub-coset. Pins that the per-sub-coset
/// scaling path and the telescope path
/// (`quotient_numerator_to_coefficients`) recover exactly the same
/// quotient.
#[test]
fn per_subcoset_vanishing_constants_match_the_telescope() {
    use crate::native::target::{EXTENDED_N, N};

    let target = crate::test_codec::target();
    let ratio = EXTENDED_N / N;
    let mu = target.domain().extended_omega().pow_u64(N as u64);
    assert_eq!((mu.pow_u64(ratio as u64)).reduce(), (<Fp>::ONE).reduce());
    assert_ne!(
        (mu.pow_u64(ratio as u64 / 2)).reduce(),
        (<Fp>::ONE).reduce()
    );

    let zeta_n = <Fp>::ZETA.pow_u64(N as u64);
    let divisors: Vec<Fp> = (0..ratio)
        .map(|residue| zeta_n.mul(&mu.pow_u64(residue as u64)).sub(&<Fp>::ONE))
        .collect();
    // The divisor is `Z_H` on the extended coset, constant along each
    // stride-8 sub-coset.
    let mut point = *target.domain().coset_generator();
    for row in 0..EXTENDED_N {
        assert_eq!(
            (point.pow_u64(N as u64).sub(&<Fp>::ONE)).reduce(),
            (divisors[row % ratio]).reduce()
        );
        point = point.mul(target.domain().extended_omega());
    }

    // A quotient at the §5.10.1 degree bound (a degree-9 term's quotient
    // has degree < 7N) round-trips exactly through both division paths.
    let mut quotient = alloc::vec![ <Fp>::ZERO; EXTENDED_N];
    for (index, value) in quotient[..7 * N].iter_mut().enumerate() {
        let index = index as u64;
        *value = <Fp>::from_u64(index * index * 31 + index * 5 + 11);
    }
    let mut numerator = quotient.clone();
    assert!(coset_fft(&mut numerator));
    for (row, value) in numerator.iter_mut().enumerate() {
        *value = value.mul(&divisors[row % ratio]);
    }

    let telescoped = quotient_numerator_to_coefficients(numerator.clone(), N).unwrap();
    assert_eq!(reduced_values(&(telescoped)), reduced_values(&(quotient)));

    let inverses = target.domain().vanishing_inverses();
    for (inverse, divisor) in inverses.iter().zip(&divisors) {
        assert!(inverse.mul(divisor).is_one());
    }
    for (row, value) in numerator.iter_mut().enumerate() {
        *value = value.mul(&inverses[row % ratio]);
    }
    assert!(coset_ifft(&mut numerator));
    assert_eq!(reduced_values(&(numerator)), reduced_values(&(quotient)));
}

/// `l_0 = Z_H/(N·(X−1))`, so a folded boundary term
/// `l_0·T` needs no extended-coset evaluation at all:
/// `l_0·T/Z_H = T/(N·(X−1))` — one synthetic division of coefficients,
/// whose remainder is the boundary constraint's value (exactly zero when
/// the constraint is satisfied).
#[test]
fn l_0_boundary_quotient_is_a_scaled_synthetic_division() {
    use crate::native::target::{EXTENDED_N, N};

    let target = crate::test_codec::target();
    let mut term: Vec<Fp> = (0..N)
        .map(|index| {
            let index = index as u64;
            <Fp>::from_u64(index * index * 13 + index * 7 + 5)
        })
        .collect();
    // Satisfy the boundary constraint: force T(1) = 0.
    let at_one = evaluate(&term, &<Fp>::ONE);
    term[0] = term[0].sub(&at_one);

    let term_extended = base_coefficients_to_extended_coset(&term).unwrap();
    let numerator: Vec<Fp> = term_extended
        .iter()
        .zip(target.boundaries().l_0())
        .map(|(value, boundary)| value.mul(boundary))
        .collect();
    let via_evaluation = quotient_numerator_to_coefficients(numerator, N).unwrap();

    let (mut via_division, remainder) = synthetic_division(&term, &<Fp>::ONE);
    assert!(remainder.is_zero());
    let scale = <Fp>::from_u64(N as u64).invert().unwrap();
    for coefficient in &mut via_division {
        *coefficient = coefficient.mul(&scale);
    }
    via_division.resize(EXTENDED_N, <Fp>::ZERO);
    assert_eq!(
        reduced_values(&(via_evaluation)),
        reduced_values(&(via_division))
    );
}

/// `l_last = (ω^u/N)·Z_H/(X−ω^u)` at the last usable row
/// `u`, so `l_last·T/Z_H = (ω^u/N)·T/(X−ω^u)` — the `l_last` analog of
/// the `l_0` synthetic-division identity, again with an exact-zero
/// remainder when the constraint holds at `ω^u`.
#[test]
fn l_last_boundary_quotient_is_a_scaled_synthetic_division() {
    use crate::native::target::{EXTENDED_N, N, USABLE_ROWS_END};

    let target = crate::test_codec::target();
    let point = target.domain().omega().pow_u64(USABLE_ROWS_END as u64);
    let mut term: Vec<Fp> = (0..N)
        .map(|index| {
            let index = index as u64;
            <Fp>::from_u64(index * index * 19 + index * 3 + 17)
        })
        .collect();
    // Satisfy the boundary constraint: force T(ω^u) = 0.
    let at_point = evaluate(&term, &point);
    term[0] = term[0].sub(&at_point);

    let term_extended = base_coefficients_to_extended_coset(&term).unwrap();
    let numerator: Vec<Fp> = term_extended
        .iter()
        .zip(target.boundaries().l_last())
        .map(|(value, boundary)| value.mul(boundary))
        .collect();
    let via_evaluation = quotient_numerator_to_coefficients(numerator, N).unwrap();

    let (mut via_division, remainder) = synthetic_division(&term, &point);
    assert!(remainder.is_zero());
    let scale = point.mul(&<Fp>::from_u64(N as u64).invert().unwrap());
    for coefficient in &mut via_division {
        *coefficient = coefficient.mul(&scale);
    }
    via_division.resize(EXTENDED_N, <Fp>::ZERO);
    assert_eq!(
        reduced_values(&(via_evaluation)),
        reduced_values(&(via_division))
    );
}

/// The residue-major coset record reads exactly the dense coset: every row
/// through the record and its borrowed view, including the rotated rows that
/// wrap at the domain end, at arbitrary field values; and its storage order
/// is residue-major (tile `s` = rows `s + 8k`).
#[test]
fn tiled_coset_record_reads_match_the_dense_coset() {
    use super::{EXTENDED_TILE_COUNT, EXTENDED_TILE_LEN, ExtendedCosetView};

    let base_size = 1usize << super::BASE_LOG_SIZE;
    let extended_size = 1usize << EXTENDED_LOG_SIZE;
    let coefficients: Vec<Fp> = (0..base_size)
        .map(|index| {
            let index = index as u64;
            <Fp>::from_u64(index.wrapping_mul(index ^ 0x9e37_79b9) ^ (index << 40) ^ 11)
                .mul(&<Fp>::ZETA)
        })
        .collect();
    // The dense oracle: zero-pad and run the reference coset FFT.
    let mut dense = coefficients.clone();
    dense.resize_with(extended_size, || <Fp>::ZERO);
    assert!(coset_fft_with_nonzero_prefix(&mut dense, base_size));
    assert_eq!(
        reduced_values(&(base_coefficients_to_extended_coset(&coefficients).unwrap())),
        reduced_values(&(dense))
    );
    let tiles = super::base_coefficients_to_extended_coset_tiles(&coefficients).unwrap();
    let view = tiles.view();
    for row in 0..extended_size {
        assert_eq!((tiles[row]).reduce(), (dense[row]).reduce());
        assert_eq!((view[row]).reduce(), (dense[row]).reduce());
    }
    // Rotations by whole base rows and by the blinding tail wrap modulo 8N
    // and stay inside the row's residue.
    for row in [
        0usize,
        7,
        EXTENDED_TILE_LEN - 1,
        EXTENDED_TILE_LEN,
        extended_size - 8,
    ] {
        for rotation in [-48i64, -8, 8, 48] {
            let rotated = (row as i64 + rotation).rem_euclid(extended_size as i64) as usize;
            assert_eq!(rotated % 8, row % 8);
            assert_eq!((view[rotated]).reduce(), (dense[rotated]).reduce());
        }
    }
    // Storage is residue-major: the flat form lists residue 0, then 1, ...
    let flat = tiles.to_dense_rows();
    assert_eq!(reduced_values(&(flat)), reduced_values(&(dense)));
    let dense_rows = dense.as_slice();
    let residue_major: Vec<Fp> = (0..EXTENDED_TILE_COUNT)
        .flat_map(|residue| (0..EXTENDED_TILE_LEN).map(move |k| dense_rows[residue + 8 * k]))
        .collect();
    assert!(
        tiles
            .iter()
            .map(reduced_values)
            .eq(residue_major.iter().map(reduced_values))
    );
    let flat_view = ExtendedCosetView::from_flat(residue_major.as_slice()).unwrap();
    assert!((0..extended_size).all(|row| (flat_view[row]).reduce() == (dense[row]).reduce()));
    assert!(ExtendedCosetView::from_flat(&residue_major[..extended_size - 1]).is_none());
    assert_eq!(
        reduced_values(&(tiles.into_flat())),
        reduced_values(&(residue_major))
    );
    assert_eq!(
        reduced_values(
            &(super::ExtendedCosetTiles::<PallasBase>::from_dense_rows(&dense)
                .unwrap()
                .into_flat())
        ),
        reduced_values(&(residue_major))
    );

    // Residue-major chunks of any shape assemble into the same record;
    // whole-tile chunks are adopted, smaller and larger ones split and joined.
    for chunk_rows in [
        EXTENDED_TILE_LEN,
        EXTENDED_TILE_LEN / 2,
        683,
        EXTENDED_TILE_LEN * 3,
        extended_size,
    ] {
        let assembled = super::ExtendedCosetTiles::from_row_chunks(
            residue_major.chunks(chunk_rows).map(|tile| tile.to_vec()),
        )
        .unwrap();
        assert!((0..extended_size).all(|row| (assembled[row]).reduce() == (dense[row]).reduce()));
    }
    assert_eq!(
        reduced_values(
            &(super::ExtendedCosetTiles::from_flat(residue_major.clone())
                .unwrap()
                .into_flat())
        ),
        reduced_values(&(residue_major))
    );
    // Short, long, and misaligned totals are refused.
    assert!(
        super::ExtendedCosetTiles::from_row_chunks([residue_major[..extended_size - 1].to_vec()])
            .is_none()
    );
    assert!(
        super::ExtendedCosetTiles::from_row_chunks([residue_major.clone(), alloc::vec![<Fp>::ONE]])
            .is_none()
    );
    assert!(
        super::ExtendedCosetTiles::from_row_chunks(
            (0..=EXTENDED_TILE_COUNT).map(|_| alloc::vec![ <Fp>::ONE; EXTENDED_TILE_LEN])
        )
        .is_none()
    );
    assert!(
        super::ExtendedCosetTiles::<PallasBase>::from_flat(alloc::vec![ <Fp>::ONE; base_size])
            .is_none()
    );
    // The Lagrange-form producer agrees with its dense reference too.
    let lagrange: Vec<Fp> = (0..base_size)
        .map(|index| <Fp>::from_u64((index as u64) * 7 + 3))
        .collect();
    let mut dense_lagrange = lagrange.clone();
    assert!(base_lagrange_to_extended_coset(&mut dense_lagrange));
    let lagrange_tiles = super::base_lagrange_to_extended_coset_tiles(&lagrange).unwrap();
    assert!(
        (0..extended_size)
            .all(|row| (lagrange_tiles[row]).reduce() == (dense_lagrange[row]).reduce())
    );
}

/// The 2N class coset record is exactly the extended coset's stride-4 rows
/// (`Ω^4` is the 2N-th root): residues 0 and 4, read at extended rows
/// through the record and its view, including the `+8` rotation wrapping at
/// the domain end.
#[test]
fn class_2n_coset_is_the_extended_coset_stride_4_rows() {
    let base_size = 1usize << super::BASE_LOG_SIZE;
    let extended_size = 1usize << EXTENDED_LOG_SIZE;
    let coefficients: Vec<Fp> = (0..base_size)
        .map(|index| {
            let index = index as u64;
            <Fp>::from_u64(index.wrapping_mul(index ^ 0x5851_f42d) ^ (index << 37) ^ 23)
                .mul(&<Fp>::ZETA_INVERSE)
        })
        .collect();
    let dense = base_coefficients_to_extended_coset(&coefficients).unwrap();
    let class = super::base_coefficients_to_class_2n_coset_tiles(&coefficients).unwrap();
    let view = class.view();
    assert_eq!(class.iter().count(), extended_size / 4);
    for row in (0..extended_size).step_by(4) {
        assert_eq!((class[row]).reduce(), (dense[row]).reduce());
        assert_eq!((view[row]).reduce(), (dense[row]).reduce());
        assert_eq!((view.at_extended_row(row)).reduce(), (dense[row]).reduce());
        let next = (row + 8) % extended_size;
        assert_eq!(
            (view.at_extended_row(next)).reduce(),
            (dense[next]).reduce()
        );
    }
    let stride_4: Vec<Fp> = (0..extended_size)
        .step_by(4)
        .map(|row| dense[row])
        .collect();
    assert_eq!(
        reduced_values(&(class.to_dense_rows())),
        reduced_values(&(stride_4))
    );
    assert_eq!(
        reduced_values(
            &(super::FpClass2NTiles::from_dense_rows(&stride_4)
                .unwrap()
                .into_flat())
        ),
        reduced_values(&(class.into_flat()))
    );
    assert!(
        super::base_coefficients_to_class_2n_coset_tiles(&coefficients[..base_size - 1]).is_none()
    );
    let scalar: Vec<PastaField<PallasScalar>> = (0..base_size)
        .map(|index| PastaField::from_u64(index as u64 + 1))
        .collect();
    // The scalar field caches the extended metadata too, so its residue
    // transforms are available for both records.
    assert!(super::base_coefficients_to_class_2n_coset_tiles(&scalar).is_some());
}

/// The pruned short-support product transform equals the dense coset
/// evaluation of the zero-padded polynomial times the factor, for every
/// support width class (one coefficient through the full base domain),
/// including interior zero coefficients, and refuses empty or oversized
/// supports.
#[test]
fn short_support_product_matches_dense_coset_product() {
    let base_size = 1usize << super::BASE_LOG_SIZE;
    let extended_size = 1usize << EXTENDED_LOG_SIZE;
    let element = |index: usize, salt: u64| {
        let index = index as u64;
        <Fp>::from_u64(index.wrapping_mul(index ^ salt) ^ (index << 37) ^ 3)
            .mul(&<Fp>::ZETA)
            .square()
            .sub(&<Fp>::from_u64(salt))
    };
    let factor_dense: Vec<Fp> = (0..extended_size)
        .map(|row| element(row, 0x9e37_79b9))
        .collect();
    let factor = Arc::new(FpCosetTiles::from_dense_rows(&factor_dense).unwrap());
    let zeta = <Fp>::ZETA;
    let extended_omega = <Fp>::root_of_unity(EXTENDED_LOG_SIZE).unwrap();
    for (length, zero_stride) in [
        (1, 0),
        (2, 0),
        (3, 0),
        (4, 0),
        (5, 2),
        (9, 0),
        (10, 0),
        (10, 2),
        (10, 3),
        (11, 0),
        (16, 0),
        (17, 0),
        (100, 7),
        (128, 0),
        (129, 0),
        (base_size / 2, 0),
        (base_size - 1, 0),
        (base_size, 5),
    ] {
        let short: Vec<Fp> = (0..length)
            .map(|index| {
                if zero_stride != 0 && index % zero_stride == 0 {
                    <Fp>::ZERO
                } else {
                    element(index, length as u64)
                }
            })
            .collect();
        let mut dense = short.clone();
        dense.resize(base_size, <Fp>::ZERO);
        let expected: Vec<Fp> = base_coefficients_to_extended_coset(&dense)
            .unwrap()
            .iter()
            .zip(&factor_dense)
            .map(|(value, factor)| value.mul(factor))
            .collect();
        let tiles =
            short_coefficients_times_factor_coset_tiles(&short, Arc::clone(&factor)).unwrap();
        assert_eq!(
            reduced_values(&(tiles.to_dense_rows())),
            reduced_values(&(expected)),
            "{length} coefficients, zero stride {zero_stride}"
        );
        // Direct evaluation at `ζ Ω^r`, independent of every transform.
        for row in [
            0usize,
            1,
            7,
            8,
            9,
            4095,
            extended_size - 9,
            extended_size - 1,
        ] {
            let point = zeta.mul(&extended_omega.pow_u64(row as u64));
            assert_eq!(
                (tiles[row]).reduce(),
                (evaluate(&short, &point).mul(&factor_dense[row])).reduce(),
                "{length} coefficients, row {row}"
            );
        }
    }
    let zeros = alloc::vec![ <Fp>::ZERO; 10];
    let tiles = short_coefficients_times_factor_coset_tiles(&zeros, Arc::clone(&factor)).unwrap();
    assert!(tiles.iter().all(<Fp>::is_zero));
    assert!(
        short_coefficients_times_factor_coset_tiles::<PallasBase>(&[], Arc::clone(&factor))
            .is_none()
    );
    assert!(
        short_coefficients_times_factor_coset_tiles(
            &alloc::vec![ <Fp>::ONE; base_size + 1],
            factor
        )
        .is_none()
    );
}
/// Every source policy binds the same transforms. In embedded mode the
/// runtime must keep slices of the artifact, without a table-sized allocation.
#[test]
fn prepared_fft_storage_and_transforms_match_unprepared_plans() {
    use super::{PreparedFft, TableValues};
    use crate::tuning::{self, OptionalPreparation};
    use sensei_shared::fft as layout;
    use udon::exec::{ExecutionOptions, SerialExecutor};

    fn check_storage(values: &TableValues, mode: OptionalPreparation, len: usize) {
        match (mode, values) {
            (OptionalPreparation::OnDemand, TableValues::Absent) => {}
            (OptionalPreparation::WarmUp, TableValues::Owned(values)) => {
                assert_eq!(values.len(), len);
                assert_eq!(values.capacity(), len);
            }
            #[cfg(any(embed_fft_tables, embed_expansion_scales))]
            (OptionalPreparation::Embed, TableValues::Embedded(values)) => {
                assert_eq!(values.len(), len);
            }
            _ => panic!("prepared table storage disagrees with the selected policy"),
        }
    }

    let prepared = PreparedFft::new();
    for (index, tables) in core::iter::once(&prepared.base)
        .chain(&prepared.cosets)
        .enumerate()
    {
        let len = layout::plan_size(index);
        check_storage(&tables.values, tuning::FFT_TABLES, 3 * len / 2);
        #[cfg(embed_fft_tables)]
        assert!(core::ptr::eq(
            tables.values.values().unwrap(),
            &super::FFT_TABLES
                [layout::table_offset(index)..layout::table_offset(index) + 3 * len / 2]
        ));
        let values: Vec<_> = (0..len)
            .map(|i| <Fp>::from_u64((i * i + 11) as u64))
            .collect();
        let mut actual = values.clone();
        let mut reference = values.clone();
        let plain = udon::fft::Tables::default().bind(tables.domain);
        plain
            .forward(
                &mut reference,
                ExecutionOptions::default(),
                &SerialExecutor,
                &mut [],
            )
            .unwrap();
        tables
            .plan()
            .forward(
                &mut actual,
                ExecutionOptions::default(),
                &SerialExecutor,
                &mut [],
            )
            .unwrap();
        assert_eq!(reduced_values(&actual), reduced_values(&reference));
        tables
            .plan()
            .inverse(
                &mut actual,
                ExecutionOptions::default(),
                &SerialExecutor,
                &mut [],
            )
            .unwrap();
        assert_eq!(reduced_values(&actual), reduced_values(&values));
    }
    for (index, scales) in prepared.residue_scales.iter().enumerate() {
        let len = sensei_shared::N << index;
        check_storage(scales, tuning::EXPANSION_SCALES, len);
        #[cfg(embed_expansion_scales)]
        assert!(core::ptr::eq(
            scales.values().unwrap(),
            &super::EXPANSION_SCALES
                [layout::scale_offset(index)..layout::scale_offset(index) + len]
        ));
        let coefficients: Vec<_> = (0..sensei_shared::N)
            .map(|i| <Fp>::from_u64((i * 17 + 3) as u64))
            .collect();
        let mut actual = vec![<Fp>::ZERO; len];
        let mut reference = actual.clone();
        let options = ExecutionOptions::default();
        super::expansion(1 << index)
            .unwrap()
            .coefficients(
                &coefficients,
                &mut reference,
                options,
                &SerialExecutor,
                &mut [],
            )
            .unwrap();
        prepared
            .expansion(1 << index)
            .unwrap()
            .coefficients(
                &coefficients,
                &mut actual,
                options,
                &SerialExecutor,
                &mut [],
            )
            .unwrap();
        assert_eq!(reduced_values(&actual), reduced_values(&reference));
    }
}
