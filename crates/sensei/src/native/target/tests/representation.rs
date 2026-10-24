//! Stored field/point bounds, canonical round trips, and preparation agreement.

use sensei_shared::INSTANCE_COLUMNS;
use sha2::{Digest, Sha256};

use crate::native::curve::{PallasPoint, PreparedAffinePoint, Vesta, VestaPoint};
use crate::native::field::{Fp, Fq};
use crate::native::srs::PREPARED_POINTS;
use crate::static_data::{bytes_of, bytes_of_slice};

use super::super::commitments::prepare_lagrange_prefix_sums;
use super::super::{ADVICE_COLUMNS, EXTENDED_N, FIXED_COLUMNS, FIXED_TUPLES, N};

/// Checks the stored representation's bound and canonical encoding round trip.
fn assert_valid_base<S: udon::field::ReductionState>(value: &Fp<S>) {
    let checked = Fp::<S>::from_montgomery_limbs(value.montgomery_limbs());
    assert_eq!(
        <Fp>::from_bytes(value.to_bytes()).map(|decoded| decoded.reduce()),
        Some(checked.reduce())
    );
}

fn assert_valid_scalar<S: udon::field::ReductionState>(value: &Fq<S>) {
    let checked = Fq::<S>::from_montgomery_limbs(value.montgomery_limbs());
    assert_eq!(
        <Fq>::from_bytes(value.to_bytes()).map(|decoded| decoded.reduce()),
        Some(checked.reduce())
    );
}

/// Asserts one embedded prepared MSM base is exactly the preparation of
/// its own canonical, on-curve, nonidentity affine point.
fn assert_prepared_vesta_base(base: &PreparedAffinePoint<Vesta>) {
    let affine = base.to_affine();
    let (x, y) = affine.coordinates();
    assert_valid_scalar(x);
    assert_valid_scalar(y);
    let decoded = VestaPoint::from_xy(*x, *y).expect("embedded base is on the curve");
    assert_eq!(decoded.as_affine(), Some(&affine));
    assert_eq!(
        bytes_of(base),
        bytes_of(&PreparedAffinePoint::from_affine(&affine)),
        "embedded base differs from the preparation of its affine point"
    );
}

/// The embedded window tables are exactly the shared `sensei-shared`
/// construction — the same code the prover runs at load when the artifact
/// is disabled — so both settings of the dial produce identical prepared
/// state. The embedded fixed values' `z` column must in turn agree with
/// the pinned per-base `z` tables both constructions now source.
#[cfg(embed_window_tables)]
#[test]
fn embedded_window_tables_match_shared_construction() {
    let recomputed = sensei_shared::fixed_bases::build_fixed_base_window_tables().unwrap();
    assert_eq!(
        bytes_of_slice(&recomputed),
        bytes_of(super::super::WINDOW_TABLES)
    );

    let target = crate::test_codec::target();
    let fixed_z = &target.fixed_values()[sensei_shared::fixed_bases::FIXED_BASE_Z_COLUMN];
    for (region, base, window_count) in sensei_shared::fixed_bases::FIXED_BASE_REGIONS {
        let start = sensei_shared::regions::REGION_STARTS[region];
        for (window, z) in base.z_column()[..window_count].iter().enumerate() {
            assert_eq!(
                (fixed_z[start + window]).reduce(),
                (<Fp>::from_u64(*z)).reduce()
            );
        }
    }
}

#[test]
fn embedded_prepared_data_is_strict_and_canonical() {
    let target = crate::test_codec::target();
    assert_eq!(target.parameters().coefficient_generators().len(), N);
    assert_eq!(target.parameters.srs.lagrange_generators.len(), N);
    assert!(
        VestaPoint::from_bytes(target.parameters().blind_generator().to_bytes())
            .unwrap()
            .as_affine()
            .is_some()
    );
    assert!(
        VestaPoint::from_bytes(target.parameters().ipa_generator().to_bytes())
            .unwrap()
            .as_affine()
            .is_some()
    );
    assert_eq!(target.fixed_values().len(), FIXED_COLUMNS);
    assert_eq!(
        target.permutation_columns().len(),
        target.sigma_values().len()
    );
    assert!(target.fixed_values().iter().all(|column| column.len() == N));
    // Existing fixed-column content pin: columns reconstructed from Sinsemilla
    // points, sparse fixed tuples/assignments, and the shared structured layout;
    // canonical little-endian field encodings in column/row order, not POD bytes.
    let mut fixed_value_digest = Sha256::new();
    for value in target.fixed_values().iter().flatten() {
        fixed_value_digest.update(value.to_bytes());
    }
    assert_eq!(
        hex::encode(fixed_value_digest.finalize()),
        "464fbdf4c3373a7bfc2d27b0d22c78109b3664b642a4f1706a61d5fd4e9862e7"
    );
    assert!(target.sigma_values().iter().all(|column| column.len() == N));
    assert!(
        target
            .queries()
            .advice()
            .iter()
            .all(|query| query.column < ADVICE_COLUMNS)
    );
    assert!(
        target
            .queries()
            .fixed()
            .iter()
            .all(|query| query.column < FIXED_COLUMNS)
    );
    assert!(
        target
            .queries()
            .instance()
            .iter()
            .all(|query| query.column < INSTANCE_COLUMNS)
    );
    assert!(!target.gates().is_empty());
    assert!(target.gates().iter().all(|range| !range.is_empty()));
    assert!(!target.lookups().is_empty());
    assert!(target.lookups().iter().all(|lookup| {
        !lookup.inputs().is_empty() && lookup.inputs().len() == lookup.tables().len()
    }));
    assert_eq!(
        (target.domain().omega()).reduce(),
        <Fp>::root_of_unity(11).unwrap().reduce()
    );
    assert_eq!(
        (target.domain().omega_inverse()).reduce(),
        target.domain().omega().invert().unwrap().reduce()
    );
    assert_eq!(
        (target.domain().extended_omega()).reduce(),
        <Fp>::root_of_unity(14).unwrap().reduce()
    );
    assert_eq!(
        (target.domain().coset_generator()).reduce(),
        <Fp>::ZETA.reduce()
    );
    assert_eq!(
        (target.domain().permutation_delta()).reduce(),
        <Fp>::from_u64(5).pow_u64(1 << 32).reduce()
    );
    assert_eq!(target.boundaries().l_0().len(), EXTENDED_N);
    assert_eq!(target.boundaries().l_last().len(), EXTENDED_N);
    assert_eq!(target.boundaries().active_rows().len(), EXTENDED_N);
    assert_eq!(
        target.permutation_identities().values().len(),
        target.permutation_columns().len()
    );
    assert_eq!(
        target.permutation_identities().deltas().len(),
        target.permutation_columns().len()
    );
}

/// Performs the validation the production loader deliberately omits for
/// the embedded point data: every stored coordinate is a canonical
/// Montgomery residue, every point is on its curve and nonidentity, every
/// prepared MSM base is exactly the preparation of its affine point, the
/// prefix-sum table is exactly the telescoped Lagrange construction, and
/// the recompressed point sets match their historical digests.
#[test]
fn embedded_point_data_is_pinned_and_on_curve() {
    let points = PREPARED_POINTS;

    for base in points
        .coefficient_bases
        .iter()
        .chain(&points.lagrange_bases)
        .chain(&points.lagrange_prefix_sums)
    {
        assert_prepared_vesta_base(&PreparedAffinePoint::from_affine(base));
    }
    for point in [&points.blind_generator, &points.ipa_generator] {
        let (x, y) = point.coordinates();
        assert_valid_scalar(x);
        assert_valid_scalar(y);
        let decoded = VestaPoint::from_xy(*x, *y).unwrap();
        assert_eq!(decoded.as_affine(), Some(point));
    }
    for point in crate::primitives::tables::sinsemilla_generators() {
        let (x, y) = point.coordinates();
        assert_valid_base(x);
        assert_valid_base(y);
        let decoded = PallasPoint::from_xy(*x, *y).unwrap();
        assert_eq!(decoded.as_affine(), Some(point));
    }

    // The embedded prefix-sum table is the telescoped construction over
    // the embedded Lagrange generators, byte for byte.
    let lagrange_affine_points = points.lagrange_bases.to_vec();
    let recomputed = prepare_lagrange_prefix_sums(&lagrange_affine_points)
        .expect("the pinned SRS has no identity prefix sum");
    assert_eq!(
        bytes_of_slice(&recomputed),
        bytes_of(&points.lagrange_prefix_sums)
    );

    for (bases, expected_digest) in [
        (
            // Historical coefficient-SRS pin from srs-coefficient-bases.points,
            // hashed as canonical 32-byte compressed points, not stored records.
            &points.coefficient_bases,
            "b3470ff54d467bdfb236f094f7a9355d963d7fbc1e27393452427867a8bcd0db",
        ),
        (
            // Historical Lagrange-SRS pin from the coefficient SRS's inverse
            // group transform, hashed as canonical 32-byte compressed points.
            &points.lagrange_bases,
            "5dc47b6e744a2a86cc4b9b94dd9e7adcc08f94bd4dde59ae506de449709069b4",
        ),
    ] {
        let mut digest = Sha256::new();
        for base in bases {
            digest.update(base.to_bytes());
        }
        assert_eq!(hex::encode(digest.finalize()), expected_digest);
    }
    // Historical Sinsemilla pin from sinsemilla-generators.points, hashed as
    // canonical 32-byte compressed points, not the raw 64-byte coordinates.
    let mut sinsemilla_digest = Sha256::new();
    for point in crate::primitives::tables::sinsemilla_generators() {
        sinsemilla_digest.update(point.to_bytes());
    }
    assert_eq!(
        hex::encode(sinsemilla_digest.finalize()),
        "d61a38f54c39732faec5cc15217f798a6b489051a42e35cfbf7129335cc3a1e1"
    );
}

/// Every prepared field element outside the point file — the coefficient
/// columns however the dial sources them, and the embedded tuples — is a
/// valid loose Montgomery residue whose canonical encoding round-trips.
#[test]
fn embedded_field_elements_respect_representation_bounds() {
    let target = crate::test_codec::target();
    for value in target
        .fixed_polynomials()
        .coefficients()
        .iter()
        .flatten()
        .chain(target.sigma_polynomials().coefficients().iter().flatten())
        .chain(FIXED_TUPLES.iter().flatten())
    {
        assert_valid_base(value);
    }
}
