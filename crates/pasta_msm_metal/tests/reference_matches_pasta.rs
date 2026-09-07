//! The reference backend against `pasta_curves`' own arithmetic: random
//! and adversarial inputs over both curves, every window width, and
//! several reduction chunk sizes.

use ff::{Field, PrimeField, WithSmallOrderMulGroup};
use group::Group;
use pasta_curves::arithmetic::CurveExt;
use pasta_curves::{pallas, vesta};
use pasta_msm_metal::curves::{Pallas, Vesta};
use pasta_msm_metal::pipeline::{
    Config, MAX_CHUNK_LOG2, MAX_WINDOW_BITS, MIN_CHUNK_LOG2, MIN_WINDOW_BITS, PastaCurve,
    Reference, multiexp,
};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

fn naive<C: CurveExt>(scalars: &[C::ScalarExt], bases: &[C::AffineExt]) -> C {
    scalars
        .iter()
        .zip(bases)
        .fold(C::identity(), |acc, (k, p)| acc + *p * *k)
}

/// Random inputs seasoned with the awkward cases: zero, one, minus one,
/// the endomorphism eigenvalue, tiny and huge scalars, identity bases, and
/// repeated bases (with equal and with opposite scalars).
fn inputs<C: CurveExt>(terms: usize, seed: u8) -> (Vec<C::ScalarExt>, Vec<C::AffineExt>) {
    let mut rng = XorShiftRng::from_seed([seed; 16]);
    let mut scalars: Vec<C::ScalarExt> =
        (0..terms).map(|_| C::ScalarExt::random(&mut rng)).collect();
    let mut bases: Vec<C::AffineExt> = (0..terms)
        .map(|_| C::random(&mut rng).to_affine())
        .collect();
    let specials = [
        C::ScalarExt::ZERO,
        C::ScalarExt::ONE,
        -C::ScalarExt::ONE,
        C::ScalarExt::ZETA,
        -C::ScalarExt::ZETA,
        C::ScalarExt::from(2),
        C::ScalarExt::from_u128((1 << 127) - 1),
        C::ScalarExt::from_u128(1 << 127),
        -C::ScalarExt::from_u128(1 << 100),
    ];
    for (i, special) in specials.iter().enumerate() {
        if i < terms {
            scalars[i] = *special;
        }
    }
    if terms > 10 {
        bases[10] = C::AffineExt::default();
        bases[11] = bases[3];
        scalars[11] = scalars[3];
        bases[12] = bases[4];
        scalars[12] = -scalars[4];
        bases[13] = bases[5];
    }
    (scalars, bases)
}

fn check<C: PastaCurve>(
    config: &Config,
    scalars: &[C::Scalar],
    bases: &[C::Affine],
    expected: C::Point,
) {
    let got = multiexp::<C>(&Reference, config, scalars, bases).expect("reference never declines");
    assert_eq!(
        got,
        expected,
        "{} terms={} config={config:?}",
        C::NAME,
        scalars.len()
    );
}

#[test]
fn small_sizes_every_window_width() {
    for terms in [0usize, 1, 2, 3, 9, 14, 33, 64, 130] {
        let (ps, pb) = inputs::<pallas::Point>(terms, 1);
        let (vs, vb) = inputs::<vesta::Point>(terms, 2);
        let pallas_expected = naive::<pallas::Point>(&ps, &pb);
        let vesta_expected = naive::<vesta::Point>(&vs, &vb);
        for window_bits in MIN_WINDOW_BITS..=MAX_WINDOW_BITS {
            // Wide windows over tiny inputs are slow in the reference
            // backend; sample them.
            if window_bits > 12 && terms > 33 {
                continue;
            }
            for chunk_log2 in [MIN_CHUNK_LOG2, 3, MAX_CHUNK_LOG2] {
                let config = Config {
                    min_terms: 0,
                    window_bits: Some(window_bits),
                    chunk_log2,
                };
                check::<Pallas>(&config, &ps, &pb, pallas_expected);
                check::<Vesta>(&config, &vs, &vb, vesta_expected);
            }
        }
    }
}

#[test]
fn default_plan_medium_sizes() {
    for (terms, seed) in [(257usize, 5u8), (1000, 6), (2050, 7)] {
        let (ps, pb) = inputs::<pallas::Point>(terms, seed);
        let expected = pallas::Point::try_multiexp_vartime(&ps, &pb)
            .unwrap_or_else(|| naive::<pallas::Point>(&ps, &pb));
        check::<Pallas>(&Config::default(), &ps, &pb, expected);

        let (vs, vb) = inputs::<vesta::Point>(terms, seed + 100);
        let expected = vesta::Point::try_multiexp_vartime(&vs, &vb)
            .unwrap_or_else(|| naive::<vesta::Point>(&vs, &vb));
        check::<Vesta>(&Config::default(), &vs, &vb, expected);
    }
}

#[test]
fn every_chunk_size_reduces_correctly() {
    let (ps, pb) = inputs::<pallas::Point>(300, 9);
    let expected = naive::<pallas::Point>(&ps, &pb);
    for chunk_log2 in MIN_CHUNK_LOG2..=MAX_CHUNK_LOG2 {
        for window_bits in [5, 8, 11] {
            let config = Config {
                min_terms: 0,
                window_bits: Some(window_bits),
                chunk_log2,
            };
            check::<Pallas>(&config, &ps, &pb, expected);
        }
    }
}

#[test]
fn all_identity_bases_and_all_zero_scalars() {
    let terms = 40;
    let (ps, pb) = inputs::<pallas::Point>(terms, 11);
    let zeros = vec![pallas::Scalar::ZERO; terms];
    check::<Pallas>(&Config::default(), &zeros, &pb, pallas::Point::identity());
    let identities = vec![pallas::Affine::default(); terms];
    check::<Pallas>(
        &Config::default(),
        &ps,
        &identities,
        pallas::Point::identity(),
    );
    // Every term in the same bucket: one base repeated with one scalar.
    let same_base = vec![pb[0]; terms];
    let same_scalar = vec![ps[0]; terms];
    let expected = pb[0] * (ps[0] * pallas::Scalar::from(terms as u64));
    check::<Pallas>(&Config::default(), &same_scalar, &same_base, expected);
    // Cancelling pairs sum to the identity through the exceptional paths.
    let mut cancel_scalars = same_scalar.clone();
    for scalar in cancel_scalars.iter_mut().skip(terms / 2) {
        *scalar = -*scalar;
    }
    check::<Pallas>(
        &Config::default(),
        &cancel_scalars,
        &same_base,
        pallas::Point::identity(),
    );
}

#[test]
fn registry_integration_through_pasta_curves() {
    // Install the reference accelerator with a low threshold and confirm
    // pasta_curves routes MSMs through it (this test binary owns the
    // process-wide registry).
    let config = Config {
        min_terms: 8,
        ..Config::default()
    };
    pasta_msm_metal::install_reference(config).expect("first install");
    assert_eq!(
        pasta_msm_metal::install_reference(config),
        Err(pasta_msm_metal::InstallError::AlreadyInstalled)
    );
    let installed = pasta_curves::glv::accelerator::installed().expect("installed");
    assert_eq!(installed.name(), "pasta-msm-reference");

    let (vs, vb) = inputs::<vesta::Point>(600, 21);
    let expected = naive::<vesta::Point>(&vs, &vb);
    let got = vesta::Point::try_multiexp_vartime(&vs, &vb).expect("accelerated");
    assert_eq!(got, expected);
    let got = halo2_style_best_multiexp(&vs, &vb);
    assert_eq!(got, expected);
}

/// What halo2's `best_multiexp` does before its generic fallback.
fn halo2_style_best_multiexp(scalars: &[vesta::Scalar], bases: &[vesta::Affine]) -> vesta::Point {
    vesta::Point::try_multiexp_vartime(scalars, bases).expect("accelerator answers")
}
