//! On Apple silicon: the Metal backend against the reference backend
//! (bit-identical window results) and against `pasta_curves` (equal group
//! elements). Skipped, with a note, when no Metal device can be opened —
//! headless CI virtual machines sometimes expose none.

#![cfg(all(target_vendor = "apple", target_arch = "aarch64"))]

use ff::Field;
use pasta_curves::arithmetic::CurveExt;
use pasta_curves::{pallas, vesta};
use pasta_msm_metal::curves::{Pallas, Vesta};
use pasta_msm_metal::metal::Metal;
use pasta_msm_metal::pipeline::{Backend, Config, PastaCurve, Plan, Reference, multiexp, prepare};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

fn open() -> Option<Metal> {
    match Metal::open() {
        Ok(metal) => {
            eprintln!("Metal device: {}", metal.device_name());
            Some(metal)
        }
        Err(error) => {
            eprintln!("skipping: {error}");
            None
        }
    }
}

fn inputs<C: CurveExt>(terms: usize, seed: u8) -> (Vec<C::ScalarExt>, Vec<C::AffineExt>) {
    let mut rng = XorShiftRng::from_seed([seed; 16]);
    let mut scalars: Vec<C::ScalarExt> =
        (0..terms).map(|_| C::ScalarExt::random(&mut rng)).collect();
    let mut bases: Vec<C::AffineExt> = (0..terms)
        .map(|_| C::random(&mut rng).to_affine())
        .collect();
    if terms > 4 {
        scalars[0] = C::ScalarExt::ZERO;
        scalars[1] = -C::ScalarExt::ONE;
        bases[2] = C::AffineExt::default();
        bases[3] = bases[4];
    }
    (scalars, bases)
}

fn naive<C: CurveExt>(scalars: &[C::ScalarExt], bases: &[C::AffineExt]) -> C {
    scalars
        .iter()
        .zip(bases)
        .fold(C::identity(), |acc, (k, p)| acc + *p * *k)
}

fn windows_match<C: PastaCurve>(
    metal: &Metal,
    config: &Config,
    scalars: &[C::Scalar],
    bases: &[C::Affine],
) {
    let plan = Plan::new(scalars.len(), config);
    let job = prepare::<C>(scalars, bases, &plan);
    let expected = Reference.run(&job, &C::FIELD).expect("reference");
    let got = metal.run(&job, &C::FIELD).expect("metal");
    assert_eq!(
        got,
        expected,
        "{} window results differ: {config:?}",
        C::NAME
    );
}

#[test]
fn metal_matches_reference_and_pasta_curves() {
    let Some(metal) = open() else { return };
    for (terms, seed) in [(1usize, 1u8), (5, 2), (64, 3), (513, 4), (4096, 5)] {
        let (ps, pb) = inputs::<pallas::Point>(terms, seed);
        let (vs, vb) = inputs::<vesta::Point>(terms, seed + 50);
        let pallas_expected = naive::<pallas::Point>(&ps, &pb);
        let vesta_expected = naive::<vesta::Point>(&vs, &vb);
        for config in [
            Config::default(),
            Config {
                window_bits: Some(4),
                chunk_log2: 1,
                ..Config::default()
            },
            Config {
                window_bits: Some(9),
                chunk_log2: 6,
                ..Config::default()
            },
        ] {
            windows_match::<Pallas>(&metal, &config, &ps, &pb);
            windows_match::<Vesta>(&metal, &config, &vs, &vb);
            let got = multiexp::<Pallas>(&metal, &config, &ps, &pb).expect("pallas");
            assert_eq!(got, pallas_expected);
            let got = multiexp::<Vesta>(&metal, &config, &vs, &vb).expect("vesta");
            assert_eq!(got, vesta_expected);
        }
    }
}

#[test]
fn metal_accelerator_serves_the_registry() {
    if Metal::open().is_err() {
        eprintln!("skipping: no Metal device");
        return;
    }
    let config = Config {
        min_terms: 16,
        ..Config::default()
    };
    pasta_msm_metal::install(config).expect("install");
    let (vs, vb) = inputs::<vesta::Point>(1000, 9);
    let expected = naive::<vesta::Point>(&vs, &vb);
    let got = vesta::Point::try_multiexp_vartime(&vs, &vb).expect("accelerated");
    assert_eq!(got, expected);
}
