#[macro_use]
extern crate criterion;

use crate::arithmetic::{best_fft, CurveExt};
use crate::pasta::{Eq, EqAffine, Fp};
use crate::poly::commitment::Params;
use group::{
    ff::{Field, PrimeField},
    Curve, CurveAffine,
};
use halo2_proofs::*;

use criterion::{BatchSize, BenchmarkId, Criterion};
use rand::rng;

const ORCHARD_K: u32 = 11;
const ORCHARD_EXTENDED_K: u32 = 14;

fn criterion_benchmark(c: &mut Criterion) {
    let params = Params::<EqAffine>::new(ORCHARD_K);
    let minv = Fp::TWO_INV.pow_vartime([u64::from(ORCHARD_K)]);
    let curve_fft_input: Vec<Eq> = params
        .get_g()
        .iter()
        .map(|point| Eq::from(*point) * minv)
        .collect::<Vec<_>>();
    let mut omega = Fp::ROOT_OF_UNITY_INV;
    for _ in ORCHARD_K..Fp::S {
        omega = omega.square();
    }

    c.bench_function("curve-fft/native-k11", |b| {
        b.iter_batched(
            || curve_fft_input.clone(),
            |mut points| {
                best_fft(&mut points, omega, ORCHARD_K);
                let mut affine = vec![EqAffine::identity(); points.len()];
                Eq::batch_normalize(&points, &mut affine);
                affine
            },
            BatchSize::LargeInput,
        );
    });
    c.bench_function("curve-fft/affine-eisenstein-k11", |b| {
        b.iter_batched(
            || {
                (
                    curve_fft_input.clone(),
                    vec![EqAffine::identity(); curve_fft_input.len()],
                )
            },
            |(points, mut affine)| {
                assert!(Eq::fft_vartime(&points, &mut affine, omega, ORCHARD_K,));
                affine
            },
            BatchSize::LargeInput,
        );
    });

    c.bench_function("params/new-k11", |b| {
        b.iter(|| Params::<EqAffine>::new(ORCHARD_K));
    });

    let mut group = c.benchmark_group("fft");
    for k in 3..19 {
        group.bench_function(BenchmarkId::new("k", k), |b| {
            let mut a = (0..(1 << k))
                .map(|_| Fp::random(&mut rng()))
                .collect::<Vec<_>>();
            let omega = Fp::random(&mut rng()); // would be weird if this mattered
            b.iter(|| {
                best_fft(&mut a, omega, k as u32);
            });
        });
    }

    let extension = 1 << (ORCHARD_EXTENDED_K - ORCHARD_K);
    let domain = poly::EvaluationDomain::<Fp>::new(extension + 1, ORCHARD_K);
    assert_eq!(domain.extended_len(), 1 << ORCHARD_EXTENDED_K);
    let coefficients = (0..(1 << ORCHARD_K))
        .map(|_| Fp::random(&mut rng()))
        .collect::<Vec<_>>();

    group.bench_function(
        BenchmarkId::new("coeff_to_extended", "orchard-k11-to-k14"),
        |b| {
            b.iter_batched(
                || domain.coeff_from_vec(coefficients.clone()),
                |coefficients| domain.coeff_to_extended(coefficients),
                BatchSize::LargeInput,
            );
        },
    );
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
