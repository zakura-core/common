#[macro_use]
extern crate criterion;

use crate::arithmetic::best_multiexp;
use crate::pasta::{EqAffine, Fp};
use crate::poly::commitment::Params;
#[cfg(feature = "orbits")]
use crate::poly::{EvaluationDomain, commitment::Blind};
#[cfg(feature = "orbits")]
use criterion::black_box;
use criterion::{BenchmarkId, Criterion};
use group::ff::Field;
use halo2_proofs::*;
use rand::rng;

fn criterion_benchmark(c: &mut Criterion) {
    #[cfg(feature = "orbits")]
    {
        const ORCHARD_K: u32 = 11;

        let params = Params::<EqAffine>::new(ORCHARD_K);
        assert!(params.prepare_commitments());
        let domain = EvaluationDomain::<Fp>::new(1, ORCHARD_K);
        let polynomial = domain.coeff_from_vec(
            (0..(1 << ORCHARD_K))
                .map(|_| Fp::random(&mut rng()))
                .collect(),
        );
        let blind = Blind(Fp::random(&mut rng()));
        let mut prepared = c.benchmark_group("prepared Orchard commitment MSM");
        prepared.sample_size(30);
        prepared.bench_function("coefficient-k11", |b| {
            b.iter(|| params.commit(black_box(&polynomial), black_box(blind)))
        });
        prepared.finish();
    }

    let params = Params::<EqAffine>::new(8);
    let bases = params.get_g();
    let mut late_ipa = c.benchmark_group("late IPA MSM");
    late_ipa.sample_size(30);
    for terms in [1, 2, 4, 8, 16, 32, 64, 128, 256] {
        late_ipa.bench_function(BenchmarkId::new("terms", terms), |b| {
            let coeffs = (0..terms)
                .map(|_| Fp::random(&mut rng()))
                .collect::<Vec<_>>();

            b.iter(|| best_multiexp(&coeffs, &bases[..terms]))
        });
    }
    late_ipa.finish();

    let mut late_ipa_round = c.benchmark_group("late IPA round");
    late_ipa_round.sample_size(30);
    // An IPA half has power-of-two terms, then the round MSM adds U and W.
    for terms in [3, 4, 6, 10, 18, 34, 66] {
        late_ipa_round.bench_function(BenchmarkId::new("terms per side", terms), |b| {
            let left_coeffs = (0..terms)
                .map(|_| Fp::random(&mut rng()))
                .collect::<Vec<_>>();
            let right_coeffs = (0..terms)
                .map(|_| Fp::random(&mut rng()))
                .collect::<Vec<_>>();
            let (left_bases, right_bases) = bases[..terms * 2].split_at(terms);

            b.iter(|| {
                maybe_rayon::join(
                    || best_multiexp(&left_coeffs, left_bases),
                    || best_multiexp(&right_coeffs, right_bases),
                )
            })
        });
    }
    late_ipa_round.finish();

    let mut group = c.benchmark_group("msm");
    for k in 8..16 {
        group
            .bench_function(BenchmarkId::new("k", k), |b| {
                let coeffs = (0..(1 << k))
                    .map(|_| Fp::random(&mut rng()))
                    .collect::<Vec<_>>();
                let bases = Params::<EqAffine>::new(k).get_g();

                b.iter(|| best_multiexp(&coeffs, &bases))
            })
            .sample_size(30);
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
