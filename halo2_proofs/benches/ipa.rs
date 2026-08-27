#[macro_use]
extern crate criterion;

use criterion::{black_box, BenchmarkId, Criterion};
use ff::Field;
use group::Curve;
use halo2_proofs::pasta::{EqAffine, Fp};
use halo2_proofs::poly::{
    commitment::{create_proof, Blind, Params},
    EvaluationDomain,
};
use halo2_proofs::transcript::{Blake2bWrite, Challenge255, Transcript, TranscriptWrite};
use rand::rng;

fn criterion_benchmark(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("ipa-opening");
    group.sample_size(20);

    for k in [8, 11, 14] {
        let params = Params::<EqAffine>::new(k);
        let domain = EvaluationDomain::new(1, k);
        let mut polynomial = domain.empty_coeff();
        for coefficient in polynomial.iter_mut() {
            *coefficient = Fp::random(&mut rng());
        }
        let blind = Blind(Fp::random(&mut rng()));
        let commitment = params.commit(&polynomial, blind).to_affine();

        let mut statement = Blake2bWrite::<_, _, Challenge255<_>>::init(Vec::new());
        statement.write_point(commitment).unwrap();
        let x = *statement.squeeze_challenge_scalar::<()>();
        let value = polynomial[..]
            .iter()
            .rev()
            .fold(Fp::ZERO, |accumulator, coefficient| {
                accumulator * x + coefficient
            });

        group.bench_with_input(BenchmarkId::from_parameter(k), &k, |bencher, _| {
            bencher.iter(|| {
                let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(Vec::new());
                transcript.write_point(commitment).unwrap();
                let transcript_x = *transcript.squeeze_challenge_scalar::<()>();
                assert_eq!(transcript_x, x);
                transcript.write_scalar(value).unwrap();
                create_proof(&params, rng(), &mut transcript, &polynomial, blind, x).unwrap();
                black_box(transcript.finalize())
            });
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
