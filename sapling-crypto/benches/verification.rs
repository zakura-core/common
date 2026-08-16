use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use group::{Curve, Group, GroupEncoding};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::time::Duration;

fn bench_point_preparation(c: &mut Criterion) {
    let mut rng = XorShiftRng::from_seed([0x5a; 16]);
    let mut group = c.benchmark_group("sapling-point-preparation");
    group
        .sample_size(50)
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(3));

    for &(spends, outputs) in &[(1, 0), (2, 0), (0, 1), (0, 2), (1, 2), (2, 2), (8, 8)] {
        let point_count = spends + outputs;
        let points = (0..point_count)
            .map(|_| jubjub::ExtendedPoint::random(&mut rng))
            .collect::<Vec<_>>();
        let encodings = points
            .iter()
            .map(|point| point.to_bytes())
            .collect::<Vec<_>>();
        let value_commitments = (0..point_count)
            .map(|_| jubjub::ExtendedPoint::random(&mut rng))
            .collect::<Vec<_>>();
        let id = format!("{spends}-spends-{outputs}-outputs");

        group.bench_with_input(
            BenchmarkId::new("individual", &id),
            &(&encodings, &value_commitments),
            |b, (encodings, value_commitments)| {
                b.iter(|| {
                    for encoding in &encodings[..spends] {
                        let point = jubjub::AffinePoint::from_bytes(*encoding).unwrap();
                        black_box(point.is_small_order());
                    }
                    for encoding in &encodings[spends..] {
                        let point = jubjub::ExtendedPoint::from_bytes(encoding).unwrap();
                        black_box(point.is_small_order());
                        black_box(point.to_affine());
                    }
                    for value_commitment in *value_commitments {
                        black_box(value_commitment.to_affine());
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("optimized", &id),
            &(&encodings, &value_commitments),
            |b, (encodings, value_commitments)| {
                b.iter(|| {
                    if encodings.len() == 1 {
                        let point = jubjub::AffinePoint::from_bytes(encodings[0]).unwrap();
                        black_box(point.is_small_order());
                        black_box(value_commitments[0].to_affine());
                        return;
                    }

                    let points = jubjub::AffinePoint::batch_from_bytes(encodings.iter().copied());
                    for point in points {
                        black_box(point.unwrap().is_small_order());
                    }

                    let value_commitments = value_commitments.to_vec();
                    let mut normalized =
                        vec![jubjub::AffinePoint::identity(); value_commitments.len()];
                    jubjub::ExtendedPoint::batch_normalize(&value_commitments, &mut normalized);
                    black_box(normalized);
                });
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_point_preparation);
criterion_main!(benches);
