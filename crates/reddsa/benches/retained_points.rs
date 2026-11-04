use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use group::{Group, GroupEncoding};
use pasta_curves::pallas;
use reddsa::{
    SigningKey, VerificationKey, batch,
    orchard::{Binding, SpendAuth},
};
use std::hint::black_box;

/// Public message shared by every signature and verification path.
const MESSAGE: &[u8; 33] = b"Orchard retained points benchmark";
/// Each workload has this many spend signatures plus one binding signature.
const ACTION_COUNTS: [usize; 3] = [1, 8, 32];

fn retained_points(c: &mut Criterion) {
    let mut rng = rand::rng();
    let binding_sk = SigningKey::<Binding>::new(&mut rng);
    let binding_vk = VerificationKey::from(&binding_sk);
    let binding_bytes: [u8; 32] = binding_vk.into();
    let point = pallas::Point::from_bytes(&binding_bytes).unwrap() + pallas::Point::identity();
    let binding_sig = binding_sk.sign(&mut rng, MESSAGE);
    let spends: Vec<_> = (0..*ACTION_COUNTS.last().unwrap())
        .map(|_| {
            let sk = SigningKey::<SpendAuth>::new(&mut rng);
            (VerificationKey::from(&sk), sk.sign(&mut rng, MESSAGE))
        })
        .collect();
    let mut keys = c.benchmark_group("orchard_binding_key");
    keys.bench_function("byte_roundtrip", |b| {
        b.iter(|| VerificationKey::<Binding>::try_from(black_box(point).to_bytes()).unwrap())
    });
    keys.bench_function("retain_point", |b| {
        b.iter(|| VerificationKey::<Binding>::from(black_box(point)))
    });
    keys.finish();
    let mut verify = c.benchmark_group("orchard_signatures");
    for n in ACTION_COUNTS {
        for path in ["serial_bytes", "serial_point", "batch_bytes", "batch_point"] {
            verify.bench_with_input(BenchmarkId::new(path, n), &n, |b, &n| {
                b.iter(|| {
                    let retained = path.ends_with("point");
                    let bvk = if retained {
                        VerificationKey::<Binding>::from(black_box(point))
                    } else {
                        VerificationKey::<Binding>::try_from(black_box(point).to_bytes()).unwrap()
                    };
                    if path.starts_with("serial") {
                        for (vk, sig) in black_box(&spends[..n]) {
                            vk.verify(MESSAGE, sig).unwrap();
                        }
                        bvk.verify(MESSAGE, &binding_sig).unwrap();
                    } else {
                        let mut batch = batch::Verifier::<SpendAuth, Binding>::new();
                        for (vk, sig) in black_box(&spends[..n]) {
                            batch.queue(if retained {
                                batch::Item::from_spendauth_key(*vk, *sig, MESSAGE)
                            } else {
                                batch::Item::from_spendauth((*vk).into(), *sig, MESSAGE)
                            });
                        }
                        batch.queue(if retained {
                            batch::Item::from_binding_key(bvk, binding_sig, MESSAGE)
                        } else {
                            batch::Item::from_binding(bvk.into(), binding_sig, MESSAGE)
                        });
                        batch.verify(&mut rng).unwrap();
                    }
                })
            });
        }
    }
    verify.finish();
}
criterion_group!(benches, retained_points);
criterion_main!(benches);
