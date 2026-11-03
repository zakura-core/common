use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use redjubjub::{SigningKey, SpendAuth, VerificationKey, batch};
use std::hint::black_box;

/// A public fixture sighash shared by every timed path.
const SIGHASH: [u8; 32] = [42; 32];
/// Singleton and larger spend sets exercise both batch-verification paths.
const SPEND_COUNTS: [usize; 3] = [1, 8, 32];

fn prepare(key: VerificationKey<SpendAuth>, retain: bool) {
    let affine = if retain {
        jubjub::AffinePoint::from(key)
    } else {
        jubjub::AffinePoint::from_bytes(key.into()).unwrap()
    };
    assert!(!bool::from(affine.is_small_order()));
    black_box((affine.get_u(), affine.get_v()));
}

fn spend_keys(c: &mut Criterion) {
    let mut rng = rand::rng();
    let fixtures: Vec<_> = (0..*SPEND_COUNTS.last().unwrap())
        .map(|_| {
            let sk = SigningKey::<SpendAuth>::new(&mut rng);
            let key = VerificationKey::from(&sk);
            // Wire decoding remains mandatory and is outside the timed paths.
            let key = VerificationKey::<SpendAuth>::try_from(<[u8; 32]>::from(key)).unwrap();
            (key, sk.sign(&mut rng, &SIGHASH))
        })
        .collect();
    let mut prep = c.benchmark_group("sapling_spend_preparation");
    for (name, retained) in [("decode_again", false), ("cached_point", true)] {
        prep.bench_function(name, |b| {
            b.iter(|| prepare(black_box(fixtures[0].0), retained))
        });
    }
    prep.finish();
    let mut verify = c.benchmark_group("sapling_spend_verification");
    for n in SPEND_COUNTS {
        for (path, affine, key) in [
            ("old", false, false),
            ("affine_only", true, false),
            ("queue_only", false, true),
            ("both", true, true),
        ] {
            verify.bench_with_input(BenchmarkId::new(path, n), &n, |b, &n| {
                b.iter(|| {
                    let mut batch = batch::Verifier::new();
                    for (vk, sig) in black_box(&fixtures[..n]) {
                        prepare(*vk, affine);
                        if key {
                            batch.queue(batch::Item::from_spendauth_key(*vk, *sig, &SIGHASH));
                        } else {
                            batch.queue(((*vk).into(), *sig, &SIGHASH));
                        }
                    }
                    batch.verify(&mut rng).unwrap();
                })
            });
        }
    }
    verify.finish();
}
criterion_group!(benches, spend_keys);
criterion_main!(benches);
