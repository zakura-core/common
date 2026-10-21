//! Public verifier contract, historical compatibility, and mixed-batch soundness.
#[path = "support/verification.rs"]
mod corpus;
mod support;
use corpus::{VERSIONS, small};
use zakura_sensei::primitives::pallas;
use zakura_sensei::{CircuitVersion, Error, VerificationRequest, verify_proofs};

fn no_randomness() -> Result<u64, zakura_sensei::RandomnessError> {
    panic!("unexpected RNG call")
}

#[test]
fn committed_reference_proofs_and_batches() {
    assert_eq!(verify_proofs(&[], &mut no_randomness), Ok(()));
    let mut fixtures = Vec::new();
    for version in VERSIONS {
        fixtures.push(corpus::original(version, false));
        for count in [1, 2] {
            fixtures.push(small(version, count));
        }
        if version != CircuitVersion::PostNu6_3 {
            for count in [3, 65, 128] {
                fixtures.push(corpus::historical(version, count));
            }
        }
    }
    fixtures.push(corpus::original(CircuitVersion::PostNu6_3, true));
    fixtures.extend(corpus::flags());
    for fixture in &fixtures {
        assert_eq!(
            verify_proofs(&[fixture.request()], &mut no_randomness),
            Ok(()),
            "{:?}, {} Actions",
            fixture.version,
            fixture.statements.len()
        );
    }
    let requests: Vec<_> = fixtures.iter().map(corpus::Fixture::request).collect();
    for seed in [89, 97, 101] {
        assert_eq!(
            verify_proofs(&requests, &mut support::SplitMix64::new(seed)),
            Ok(())
        );
        let mut reverse = requests.clone();
        reverse.reverse();
        assert_eq!(
            verify_proofs(&reverse, &mut support::SplitMix64::new(seed)),
            Ok(())
        );
    }
}

#[test]
fn every_version_pair_and_batch_order() {
    let fixtures = VERSIONS.map(|version| corpus::original(version, false));
    for fixture in &fixtures {
        for version in VERSIONS {
            let request =
                VerificationRequest::new(version, &fixture.statements, fixture.proof).unwrap();
            let expected = if version == fixture.version {
                Ok(())
            } else {
                Err(Error::InvalidProof)
            };
            assert_eq!(verify_proofs(&[request], &mut no_randomness), expected);
            assert_eq!(verify_proofs(&[request; 2], &mut || Ok(73)), expected);
        }
    }
    for a in &fixtures {
        for b in &fixtures {
            for c in &fixtures {
                assert_eq!(
                    verify_proofs(&[a.request(), b.request(), c.request()], &mut || Ok(79)),
                    Ok(())
                );
            }
        }
    }
}

#[test]
fn historical_suffixes_preserve_singleton_and_batch_verification() {
    let version = CircuitVersion::InsecurePreNu6_2;
    for count in [1, 2, 3, 65, 128] {
        let fixture = if count <= 2 {
            small(version, count)
        } else {
            corpus::historical(version, count)
        };
        for suffix in [&[0][..], &[255; 33][..]] {
            let mut padded = fixture.proof.to_vec();
            padded.extend_from_slice(suffix);
            let request = VerificationRequest::new(version, &fixture.statements, &padded).unwrap();
            assert_eq!(verify_proofs(&[request], &mut no_randomness), Ok(()));
            assert_eq!(verify_proofs(&[request; 2], &mut || Ok(73)), Ok(()));
            assert_eq!(&padded[fixture.proof.len()..], suffix);
            padded[0] ^= 1;
            let request = VerificationRequest::new(version, &fixture.statements, &padded).unwrap();
            assert_eq!(
                verify_proofs(&[request], &mut no_randomness),
                Err(Error::InvalidProof)
            );
        }
    }
}

#[test]
fn mixed_batches_reject_one_invalid_proof_at_every_position() {
    let fixtures: Vec<_> = VERSIONS
        .into_iter()
        .flat_map(|v| [small(v, 1), small(v, 2)])
        .collect();
    let workers = std::thread::available_parallelism().map_or(1, usize::from);
    let count = (2 * workers + 1).max(2 * fixtures.len() + 1);
    let baseline: Vec<_> = (0..count)
        .map(|i| fixtures[i % fixtures.len()].request())
        .collect();
    let check =
        |batch: &[VerificationRequest<'_>]| verify_proofs(batch, &mut support::SplitMix64::new(89));
    assert_eq!(check(&baseline), Ok(()));
    for malformed in [false, true] {
        let invalid: Vec<_> = fixtures
            .iter()
            .map(|fixture| {
                let mut proof = fixture.proof.to_vec();
                if malformed {
                    proof[..32].fill(0);
                } else {
                    let offset = proof.len() - 32;
                    let response =
                        pallas::Base::from_repr(proof[offset..].try_into().unwrap()).unwrap();
                    proof[offset..].copy_from_slice(&(response + pallas::Base::from(1)).to_repr());
                }
                proof
            })
            .collect();
        let mut batch = baseline.clone();
        for index in 0..batch.len() {
            let i = index % fixtures.len();
            let fixture = &fixtures[i];
            batch[index] =
                VerificationRequest::new(fixture.version, &fixture.statements, &invalid[i])
                    .unwrap();
            assert_eq!(
                check(&batch),
                Err(Error::InvalidProof),
                "position {index}, malformed={malformed}, workers={workers}"
            );
            batch[index] = baseline[index];
        }
        assert_eq!(check(&batch), Ok(()));
    }
    // Wrong key labels also fail at every position in a mixed batch.
    let fixtures = VERSIONS.map(|v| corpus::original(v, false));
    let mut batch: Vec<_> = (0..count)
        .map(|i| fixtures[i % fixtures.len()].request())
        .collect();
    for index in 0..count {
        let fixture = &fixtures[index % fixtures.len()];
        let wrong_version = VERSIONS[(index + 1) % VERSIONS.len()];
        batch[index] =
            VerificationRequest::new(wrong_version, &fixture.statements, fixture.proof).unwrap();
        assert_eq!(check(&batch), Err(Error::InvalidProof));
        batch[index] = fixture.request();
    }
}

#[test]
fn shape_points_encodings_and_public_inputs() {
    for version in VERSIONS {
        let fixture = small(version, 2);
        let statements = &fixture.statements;
        let proof = fixture.proof;
        assert_eq!(
            VerificationRequest::new(version, &[], proof).err(),
            Some(Error::InvalidInput)
        );
        // Every truncated byte length, plus trailing bytes and the wrong Action count.
        for length in 0..proof.len() {
            assert_eq!(
                VerificationRequest::new(version, statements, &proof[..length]).err(),
                Some(Error::InvalidInput)
            );
        }
        let wrong_count = VerificationRequest::new(version, &statements[..1], proof);
        if version == CircuitVersion::InsecurePreNu6_2 {
            assert_eq!(
                verify_proofs(&[wrong_count.unwrap()], &mut no_randomness),
                Err(Error::InvalidProof)
            );
        } else {
            assert_eq!(wrong_count.err(), Some(Error::InvalidInput));
        }
        let mut trailing = proof.to_vec();
        trailing.push(0);
        let padded = VerificationRequest::new(version, statements, &trailing);
        if version == CircuitVersion::InsecurePreNu6_2 {
            assert_eq!(
                verify_proofs(&[padded.unwrap()], &mut no_randomness),
                Ok(())
            );
        } else {
            assert_eq!(padded.err(), Some(Error::InvalidInput));
        }
        let zero = zakura_sensei::Fp::from_bytes([0; 32]).unwrap();
        let mut one = [0; 32];
        one[0] = 1;
        let one = zakura_sensei::Fp::from_bytes(one).unwrap();
        for point in [(zero, zero), (one, zero)] {
            let mut bad = statements.clone();
            bad[0].rk = point;
            assert_eq!(
                VerificationRequest::new(version, &bad, proof).err(),
                Some(Error::InvalidInput)
            );
        }
        let mut bad = statements.clone();
        bad[0].cv_net = (one, zero);
        assert_eq!(
            VerificationRequest::new(version, &bad, proof).err(),
            Some(Error::InvalidInput)
        );
        bad[0].cv_net = (zero, zero);
        assert_eq!(
            verify_proofs(
                &[VerificationRequest::new(version, &bad, proof).unwrap()],
                &mut no_randomness
            ),
            Err(Error::InvalidProof)
        );
        // A different valid point must fail algebraically rather than at decoding.
        for replace_rk in [false, true] {
            let mut bad = statements.clone();
            if replace_rk {
                bad[0].rk = statements[1].rk;
            } else {
                bad[0].cv_net = statements[1].rk;
            }
            assert_eq!(
                verify_proofs(
                    &[VerificationRequest::new(version, &bad, proof).unwrap()],
                    &mut no_randomness
                ),
                Err(Error::InvalidProof)
            );
        }
        for encoding in [[0; 32], [0xff; 32]] {
            let mut bad = proof.to_vec();
            bad[..32].copy_from_slice(&encoding);
            assert_eq!(
                verify_proofs(
                    &[VerificationRequest::new(version, statements, &bad).unwrap()],
                    &mut no_randomness
                ),
                Err(Error::InvalidProof)
            );
        }
        let mut bad = proof.to_vec();
        let end = bad.len();
        bad[end - 32..].fill(0xff);
        assert_eq!(
            verify_proofs(
                &[VerificationRequest::new(version, statements, &bad).unwrap()],
                &mut no_randomness
            ),
            Err(Error::InvalidProof)
        );
        for action in 0..statements.len() {
            for row in [0, 3, 6, 7, 8, 9] {
                let mut inputs = fixture.instances.clone();
                if row == 9 && version != CircuitVersion::PostNu6_3 {
                    let mut bad = statements.clone();
                    bad[action].disable_cross_address = true;
                    assert_eq!(
                        VerificationRequest::new(version, &bad, proof).err(),
                        Some(Error::InvalidInput)
                    );
                    continue;
                }
                inputs[action][row] = if row >= 7 {
                    pallas::Base::from(1) - inputs[action][row]
                } else {
                    inputs[action][row] + pallas::Base::from(1)
                };
                let altered = corpus::from_instances(version, inputs, proof);

                assert_eq!(
                    verify_proofs(&[altered.request()], &mut no_randomness),
                    Err(Error::InvalidProof)
                );
            }
        }
        let mut reversed = statements.clone();
        reversed.reverse();
        assert_eq!(
            verify_proofs(
                &[VerificationRequest::new(version, &reversed, proof).unwrap()],
                &mut no_randomness
            ),
            Err(Error::InvalidProof)
        );
        for count in [65, 128, 1024] {
            let statements = vec![statements[0].clone(); count];
            let bytes = vec![0; 2720 + 2272 * count];
            assert!(VerificationRequest::new(version, &statements, &bytes).is_ok());
        }
    }
}

#[test]
fn randomness_failures_and_concurrent_calls() {
    let fixtures = VERSIONS.map(|version| small(version, 1));
    let requests = fixtures.each_ref().map(corpus::Fixture::request);
    for request in requests {
        assert_eq!(verify_proofs(&[request], &mut no_randomness), Ok(()));
        assert_eq!(
            verify_proofs(&[request; 2], &mut || Ok(0)),
            Err(Error::RetryRandomness)
        );
    }
    for failure in 0..16 {
        let mut calls = 0;
        let mut rng = || {
            let result = if calls == failure {
                Err(zakura_sensei::RandomnessError)
            } else {
                Ok(73)
            };
            calls += 1;
            result
        };
        assert_eq!(verify_proofs(&requests, &mut rng), Err(Error::RngFailure));
        assert_eq!(calls, failure + 1);
    }
    for zero_weight in 0..2 {
        let mut calls = 0;
        assert_eq!(
            verify_proofs(&requests, &mut || {
                let value = if calls / 8 == zero_weight { 0 } else { 79 };
                calls += 1;
                Ok(value)
            }),
            Err(Error::RetryRandomness)
        );
        assert_eq!(calls, (zero_weight + 1) * 8);
    }
    let batch: Vec<_> = requests.into_iter().cycle().take(9).collect();
    let mut calls = 0;
    assert_eq!(
        verify_proofs(&batch, &mut || {
            calls += 1;
            Ok(79)
        }),
        Ok(())
    );
    assert_eq!(calls, 8 * 8);
    std::thread::scope(|scope| {
        for _ in 0..8 {
            scope.spawn(|| {
                for _ in 0..5 {
                    zakura_sensei::warm_up_verifier();
                    for request in requests {
                        assert_eq!(verify_proofs(&[request], &mut no_randomness), Ok(()));
                    }
                    assert_eq!(verify_proofs(&requests, &mut || Ok(83)), Ok(()));
                }
            });
        }
    });
}
