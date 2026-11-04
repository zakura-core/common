//! Version-independent differential and adversarial verifier matrix.
use super::*;
use crate::CircuitVersion;
use sensei_shared::records::VK_COLUMN_COUNT;

fn compare(fixture: &corpus::Fixture, proof: &[u8], weight: Fp) {
    compare_equation_with_instances(
        fixture.version,
        &fixture.statements,
        &fixture.instances,
        proof,
        weight,
    );
}

/// Independent byte inventory, checked against each actual proof extent and
/// the Halo2 transcript in the differential tests.
fn slots(actions: usize) -> (Vec<usize>, Vec<usize>) {
    let evaluations = (22 * actions + 9) * 32;
    let q_prime = evaluations + (49 * actions + 45) * 32;
    let u = q_prime + 32;
    let s = u + POINT_SETS * 32;
    let responses = s + (1 + 2 * ROUNDS) * 32;
    assert_eq!(
        responses + 64,
        crate::native::protocol::transcript_encoding::proof_capacity(actions).unwrap()
    );
    let points = (0..evaluations)
        .step_by(32)
        .chain([q_prime])
        .chain((s..responses).step_by(32))
        .collect();
    let scalars = (evaluations..q_prime)
        .step_by(32)
        .chain((u..s).step_by(32))
        .chain([responses, responses + 32])
        .collect();
    (points, scalars)
}

#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "reference key generation requires --release"
)]
fn pinned_keys_and_instance_prefixes_match_reference() {
    let runtime = VerifierRuntime::get();
    let current = corpus::pinned_description(CircuitVersion::PostNu6_3);
    let current_prefix = current.split_once("    fixed_commitments: [").unwrap().0;
    for version in corpus::VERSIONS {
        let pinned = corpus::pinned_description(version);
        let (prefix, points) = pinned.split_once("    fixed_commitments: [").unwrap();
        assert_eq!(
            prefix, current_prefix,
            "shared constraint system: {version:?}"
        );
        let points: Vec<_> = points
            .lines()
            .map(str::trim)
            .filter(|s| s.starts_with("(0x"))
            .collect();
        assert_eq!(points.len(), VK_COLUMN_COUNT);
        for (point, &slot) in points.iter().zip(&VK_DATA.columns[version.index()]) {
            let (x, y) = VK_COMMITMENTS[slot as usize].coordinates();
            let hex_field =
                |bytes: [u8; 32]| hex::encode(bytes.into_iter().rev().collect::<Vec<_>>());
            let actual = format!(
                "(0x{}, 0x{})",
                hex_field(x.to_bytes()),
                hex_field(y.to_bytes())
            );
            assert_eq!(actual, point.trim_end_matches(','));
        }
        let fixture = corpus::original(version, false);
        // The frozen challenge records also pin each key's transcript representative.
        for (statement, expected) in fixture.statements.iter().zip(&fixture.instances) {
            assert_eq!(
                statement.native()[..version.instance_len()]
                    .iter()
                    .map(scalar)
                    .collect::<Vec<_>>(),
                *expected
            );
        }
        let native: Vec<_> = fixture
            .statements
            .iter()
            .map(PublicStatement::native)
            .collect();
        let absorb = |len| {
            let mut reader = Reader::new(&[]);
            runtime.executor.run(|executor| {
                absorb_instances(
                    &mut reader,
                    &native,
                    len,
                    &runtime.srs,
                    &mut MsmWorkspace::new(),
                    Execution::new(executor, runtime.executor.budget()),
                )
                .unwrap();
            });
            reader.challenge()
        };
        // A legacy nine-row column and the same column padded with a zero
        // tenth value are exactly the same polynomial and commitment.
        assert_eq!(
            absorb(corpus::LEGACY_ROWS).to_bytes(),
            absorb(INSTANCE_VALUE_COUNT).to_bytes()
        );
        // Wrong-key proofs still have a well-formed transcript and equation.
        // Check all nine pairings, not only the three successful verifications.
        for selected in corpus::VERSIONS {
            compare_equation_with_instances(
                selected,
                &fixture.statements,
                &fixture.instances,
                fixture.proof,
                <Fp>::from_u64(47),
            );
        }
    }
    for (mask, expected) in [0, 44, 44, 74, 44, 74, 47, 77].into_iter().enumerate() {
        assert_eq!(runtime.vk_indices[mask].len(), expected);
        assert!(
            runtime.vk_indices[mask]
                .windows(2)
                .all(|pair| pair[0] < pair[1])
        );
    }
}

#[test]
#[cfg_attr(debug_assertions, ignore = "reference equations require --release")]
fn transcript_and_equations_match_reference_for_valid_and_invalid_proofs() {
    for version in corpus::VERSIONS {
        let fixture = corpus::small(version, 2);

        compare(&fixture, fixture.proof, <Fp>::ONE);
        // Compare equations after changing each scalar public input and flag
        // in each Action, using independently decoded instance columns.
        for action in 0..fixture.instances.len() {
            for row in [0, 3, 6, 7, 8, 9] {
                if row >= fixture.instances[action].len() {
                    continue;
                }
                let mut instances = fixture.instances.clone();
                instances[action][row] = if row >= 7 {
                    pallas::Base::from(1) - instances[action][row]
                } else {
                    instances[action][row] + pallas::Base::from(1)
                };
                let altered = corpus::from_instances(version, instances, fixture.proof);
                compare(&altered, fixture.proof, <Fp>::from_u64(37));
            }
        }
        let (points, scalars) = slots(fixture.statements.len());
        assert_eq!((points.len() + scalars.len()) * 32, fixture.proof.len());
        for offset in points {
            let mut altered = fixture.proof.to_vec();
            assert_ne!(
                &altered[offset..offset + 32],
                &VestaPoint::GENERATOR.to_bytes()
            );
            altered[offset..offset + 32].copy_from_slice(&VestaPoint::GENERATOR.to_bytes());
            compare(&fixture, &altered, <Fp>::from_u64(41));

            assert_eq!(
                crate::verify_proofs(
                    &[VerificationRequest::new(version, &fixture.statements, &altered).unwrap()],
                    &mut no_rng
                ),
                Err(Error::InvalidProof)
            );
            for encoding in [[0; 32], [0xff; 32]] {
                altered[offset..offset + 32].copy_from_slice(&encoding);

                assert_eq!(
                    crate::verify_proofs(
                        &[
                            VerificationRequest::new(version, &fixture.statements, &altered)
                                .unwrap()
                        ],
                        &mut no_rng
                    ),
                    Err(Error::InvalidProof)
                );
            }
        }
        for offset in scalars {
            let mut altered = fixture.proof.to_vec();
            let value = <Fp>::from_bytes(altered[offset..offset + 32].try_into().unwrap()).unwrap();
            altered[offset..offset + 32].copy_from_slice(&value.add(&<Fp>::ONE).to_bytes());
            compare(&fixture, &altered, <Fp>::from_u64(43));

            assert_eq!(
                crate::verify_proofs(
                    &[VerificationRequest::new(version, &fixture.statements, &altered).unwrap()],
                    &mut no_rng
                ),
                Err(Error::InvalidProof)
            );
            altered[offset..offset + 32].fill(0xff);

            assert_eq!(
                crate::verify_proofs(
                    &[VerificationRequest::new(version, &fixture.statements, &altered).unwrap()],
                    &mut no_rng
                ),
                Err(Error::InvalidProof)
            );
        }
    }
}

#[test]
#[cfg_attr(debug_assertions, ignore = "reference equations require --release")]
fn arbitrary_canonical_transcripts_and_large_historical_equations() {
    let mut rng = ChaCha20Rng::from_seed([113; 32]);
    for version in corpus::VERSIONS {
        for count in [1, 2, 3, 65, 128] {
            let fixture = if version == CircuitVersion::PostNu6_3 {
                let original = corpus::current(1);
                corpus::from_instances(
                    version,
                    vec![original.instances[0].clone(); count],
                    original.proof,
                )
            } else {
                let fixture = corpus::historical(version, count);
                compare(&fixture, fixture.proof, <Fp>::from_u64(53));
                fixture
            };
            let (points, scalars) = slots(count);
            for _ in 0..2 {
                let mut bytes = vec![0; (points.len() + scalars.len()) * 32];
                for &offset in &points {
                    let point = &VK_COMMITMENTS[rng.next_u64() as usize % VK_COMMITMENTS.len()];
                    bytes[offset..offset + 32].copy_from_slice(&point.to_bytes());
                }
                for &offset in &scalars {
                    bytes[offset..offset + 32]
                        .copy_from_slice(&pallas::Base::random(&mut rng).to_repr());
                }
                compare(&fixture, &bytes, <Fp>::from_u64(rng.next_u64()));

                assert_eq!(
                    crate::verify_proofs(
                        &[VerificationRequest::new(version, &fixture.statements, &bytes).unwrap()],
                        &mut no_rng
                    ),
                    Err(Error::InvalidProof)
                );
            }
        }
    }
}

#[test]
fn randomized_batch_prevents_cancelling_invalid_responses_across_versions() {
    let first = corpus::VERSIONS.map(|v| corpus::small(v, 1));
    let second = corpus::VERSIONS.map(|v| corpus::small(v, 2));
    for a in &first {
        for b in &second {
            let change = |proof: &[u8], delta: Fp| {
                let mut bytes = proof.to_vec();
                let offset = bytes.len() - 32;
                let f = <Fp>::from_bytes(bytes[offset..].try_into().unwrap()).unwrap();
                bytes[offset..].copy_from_slice(&f.add(&delta).to_bytes());
                bytes
            };
            let plus = change(a.proof, <Fp>::ONE);
            let minus = change(b.proof, <Fp>::ONE.neg());
            let requests = [
                VerificationRequest::new(a.version, &a.statements, &plus).unwrap(),
                VerificationRequest::new(b.version, &b.statements, &minus).unwrap(),
            ];
            for request in requests {
                assert_eq!(
                    crate::verify_proofs(&[request], &mut no_rng),
                    Err(Error::InvalidProof)
                );
            }
            // Deliberately broken equal weights expose the cancellation; a
            // fresh independent non-unit weight must reject the same pair.
            let mut words = 0;
            assert_eq!(
                crate::verify_proofs(&requests, &mut || {
                    let word = u64::from(words % 8 == 0);
                    words += 1;
                    Ok(word)
                }),
                Ok(())
            );
            assert_eq!(words, 8);
            assert_eq!(
                crate::verify_proofs(&requests, &mut || Ok(67)),
                Err(Error::InvalidProof)
            );
        }
    }
}

#[test]
fn every_version_union_matches_affine_msm_and_merges() {
    let runtime = VerifierRuntime::get();
    for mask in 1..VERSION_MASKS {
        let mut combined = Equation::new();
        let mut expected = VestaProjective::IDENTITY;
        for version in corpus::VERSIONS {
            if mask & (1 << version.index()) == 0 {
                continue;
            }
            let mut equation = Equation::new();
            equation.versions = 1 << version.index();
            for (column, &index) in VK_DATA.columns[version.index()].iter().enumerate() {
                let scalar =
                    <Fp>::from_u64((column + 1 + version.index() * VK_COLUMN_COUNT) as u64).neg();
                equation.fixed[FIXED_OFFSET + index as usize] = scalar;
                expected =
                    expected.add(&VK_COMMITMENTS[index as usize].to_projective().mul(&scalar));
            }
            combined.merge(equation);
        }
        assert_eq!(usize::from(combined.versions), mask);
        assert_eq!(
            runtime
                .evaluate(&combined, &mut MsmWorkspace::new())
                .unwrap()
                .to_point()
                .to_bytes(),
            expected.to_point().to_bytes()
        );
    }
}

#[test]
fn historical_fixture_files_are_pinned() {
    use sha2::{Digest, Sha256};
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/legacy");
    let manifest = include_str!("../../../tests/fixtures/legacy/manifest.json");
    for version in ["fixed", "insecure"] {
        for case in ["1", "2", "3", "65", "128", "flags-0", "flags-1", "flags-2"] {
            for extension in ["instances", "proof"] {
                let name = format!("{version}-{case}.{extension}");
                let digest = hex::encode(Sha256::digest(std::fs::read(root.join(&name)).unwrap()));
                assert!(
                    manifest.contains(&format!("\"{name}\": \"{digest}\"")),
                    "fixture digest changed: {name}"
                );
            }
        }
    }
}

#[test]
fn mixed_scratch_is_released_after_success_and_failure() {
    if tuning::WORKSPACE != WorkspaceRetention::Discard {
        return;
    }
    let fixtures = corpus::VERSIONS.map(|version| corpus::small(version, 2));
    let requests: Vec<_> = fixtures
        .iter()
        .cycle()
        .take(16)
        .map(corpus::Fixture::request)
        .collect();
    assert_eq!(crate::verify_proofs(&requests, &mut || Ok(71)), Ok(()));
    for (index, fixture) in fixtures.iter().enumerate() {
        let mut altered = fixture.proof.to_vec();
        let offset = altered.len() - 32;
        let response = <Fp>::from_bytes(altered[offset..].try_into().unwrap()).unwrap();
        altered[offset..].copy_from_slice(&response.add(&<Fp>::ONE).to_bytes());
        let mut batch = requests.clone();
        batch[index] =
            VerificationRequest::new(fixture.version, &fixture.statements, &altered).unwrap();
        assert_eq!(
            crate::verify_proofs(&batch, &mut || Ok(71)),
            Err(Error::InvalidProof)
        );
        assert!(VerifierRuntime::get().idle.lock().unwrap().is_none());
    }
    assert_eq!(crate::verify_proofs(&requests, &mut || Ok(71)), Ok(()));
    assert!(VerifierRuntime::get().idle.lock().unwrap().is_none());
}

#[test]
#[ignore = "manual homogeneous and mixed-version benchmark; run with --nocapture"]
fn benchmark_versions() {
    use std::{hint::black_box, time::Instant};
    let fixtures = corpus::VERSIONS.map(|version| corpus::small(version, 2));
    let repetitions = 100;
    for count in [1, 2, 16, 64] {
        for version in corpus::VERSIONS {
            let requests = vec![fixtures[version.index()].request(); count];
            let mut rng = ChaCha20Rng::from_seed([89; 32]);
            let mut run =
                || crate::verify_proofs(black_box(&requests), &mut || Ok(rng.next_u64())).unwrap();
            run();
            let start = Instant::now();
            for _ in 0..repetitions {
                run();
            }
            eprintln!(
                "{version:?} count={count} ns={}",
                start.elapsed().as_nanos() / repetitions
            );
        }
        let requests: Vec<_> = fixtures
            .iter()
            .cycle()
            .take(count)
            .map(corpus::Fixture::request)
            .collect();
        let partitions = corpus::VERSIONS.map(|v| {
            requests
                .iter()
                .copied()
                .filter(|r| r.version == v)
                .collect::<Vec<_>>()
        });
        let mut rng = ChaCha20Rng::from_seed([97; 32]);
        let start = Instant::now();
        for _ in 0..repetitions {
            crate::verify_proofs(black_box(&requests), &mut || Ok(rng.next_u64())).unwrap();
        }
        let mixed = start.elapsed().as_nanos() / repetitions;
        let start = Instant::now();
        for _ in 0..repetitions {
            for partition in &partitions {
                crate::verify_proofs(black_box(partition), &mut || Ok(rng.next_u64())).unwrap();
            }
        }
        eprintln!(
            "mixed count={count} ns={mixed} separate_ns={}",
            start.elapsed().as_nanos() / repetitions
        );
    }
}
