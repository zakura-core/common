use super::*;
#[path = "versions.rs"]
mod versions;
#[cfg(feature = "prover")]
use crate::ProvingRequest;
use crate::primitives::pallas;
use crate::{PublicStatement, verification_corpus as corpus};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

fn scalar(value: &Fp) -> pallas::Base {
    pallas::Base::from_repr(value.to_bytes()).unwrap()
}
#[cfg(feature = "prover")]
fn instances(statements: &[PublicStatement]) -> Vec<Vec<pallas::Base>> {
    statements
        .iter()
        .map(|s| s.native().iter().map(scalar).collect())
        .collect()
}
fn fixture() -> (Vec<PublicStatement>, Vec<u8>) {
    let fixture = corpus::current(2);
    (fixture.statements, fixture.proof.to_vec())
}
fn no_rng() -> Result<u64, crate::RandomnessError> {
    panic!("singleton must not consume randomness")
}

#[test]
fn split_equation_matches_an_affine_msm() {
    let runtime = VerifierRuntime::get();
    assert!(Arc::ptr_eq(&runtime.srs, &PreparedSrs::shared()));
    assert!(Arc::ptr_eq(
        &runtime.codebook,
        &runtime.srs.codebook(tuning::VERIFIER_FIXED_ALPHA_WIDTH),
    ));

    let mut boundaries = Equation::new();
    boundaries.versions = (VERSION_MASKS - 1) as u8;
    for index in [
        0,
        N - 1,
        FIXED_OFFSET,
        FIXED_OFFSET + FIXED_COLUMNS,
        INSTANCE_OFFSET - 1,
        INSTANCE_OFFSET,
        BLIND_GENERATOR_SLOT - 1,
        BLIND_GENERATOR_SLOT,
        IPA_GENERATOR_SLOT,
    ] {
        boundaries.fixed[index] = <Fp>::from_u64(index as u64 + 1).neg();
    }
    let mut dense = Equation::new();
    dense.versions = (VERSION_MASKS - 1) as u8;
    let step = <Fp>::from_u64(13).invert().unwrap();
    for (index, scalar) in dense.fixed.iter_mut().enumerate() {
        *scalar = step.mul(&<Fp>::from_u64(index as u64 + 1));
    }
    dense.points = vec![
        PREPARED_POINTS.coefficient_bases[17],
        VK_COMMITMENTS[3],
        PREPARED_POINTS.lagrange_bases[5],
    ];
    dense.scalars = vec![<Fp>::ZERO, <Fp>::ONE.neg(), step];

    for equation in [Equation::new(), boundaries, dense] {
        let bases: Vec<_> = PREPARED_POINTS
            .coefficient_bases
            .iter()
            .chain(VK_COMMITMENTS)
            .chain(&PREPARED_POINTS.lagrange_bases[..INSTANCE_VALUE_COUNT])
            .chain([
                &PREPARED_POINTS.blind_generator,
                &PREPARED_POINTS.ipa_generator,
            ])
            .chain(&equation.points)
            .copied()
            .collect();
        let scalars: Vec<_> = equation
            .fixed
            .iter()
            .chain(&equation.scalars)
            .copied()
            .collect();
        let mut expected = [VestaProjective::IDENTITY];
        MsmWorkspace::new()
            .prepare(
                &[Input::new(Bases::Affine(&bases), &scalars)],
                udon::exec::TaskBudget::SERIAL,
            )
            .unwrap()
            .execute(&mut expected, &udon::exec::SerialExecutor)
            .unwrap();
        let actual = runtime
            .evaluate(&equation, &mut MsmWorkspace::new())
            .unwrap();
        assert_eq!(actual.to_point(), expected[0].to_point());
    }
}

/// Compare the entire assembled group equation even when it is nonzero. Merely
/// checking that both verifiers reject a corrupted proof would miss differences
/// in claimed evaluations, query order, quotient constraints, or batch weights.
#[cfg(feature = "prover")]
fn compare_equation(statements: &[PublicStatement], proof: &[u8], weight: Fp) {
    compare_equation_with_instances(
        crate::CircuitVersion::PostNu6_3,
        statements,
        &instances(statements),
        proof,
        weight,
    );
}
fn compare_equation_with_instances(
    version: crate::CircuitVersion,
    statements: &[PublicStatement],
    values: &[Vec<pallas::Base>],
    proof: &[u8],
    weight: Fp,
) {
    let mut key = blake2b_simd::Params::new().hash_length(32).to_state();
    key.update(&[version.index() as u8]);
    key.update(proof);
    for column in values {
        for value in column {
            key.update(&value.to_repr());
        }
    }
    key.update(&weight.to_bytes());
    let key: [u8; 32] = key.finalize().as_bytes().try_into().unwrap();
    let expected = captured_equations()
        .get(&key)
        .unwrap_or_else(|| panic!("missing independent equation {}", hex::encode(key)));
    let mut equation = Equation::new();
    let runtime = VerifierRuntime::get();
    runtime
        .executor
        .run(|executor| {
            equation.proof(
                &VerificationRequest::new(version, statements, proof).unwrap(),
                weight,
                &runtime.srs,
                &mut MsmWorkspace::new(),
                Execution::new(executor, runtime.executor.budget()).serial(),
            )
        })
        .unwrap();
    let challenge_count = u32::from_le_bytes(expected[32..36].try_into().unwrap()) as usize;
    assert_eq!(expected.len(), 36 + challenge_count * 32);
    let challenges: Vec<[u8; 32]> = expected[36..]
        .chunks_exact(32)
        .map(|chunk| chunk.try_into().unwrap())
        .collect();
    assert_eq!(
        equation.challenges, challenges,
        "legacy transcript challenges"
    );
    assert_eq!(
        runtime
            .evaluate(&equation, &mut MsmWorkspace::new())
            .unwrap()
            .to_point()
            .to_bytes(),
        expected[..32],
        "legacy weighted group equation"
    );
}

#[test]
#[cfg_attr(debug_assertions, ignore = "proof generation requires --release")]
#[cfg(feature = "prover")]
fn independently_generated_proofs_and_fresh_sensei_proofs() {
    for restricted in [false, true] {
        let fixture = corpus::migrated_current(3, restricted);
        assert_eq!(
            crate::verify_proofs(&[fixture.request()], &mut no_rng),
            Ok(())
        );
        compare_equation(&fixture.statements, fixture.proof, <Fp>::from_u64(47));
    }
    for bytes in [
        crate::test_codec::FIXTURES[0].request,
        crate::test_codec::FIXTURES[1].request,
    ] {
        let request = ProvingRequest::decode_iwpr_for_test(bytes).unwrap();
        let statements: Vec<_> = request
            .actions()
            .iter()
            .map(|a| a.statement.clone())
            .collect();
        let mut rng = ChaCha20Rng::from_seed([53; 32]);
        let proof = crate::create_proof(&request, &mut || Ok(rng.next_u64())).unwrap();
        assert_eq!(
            crate::verify_proofs(
                &[
                    VerificationRequest::new(crate::CircuitVersion::PostNu6_3, &statements, &proof)
                        .unwrap()
                ],
                &mut no_rng
            ),
            Ok(())
        );
    }
}
#[test]
fn archived_current_proofs_have_no_action_count_ceiling() {
    for count in [65, 128] {
        let fixture = corpus::migrated_current(count, true);
        let request = fixture.request();
        assert_eq!(crate::verify_proofs(&[request], &mut no_rng), Ok(()));
        assert_eq!(
            crate::verify_proofs(&[request, request], &mut || Ok(61)),
            Ok(())
        );
    }
}

#[test]
fn discard_releases_verifier_scratch_after_success_and_failure() {
    if tuning::WORKSPACE != WorkspaceRetention::Discard {
        return;
    }
    let (statements, proof) = fixture();
    let mut altered = proof.clone();
    let offset = proof.len() - 32;
    let f = <Fp>::from_bytes(proof[offset..].try_into().unwrap()).unwrap();
    altered[offset..].copy_from_slice(&f.add(&<Fp>::ONE).to_bytes());

    for (bytes, expected) in [(&proof, Ok(())), (&altered, Err(Error::InvalidProof))] {
        let request =
            VerificationRequest::new(crate::CircuitVersion::PostNu6_3, &statements, bytes).unwrap();
        assert_eq!(
            crate::verify_proofs(&[request; 16], &mut || Ok(71)),
            expected
        );
        assert!(VerifierRuntime::get().idle.lock().unwrap().is_none());
    }
    let request =
        VerificationRequest::new(crate::CircuitVersion::PostNu6_3, &statements, &proof).unwrap();
    assert_eq!(crate::verify_proofs(&[request], &mut no_rng), Ok(()));
    assert!(VerifierRuntime::get().idle.lock().unwrap().is_none());
}

#[test]
#[ignore = "manual warm verifier timing; run with --nocapture"]
fn benchmark_verification() {
    use std::{hint::black_box, time::Instant};
    for count in [1, 2] {
        let fixture = corpus::current(count);
        let request = fixture.request();
        crate::verify_proofs(&[request], &mut no_rng).unwrap();
        let start = Instant::now();
        let repetitions = 100;
        for _ in 0..repetitions {
            crate::verify_proofs(black_box(&[request]), &mut no_rng).unwrap();
        }
        eprintln!(
            "actions={count} ns={}",
            start.elapsed().as_nanos() / repetitions
        );
    }
}

/// Records captured from the archived pre-migration Halo2 verifier. The key
/// binds the circuit version, proof bytes, independent instance rows and weight.
fn captured_equations() -> &'static std::collections::BTreeMap<[u8; 32], &'static [u8]> {
    static RECORDS: OnceLock<std::collections::BTreeMap<[u8; 32], &'static [u8]>> = OnceLock::new();
    RECORDS.get_or_init(|| {
        let mut bytes =
            include_bytes!("../../../tests/fixtures/migration/equations.bin").as_slice();
        let mut records = std::collections::BTreeMap::new();
        while !bytes.is_empty() {
            let key = bytes[..32].try_into().unwrap();
            let length = u32::from_le_bytes(bytes[32..36].try_into().unwrap()) as usize;
            let value = &bytes[36..36 + length];
            assert!(
                records.insert(key, value).is_none(),
                "duplicate equation key"
            );
            bytes = &bytes[36 + length..];
        }
        records
    })
}
