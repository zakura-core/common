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
fn instance_commitments_match_a_lagrange_msm_reference() {
    let runtime = VerifierRuntime::get();
    let (statements, _) = fixture();
    // The archived statements share one anchor (the shared-term path); flip
    // the second anchor for the per-statement fallback.
    let mut distinct = statements.clone();
    let mut anchor = [0; 32];
    anchor[0] = 99;
    distinct[1].anchor = crate::primitives::Fp::from_bytes(anchor).unwrap();
    for statements in [statements, distinct] {
        let natives: Vec<_> = statements.iter().map(|s| s.native()).collect();
        for instance_len in [9, 10] {
            let mut reader = Reader::new(&[]);
            absorb_instances(
                &mut reader,
                &natives,
                instance_len,
                &runtime.instance_generators,
            )
            .unwrap();
            let got = reader.challenge();
            // The fixed-base path must absorb exactly what per-statement
            // multiplications over the same Lagrange prefix produce.
            let mut reference = Reader::new(&[]);
            for s in &natives {
                let mut sum = PREPARED_POINTS.blind_generator.to_projective();
                for (base, value) in PREPARED_POINTS.lagrange_bases[..instance_len]
                    .iter()
                    .zip(&s[..instance_len])
                {
                    sum = sum.add(&base.to_point().mul_projective(value));
                }
                reference.common_point(&sum.to_point()).unwrap();
            }
            assert_eq!(got.to_bytes(), reference.challenge().to_bytes());
        }
    }
}

#[test]
fn prefetch_decodes_every_point_of_an_archived_proof() {
    use super::super::protocol::transcript_encoding::{ACTION_POINTS, FIXED_POINTS};
    let (statements, proof) = fixture();
    let points = prefetch_points(&proof, statements.len()).expect("canonical proof prefetches");
    assert_eq!(
        points.len(),
        FIXED_POINTS + ACTION_POINTS * statements.len()
    );
    // Truncated proofs and corrupted encodings fail prefetch.
    assert!(prefetch_points(&proof[..proof.len() - 1], statements.len()).is_none());
    let mut corrupted = proof.clone();
    corrupted[..32].fill(0xff);
    assert!(prefetch_points(&corrupted, statements.len()).is_none());
    // Full verification runs through the prefetched reader (whose debug
    // assertion checks every point against its proof bytes).
    let request =
        VerificationRequest::new(crate::CircuitVersion::PostNu6_3, &statements, &proof).unwrap();
    assert_eq!(crate::verify_proofs(&[request], &mut no_rng), Ok(()));
}

#[test]
fn malformed_points_are_rejected_before_equation_assembly() {
    use super::super::protocol::transcript_encoding::{POINT_BYTES, point_runs};
    let runtime = VerifierRuntime::get();
    for version in corpus::VERSIONS {
        let fixture = corpus::small(version, 2);
        for (offset, count) in point_runs(fixture.statements.len()).unwrap() {
            // A bad point at the end of each run must not cause the preceding
            // points to be read again into the verification equation.
            let offset = offset + (count - 1) * POINT_BYTES;
            for encoding in [[0; POINT_BYTES], [0xff; POINT_BYTES]] {
                let mut proof = fixture.proof.to_vec();
                proof[offset..offset + POINT_BYTES].copy_from_slice(&encoding);
                let request =
                    VerificationRequest::new(version, &fixture.statements, &proof).unwrap();
                let mut equation = Equation::new();
                assert_eq!(
                    equation.proof(&request, <Fp>::ONE, &runtime.instance_generators),
                    Err(Error::InvalidProof)
                );
                assert_eq!(equation.versions, 0);
                assert!(equation.points.is_empty());
                assert!(equation.scalars.is_empty());
            }
        }
    }
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
        PreparedAffinePoint::from_affine(&PREPARED_POINTS.coefficient_bases[17]),
        PreparedAffinePoint::from_affine(&VK_COMMITMENTS[3]),
        PreparedAffinePoint::from_affine(&PREPARED_POINTS.lagrange_bases[5]),
    ];
    dense.scalars = vec![<Fp>::ZERO, <Fp>::ONE.neg(), step];

    for equation in [Equation::new(), boundaries, dense] {
        let actual = runtime
            .evaluate(&equation, &mut MsmWorkspace::new())
            .unwrap();
        assert_eq!(actual.to_point(), affine_reference(&equation).to_point());
    }
}

/// The equation as one serial MSM over plain affine bases: independent of the
/// verifier's input split, slicing, prepared banks, and workspace reuse.
fn affine_reference(equation: &Equation) -> VestaProjective {
    let equation_affine: Vec<_> = equation
        .points
        .iter()
        .map(PreparedAffinePoint::to_affine)
        .collect();
    let bases: Vec<_> = PREPARED_POINTS
        .coefficient_bases
        .iter()
        .chain(VK_COMMITMENTS)
        .chain(&PREPARED_POINTS.lagrange_bases[..INSTANCE_VALUE_COUNT])
        .chain([
            &PREPARED_POINTS.blind_generator,
            &PREPARED_POINTS.ipa_generator,
        ])
        .chain(&equation_affine)
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
    expected[0]
}

/// Accept/reject tests only show that a valid batch still sums to the
/// identity. This compares the sliced final MSM's value for nonzero equations
/// of every slicing regime, on the three workspace states `verify` can lease:
/// fresh, reused across other shapes, and provisioned but never executed.
/// Slice counts follow the pool: a single-worker pool exercises one slice.
#[test]
fn sliced_final_msm_matches_an_affine_msm_on_every_workspace_state() {
    let runtime = VerifierRuntime::get();
    let step = <Fp>::from_u64(13).invert().unwrap();
    let floor = tuning::VERIFY_MSM_SLICE_POINTS;
    let mut reused = MsmWorkspace::new();
    for (round, count) in [
        0,
        1,
        floor - 1,
        floor,
        2 * floor - 1,
        2 * floor,
        2 * floor + 1,
        5000,
        3,
        9000,
        77,
    ]
    .into_iter()
    .enumerate()
    {
        let mut equation = Equation::new();
        equation.versions = (VERSION_MASKS - 1) as u8;
        for (index, scalar) in equation.fixed.iter_mut().enumerate() {
            *scalar = step.mul(&<Fp>::from_u64((index + round) as u64 + 1));
        }
        equation.points = (0..count)
            .map(|index| {
                PreparedAffinePoint::from_affine(
                    &PREPARED_POINTS.coefficient_bases[(7 * index + round) % N],
                )
            })
            .collect();
        equation.scalars = (0..count)
            .map(|index| {
                step.mul(&<Fp>::from_u64((31 * index + round) as u64 + 5))
                    .neg()
            })
            .collect();
        let expected = affine_reference(&equation);
        assert!(!expected.is_identity());
        let mut provisioned = MsmWorkspace::new();
        runtime.provision_workspace(&mut provisioned, 2 * count.max(1));
        for (state, workspace) in [
            ("fresh", &mut MsmWorkspace::new()),
            ("reused", &mut reused),
            ("provisioned", &mut provisioned),
        ] {
            assert_eq!(
                runtime.evaluate(&equation, workspace).unwrap().to_point(),
                expected.to_point(),
                "{state} workspace, {count} points"
            );
        }
    }
    // A point without its scalar is an internal fault, never a shorter sum.
    let mut uneven = Equation::new();
    uneven.points = vec![PreparedAffinePoint::from_affine(&VestaAffine::GENERATOR); 2 * floor];
    uneven.scalars = vec![<Fp>::ONE; floor];
    assert_eq!(
        runtime.evaluate(&uneven, &mut MsmWorkspace::new()).err(),
        Some(Error::InternalInvariant)
    );
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
    equation
        .proof(
            &VerificationRequest::new(version, statements, proof).unwrap(),
            weight,
            &runtime.instance_generators,
        )
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

/// The pool invariants every verification path must restore: bounded slot
/// counts and per-entry retained capacities within their tuning ceilings.
/// Shared with the version matrix; the pools are process-global, so these are
/// invariant checks rather than exact-occupancy assertions.
pub(super) fn assert_scratch_pools_bounded() {
    let scratch = &VerifierRuntime::get().scratch;
    assert!(tuning::VERIFIER_EQUATION_SLOTS.contains(&scratch.equation_slots));
    assert!(tuning::VERIFIER_WORKSPACE_SLOTS.contains(&scratch.workspace_slots));
    let equations = lock(&scratch.equations);
    assert!(equations.len() <= scratch.equation_slots);
    for equation in equations.iter() {
        assert!(equation.retained_bytes() <= tuning::VERIFIER_EQUATION_MAX_BYTES);
        assert!(equation.points.is_empty() && equation.scalars.is_empty());
        assert_eq!(equation.versions, 0);
    }
    drop(equations);
    let workspaces = lock(&scratch.workspaces);
    assert!(workspaces.len() <= scratch.workspace_slots);
    for workspace in workspaces.iter() {
        assert!(workspace.retained_bytes() <= tuning::VERIFIER_WORKSPACE_MAX_BYTES);
    }
}

#[test]
fn scratch_pool_slots_follow_the_worker_budget() {
    let equations = tuning::VERIFIER_EQUATION_SLOTS;
    let workspaces = tuning::VERIFIER_WORKSPACE_SLOTS;
    for budget in [1, 2, 8, 16, 24, 32, 64, 128] {
        let slots = tuning::verifier_equation_slots(budget);
        assert!(equations.contains(&slots));
        assert!(
            slots >= budget.min(*equations.end()),
            "one batch's chunks fit"
        );
        assert!(workspaces.contains(&tuning::verifier_workspace_slots(budget)));
    }
    assert_eq!(tuning::verifier_equation_slots(16), 32);
    assert_eq!(tuning::verifier_workspace_slots(16), 4);
    assert_eq!(
        tuning::verifier_workspace_slots(32),
        (32 / tuning::VERIFIER_WORKSPACE_WORKERS_PER_SLOT)
            .clamp(*workspaces.start(), *workspaces.end())
    );
    // Monotone in the budget.
    let mut last = (0, 0);
    for budget in 1..=256 {
        let next = (
            tuning::verifier_equation_slots(budget),
            tuning::verifier_workspace_slots(budget),
        );
        assert!(next.0 >= last.0 && next.1 >= last.1);
        last = next;
    }
}

#[test]
fn bounded_pools_survive_success_and_failure() {
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
        assert_scratch_pools_bounded();
    }
    let request =
        VerificationRequest::new(crate::CircuitVersion::PostNu6_3, &statements, &proof).unwrap();
    assert_eq!(crate::verify_proofs(&[request], &mut no_rng), Ok(()));
    assert_scratch_pools_bounded();
}

#[test]
fn scratch_pool_returns_reset_entries_and_honors_ceilings() {
    let scratch = VerifierScratch::new(16, 4);
    // A used equation returns reset, with its capacity retained for reuse.
    let mut equation = scratch.lease_equation();
    equation.versions = 3;
    equation.fixed[0] = <Fp>::ONE;
    equation
        .points
        .push(PreparedAffinePoint::from_affine(&VestaAffine::GENERATOR));
    equation.scalars.push(<Fp>::ONE);
    scratch.return_equation(equation);
    {
        let pooled = lock(&scratch.equations);
        assert_eq!(pooled.len(), 1);
        assert_eq!(pooled[0].versions, 0);
        assert!(pooled[0].fixed[0].is_zero());
        assert!(pooled[0].points.is_empty());
        assert!(pooled[0].points.capacity() > 0, "capacity is retained");
    }
    let reused = scratch.lease_equation();
    assert!(lock(&scratch.equations).is_empty());
    scratch.return_equation(reused);
    // An entry above the retained-capacity ceiling is dropped, not pooled.
    let mut oversized = scratch.lease_equation();
    oversized
        .scalars
        .reserve(tuning::VERIFIER_EQUATION_MAX_BYTES / size_of::<Fp>() + 1);
    scratch.return_equation(oversized);
    assert!(lock(&scratch.equations).is_empty());
    // A full pool drops further returns instead of growing.
    for _ in 0..scratch.equation_slots + 3 {
        scratch.return_equation(Equation::new());
    }
    assert_eq!(lock(&scratch.equations).len(), scratch.equation_slots);
    for _ in 0..scratch.workspace_slots + 3 {
        scratch.return_workspace(MsmWorkspace::new());
    }
    assert_eq!(lock(&scratch.workspaces).len(), scratch.workspace_slots);
    assert_eq!(
        scratch.max_idle_bytes(),
        16 * tuning::VERIFIER_EQUATION_MAX_BYTES + 4 * tuning::VERIFIER_WORKSPACE_MAX_BYTES
    );
}

#[test]
fn warm_up_scratch_provisions_a_matching_workspace() {
    let runtime = VerifierRuntime::get();
    let (statements, proof) = fixture();
    let request =
        VerificationRequest::new(crate::CircuitVersion::PostNu6_3, &statements, &proof).unwrap();
    let mut combined = Equation::new();
    for weight in 1..5 {
        combined
            .proof(
                &request,
                <Fp>::from_u64(weight),
                &runtime.instance_generators,
            )
            .unwrap();
    }
    let mut workspace = MsmWorkspace::new();
    runtime.provision_workspace(&mut workspace, combined.points.len());
    let provisioned = workspace.retained_bytes();
    assert!(provisioned > 0);
    // The synthetic full-width provisioning shapes match a real batch: the
    // provisioned workspace evaluates it without growing.
    runtime.evaluate(&combined, &mut workspace).unwrap();
    assert_eq!(workspace.retained_bytes(), provisioned);
    // The public entry point keeps the global pools within their bounds and
    // reports the shape it provisioned.
    let plan = crate::warm_up_verifier_scratch(16, 32);
    assert_scratch_pools_bounded();
    assert_eq!(plan.fold_tasks, fold_jobs(runtime.fold_cap(), 16, 32));
    assert_eq!(
        plan.msm_tasks,
        runtime.msm_budget(16 * combined.points.len() / 4).get()
    );
    assert!(plan.retained);
    assert!(plan.workspace_bytes > 0 && plan.equation_bytes > 0);
    assert_eq!(plan.pooled_batches, runtime.scratch.workspace_slots);
    assert_eq!(plan.max_idle_bytes, runtime.scratch.max_idle_bytes());
    assert!(plan.workspace_bytes + plan.equation_bytes <= plan.max_idle_bytes);
    // Warming only reports the pools' policy, with nothing provisioned.
    let warmed = crate::warm_up_verifier_scratch(0, 0);
    assert_scratch_pools_bounded();
    assert_eq!(
        (
            warmed.fold_tasks,
            warmed.msm_tasks,
            warmed.workspace_bytes,
            warmed.equation_bytes
        ),
        (0, 0, 0, 0)
    );
    assert_eq!(
        (
            warmed.pooled_batches,
            warmed.max_idle_bytes,
            warmed.retained
        ),
        (plan.pooled_batches, plan.max_idle_bytes, true)
    );
}

#[test]
fn task_budgets_follow_the_work() {
    // Folding: one chunk per Action floor, bounded by proofs and the cap.
    let floor = tuning::VERIFY_FOLD_MIN_ACTIONS;
    assert_eq!(fold_jobs(16, 1, 1), 1);
    assert_eq!(fold_jobs(16, 1, floor * 16), 1, "a proof is one unit");
    assert_eq!(
        fold_jobs(16, 2, floor - 1),
        1,
        "below one floor stays serial"
    );
    assert_eq!(fold_jobs(16, 8, floor * 4), 4);
    assert_eq!(fold_jobs(16, 128, floor * 128), 16, "capped by the pool");
    assert_eq!(fold_jobs(2, 128, floor * 128), 2);
    assert_eq!(fold_jobs(0, 128, floor * 128), 1, "a zero cap means serial");
    // The final MSM: its fixed segments alone span several term floors.
    let fixed = N + VERIFIER_POINT_COUNT + INSTANCE_VALUE_COUNT;
    let min = tuning::VERIFY_MSM_MIN_TERMS;
    assert_eq!(msm_tasks(32, 0), (fixed / min).clamp(1, 32));
    assert_eq!(msm_tasks(1, 1 << 20), 1);
    assert_eq!(msm_tasks(0, 1 << 20), 1, "a zero cap means serial");
    assert_eq!(
        msm_tasks(usize::MAX, min * 64),
        (fixed + min * 64) / min,
        "large batches scale with their terms"
    );
}

#[test]
#[ignore = "manual cold-call benchmark; one fresh process per measurement, --nocapture"]
fn benchmark_cold_verification() {
    use std::time::Instant;
    let batch: usize = std::env::var("SENSEI_COLD_BATCH")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(64);
    let fixture = corpus::current(2);
    let requests = vec![fixture.request(); batch];
    let scratch = std::env::var_os("SENSEI_COLD_SCRATCH").is_some();
    let start = Instant::now();
    if scratch {
        let plan = crate::warm_up_verifier_scratch(batch, batch * fixture.statements.len());
        println!("plan {plan:?}");
    } else {
        crate::warm_up_verifier();
    }
    let warm = start.elapsed();
    let start = Instant::now();
    crate::verify_proofs(&requests, &mut || Ok(93)).unwrap();
    let first = start.elapsed();
    let start = Instant::now();
    crate::verify_proofs(&requests, &mut || Ok(95)).unwrap();
    let second = start.elapsed();
    println!(
        "cold batch={batch} scratch={scratch} warm_up={warm:?} first={first:?} second={second:?}"
    );
    let pools = &VerifierRuntime::get().scratch;
    let equations = lock(&pools.equations);
    let equation_bytes: usize = equations.iter().map(Equation::retained_bytes).sum();
    let (equation_count, max_equation) = (
        equations.len(),
        equations.iter().map(Equation::retained_bytes).max(),
    );
    drop(equations);
    let workspaces = lock(&pools.workspaces);
    let workspace_bytes: Vec<usize> = workspaces
        .iter()
        .map(MsmWorkspace::retained_bytes)
        .collect();
    println!(
        "pooled equations={equation_count} bytes={equation_bytes} max={max_equation:?} \
         workspaces={} bytes={workspace_bytes:?}",
        workspace_bytes.len()
    );
}

#[test]
#[ignore = "manual concurrent verification benchmark; run with --nocapture under /usr/bin/time -l"]
fn benchmark_concurrent_verification() {
    use std::time::Instant;
    let setting = |name, default| {
        std::env::var(name)
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(default)
    };
    let threads: usize = setting("SENSEI_CONCURRENT", 4);
    let batch: usize = setting("SENSEI_CONCURRENT_BATCH", 32);
    let rounds: usize = setting("SENSEI_CONCURRENT_ROUNDS", 50);
    let fixture = corpus::current(2);
    crate::warm_up_verifier();
    let start = Instant::now();
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                let requests = vec![fixture.request(); batch];
                for _ in 0..rounds {
                    crate::verify_proofs(&requests, &mut || Ok(97)).unwrap();
                }
            });
        }
    });
    let elapsed = start.elapsed();
    println!(
        "concurrent threads={threads} batch={batch} rounds={rounds} \
         total={elapsed:?} per-batch={:.3}ms peak_rss_kib={:?}",
        elapsed.as_secs_f64() * 1e3 / (threads * rounds) as f64,
        peak_rss_kib(),
    );
}

/// The process's peak resident set size from `/proc/self/status` (Linux).
fn peak_rss_kib() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    status
        .lines()
        .find_map(|line| line.strip_prefix("VmHWM:"))
        .and_then(|value| value.trim().trim_end_matches("kB").trim().parse().ok())
}

/// Per-stage attribution of repeated warm verification of one batch shape,
/// for tuning the fold and final-MSM budgets on a given machine.
///
/// Environment: `SENSEI_VERIFY_PROOFS` (64), `SENSEI_VERIFY_ACTIONS` per proof
/// (2; 1 and 2 use the archived current proofs, 128 the migrated 128-Action
/// proof), `SENSEI_VERIFY_REPS` (50), `SENSEI_VERIFY_WARMUP` untimed calls
/// (5), `SENSEI_VERIFY_SCRATCH` (provision the pools for the shape first),
/// `SENSEI_VERIFY_COLD_SCRATCH` (drain both pools before every timed call,
/// measuring the allocate-every-call cost), `SENSEI_VERIFY_TRACE` (one line
/// per call), plus `SENSEI_BENCH_WORKERS` for the pool size.
#[test]
#[ignore = "manual staged verification benchmark; --release --nocapture, one process per worker count"]
fn benchmark_verification_stages() {
    use std::time::Instant;
    let setting = |name: &str, default: usize| -> usize {
        std::env::var(name)
            .ok()
            .map(|value| value.parse().expect("positive integer setting"))
            .unwrap_or(default)
    };
    let proofs = setting("SENSEI_VERIFY_PROOFS", 64);
    let actions = setting("SENSEI_VERIFY_ACTIONS", 2);
    let reps = setting("SENSEI_VERIFY_REPS", 50);
    let warmup = setting("SENSEI_VERIFY_WARMUP", 5);
    let provision = std::env::var_os("SENSEI_VERIFY_SCRATCH").is_some();
    let cold_scratch = std::env::var_os("SENSEI_VERIFY_COLD_SCRATCH").is_some();
    let trace = std::env::var_os("SENSEI_VERIFY_TRACE").is_some();
    assert!(proofs > 0 && reps > 0);
    let fixture = match actions {
        1 | 2 => corpus::current(actions),
        128 => corpus::migrated_current(128, true),
        _ => panic!("SENSEI_VERIFY_ACTIONS must be 1, 2, or 128"),
    };
    let requests = vec![fixture.request(); proofs];
    if provision {
        crate::warm_up_verifier_scratch(proofs, proofs * actions);
    } else {
        crate::warm_up_verifier();
    }
    let workers = crate::worker_budget();
    let runtime = VerifierRuntime::get();
    let drain = || {
        lock(&runtime.scratch.equations).clear();
        lock(&runtime.scratch.workspaces).clear();
    };
    for _ in 0..warmup {
        crate::verify_proofs(&requests, &mut || Ok(93)).unwrap();
    }

    const GROUPS: [&str; 4] = ["srs", "vk", "lagrange", "dynamic"];
    struct Sample {
        total: u128,
        timings: timing::VerifyTimings,
        traffic: [usize; 6],
    }
    let mut samples = Vec::with_capacity(reps);
    for rep in 0..reps {
        if cold_scratch {
            drain();
        }
        let before = runtime.scratch.snapshot();
        timing::enable();
        let started = Instant::now();
        crate::verify_proofs(&requests, &mut || Ok(93)).unwrap();
        let total = started.elapsed().as_nanos();
        let timings = timing::take().expect("attributed verification");
        let after = runtime.scratch.snapshot();
        let traffic = [
            after.equation_misses - before.equation_misses,
            after.equation_ceiling_drops - before.equation_ceiling_drops,
            after.equation_full_drops - before.equation_full_drops,
            after.workspace_misses - before.workspace_misses,
            after.workspace_ceiling_drops - before.workspace_ceiling_drops,
            after.workspace_full_drops - before.workspace_full_drops,
        ];
        if trace {
            let stages: Vec<_> = timing::NAMES
                .iter()
                .zip(timings.elapsed_ns)
                .map(|(name, ns)| format!("{name}={ns}"))
                .collect();
            println!(
                "SENSEI_VERIFY_TRACE rep={rep} total={total} {} workspace_after={} traffic={traffic:?}",
                stages.join(" "),
                timings.facts.workspace_after,
            );
        }
        samples.push(Sample {
            total,
            timings,
            traffic,
        });
    }

    fn median(values: &mut [u128]) -> u128 {
        values.sort_unstable();
        values[values.len() / 2]
    }
    fn p90(values: &mut [u128]) -> u128 {
        values.sort_unstable();
        values[values.len() * 9 / 10]
    }
    let collect = |f: &dyn Fn(&Sample) -> u128| -> Vec<u128> { samples.iter().map(f).collect() };
    let stage = |index: usize| -> Vec<u128> { collect(&|s| s.timings.elapsed_ns[index]) };
    let stages: Vec<_> = timing::NAMES
        .iter()
        .enumerate()
        .map(|(index, name)| format!("{name}={}", median(&mut stage(index))))
        .collect();
    println!(
        "SENSEI_T_VERIFY_NS workers={workers} proofs={proofs} actions={} reps={reps} total={} {}",
        proofs * actions,
        median(&mut collect(&|s| s.total)),
        stages.join(" "),
    );
    println!(
        "SENSEI_T_VERIFY_P90_NS total={} fold={} msm_execute={}",
        p90(&mut collect(&|s| s.total)),
        p90(&mut stage(timing::Stage::Fold as usize)),
        p90(&mut stage(timing::Stage::MsmExecute as usize)),
    );
    let facts = &samples[0].timings.facts;
    println!(
        "SENSEI_VERIFY_FOLD jobs={} chunk={} tasks={} sum_ns={} max_ns={} \
         prefetch_tasks={} prefetch_sum_ns={} prefetch_max_ns={}",
        facts.fold_jobs,
        facts.fold_chunk,
        samples[0].timings.fold.count,
        median(&mut collect(&|s| s.timings.fold.sum_ns.into())),
        median(&mut collect(&|s| s.timings.fold.max_ns.into())),
        samples[0].timings.prefetch.count,
        median(&mut collect(&|s| s.timings.prefetch.sum_ns.into())),
        median(&mut collect(&|s| s.timings.prefetch.max_ns.into())),
    );
    let groups: Vec<_> = GROUPS
        .iter()
        .zip(&facts.msm_groups)
        .map(|(name, (partitions, slots, grain))| format!("{name}:{partitions}/{slots}/{grain}"))
        .collect();
    let probes: Vec<_> = GROUPS
        .iter()
        .enumerate()
        .map(|(group, name)| {
            let kinds: Vec<_> = timing::MSM_TASK_KINDS
                .iter()
                .enumerate()
                .map(|(kind, token)| {
                    format!(
                        "{}:{}/{}/{}",
                        &token[..1],
                        samples[0].timings.msm[group][kind].count,
                        median(&mut collect(&|s| s.timings.msm[group][kind].sum_ns.into())),
                        median(&mut collect(&|s| s.timings.msm[group][kind].max_ns.into())),
                    )
                })
                .collect();
            format!("{name}={}", kinds.join("|"))
        })
        .collect();
    println!(
        "SENSEI_VERIFY_MSM budget={} workers={} groups={} {}",
        facts.msm_budget,
        facts.msm_workers,
        groups.join(","),
        probes.join(" "),
    );
    let traffic = |index: usize| -> u128 { median(&mut collect(&|s| s.traffic[index] as u128)) };
    println!(
        "SENSEI_VERIFY_SCRATCH workspace_before={} workspace_after={} eq_miss={} eq_ceiling_drop={} \
         eq_full_drop={} ws_miss={} ws_ceiling_drop={} ws_full_drop={} peak_rss_kib={:?}",
        median(&mut collect(&|s| s.timings.facts.workspace_before as u128)),
        median(&mut collect(&|s| s.timings.facts.workspace_after as u128)),
        traffic(0),
        traffic(1),
        traffic(2),
        traffic(3),
        traffic(4),
        traffic(5),
        peak_rss_kib(),
    );
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
