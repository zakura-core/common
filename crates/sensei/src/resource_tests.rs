//! Caller-owned preparation, scratch reuse, and execution contracts.

use crate::native::{PreparedProver, ProverWorkspace, srs::PreparedSrs};
use crate::test_codec::{FIXTURES, Fixture, TapeRng, decode_iwpr};
use udon::exec::{Executor, SerialExecutor, TaskBudget};

pub(crate) struct PoolExecutor<'a>(pub(crate) &'a rayon::ThreadPool);
impl Executor for PoolExecutor<'_> {
    fn join<L, R, A, B>(&self, left: L, right: R) -> (A, B)
    where
        L: FnOnce() -> A + Send,
        R: FnOnce() -> B + Send,
        A: Send,
        B: Send,
    {
        self.0.install(|| rayon::join(left, right))
    }
}

#[test]
#[cfg_attr(debug_assertions, ignore = "proof replay requires --release")]
fn caller_pool_and_reused_workspace_preserve_proofs() {
    fn shareable<T: Send + Sync>() {}
    shareable::<PreparedProver>();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(3)
        .build()
        .unwrap();
    let executor = PoolExecutor(&pool);
    let budget = TaskBudget::new(3).unwrap();
    let prepared = PreparedProver::new(PreparedSrs::shared(), &executor, budget).unwrap();
    let mut workspace = ProverWorkspace::new();

    check_dirty_workspace_reuse(&prepared, &mut workspace, &executor, budget);
    check_nested_execution(&prepared);
    check_simultaneous_proofs(&prepared, &executor);
}

fn check_dirty_workspace_reuse(
    prepared: &PreparedProver,
    workspace: &mut ProverWorkspace,
    executor: &PoolExecutor<'_>,
    budget: TaskBudget,
) {
    for (iteration, index) in [0, 1, 1, 0, 1].into_iter().enumerate() {
        workspace.ipa.dirty();
        workspace.lookup.dirty();
        workspace.buffers.dirty(udon::field::Fp::from_u64(19));
        workspace.fft.buffers.dirty(udon::field::Fp::from_u64(23));
        let fixture = &FIXTURES[index];
        let request = decode_iwpr(fixture.request).unwrap();
        if iteration == 2 {
            check_failed_proof(prepared, &request, fixture, workspace, executor, budget);
        }
        assert_eq!(request.action_count(), fixture.actions);
        let mut rng = TapeRng::new(fixture.tape);
        let before = workspace.msm.capacities();
        let ipa_before = workspace.ipa.capacities();
        let fft_before = workspace.fft.capacities();
        let buffers_before = workspace.buffers.inventory();
        let lookup_before = workspace.lookup.inventory();
        let proof = prepared
            .create_proof(&request, &mut rng, workspace, executor, budget)
            .unwrap();
        assert_eq!(proof, fixture.proof);
        assert_eq!(rng.words_consumed(), fixture.rng_words);
        if iteration > 1 {
            assert_eq!(workspace.msm.capacities(), before);
            assert_eq!(workspace.fft.capacities(), fft_before);
            assert_eq!(workspace.ipa.capacities(), ipa_before);
            assert_eq!(workspace.buffers.inventory(), buffers_before);
            assert_eq!(workspace.lookup.inventory(), lookup_before);
        }
    }
}

fn check_failed_proof(
    prepared: &PreparedProver,
    request: &crate::ProvingRequest,
    fixture: &Fixture,
    workspace: &mut ProverWorkspace,
    executor: &PoolExecutor<'_>,
    budget: TaskBudget,
) {
    let mut actions = request.actions().to_vec();
    actions[0].witness.v_old = 1;
    let invalid = crate::ProvingRequest::new(actions).unwrap();
    assert!(
        prepared
            .create_proof(
                &invalid,
                &mut TapeRng::new(fixture.tape),
                workspace,
                executor,
                budget
            )
            .is_err()
    );
}

fn check_nested_execution(prepared: &PreparedProver) {
    // Enter the selected pool before proving to exercise nested joins even
    // when only one worker can make progress.
    for workers in [
        1,
        2,
        4,
        std::thread::available_parallelism().map_or(1, usize::from),
    ] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .build()
            .unwrap();
        let executor = PoolExecutor(&pool);
        let budget = TaskBudget::new(workers).unwrap();
        for fixture in FIXTURES {
            let request = decode_iwpr(fixture.request).unwrap();
            let mut rng = TapeRng::new(fixture.tape);
            let proof = pool
                .install(|| {
                    prepared.create_proof(
                        &request,
                        &mut rng,
                        &mut ProverWorkspace::new(),
                        &executor,
                        budget,
                    )
                })
                .unwrap();
            assert_eq!(proof, fixture.proof);
            assert_eq!(rng.words_consumed(), fixture.rng_words);
        }
    }
}

fn check_simultaneous_proofs(prepared: &PreparedProver, executor: &PoolExecutor<'_>) {
    // One immutable preparation supports two simultaneous proofs with distinct
    // workspaces and RNGs, each owning its serial task allowance.
    executor.join(|| replay(prepared, 0), || replay(prepared, 1));
}

fn replay(prepared: &PreparedProver, index: usize) {
    let fixture = &FIXTURES[index];
    let request = decode_iwpr(fixture.request).unwrap();
    let mut rng = TapeRng::new(fixture.tape);
    let proof = prepared
        .create_proof(
            &request,
            &mut rng,
            &mut ProverWorkspace::new(),
            &SerialExecutor,
            TaskBudget::SERIAL,
        )
        .unwrap();
    assert_eq!(proof, fixture.proof);
    assert_eq!(rng.words_consumed(), fixture.rng_words);
}

#[test]
#[cfg_attr(debug_assertions, ignore = "large proof replay requires --release")]
fn large_windows_bound_frontiers_and_recover_for_small_and_failed_requests() {
    use rand::{Rng, SeedableRng};
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(3)
        .build()
        .unwrap();
    let executor = PoolExecutor(&pool);
    let budget = TaskBudget::new(3).unwrap();
    let prepared = PreparedProver::new(PreparedSrs::shared(), &executor, budget).unwrap();
    let action = decode_iwpr(FIXTURES[0].request).unwrap().actions()[0].clone();
    let mut workspace = ProverWorkspace::new();
    let mut first_frontier = None;
    for count in [17, 65, 1] {
        let request = crate::ProvingRequest::new(vec![action.clone(); count]).unwrap();
        let mut rng = rand_chacha::ChaCha20Rng::from_seed([count as u8; 32]);
        let proof = prepared
            .create_proof(
                &request,
                &mut || Ok(rng.next_u64()),
                &mut workspace,
                &executor,
                budget,
            )
            .unwrap();
        assert_eq!(proof.len(), request.shape.proof_bytes);
        let fft = workspace.fft.capacities();
        let msm = workspace.msm.capacities();
        let frontier = (fft[0], fft[1], msm[0], msm[1], msm[2]);
        if let Some(expected) = first_frontier {
            assert_eq!(frontier, expected);
        } else {
            first_frontier = Some(frontier);
        }
        assert_eq!(
            fft[0],
            crate::sizing::ACTION_WINDOW * (sensei_shared::ADVICE_COLUMNS + 6)
        );
        assert!(msm[0] <= 2 * budget.get() * 32);
    }
    let mut invalid = action;
    invalid.witness.v_old = 1;
    let invalid = crate::ProvingRequest::new(vec![invalid; 65]).unwrap();
    let mut rng = rand_chacha::ChaCha20Rng::from_seed([9; 32]);
    assert!(
        prepared
            .create_proof(
                &invalid,
                &mut || Ok(rng.next_u64()),
                &mut workspace,
                &executor,
                budget
            )
            .is_err()
    );
    let fixture = &FIXTURES[0];
    assert_eq!(
        prepared
            .create_proof(
                &decode_iwpr(fixture.request).unwrap(),
                &mut TapeRng::new(fixture.tape),
                &mut workspace,
                &executor,
                budget
            )
            .unwrap(),
        fixture.proof
    );
}

#[test]
#[cfg_attr(debug_assertions, ignore = "proof replay requires --release")]
fn consumers_start_before_unrelated_producers_finish() {
    let prepared =
        PreparedProver::new(PreparedSrs::shared(), &SerialExecutor, TaskBudget::SERIAL).unwrap();
    crate::native::stage_timing::enable();
    replay(&prepared, 0);
    let timings = crate::native::stage_timing::take().unwrap();
    let quotient = crate::native::stage_timing::take_quotient().unwrap();
    crate::native::stage_timing::take_witness().unwrap();
    // Only phases whose generator bank exceeds 32 points can overlap.
    // The exact count also depends on the selected table's MSM pass sizes.
    let mut start = 0;
    let mut expected = 0;
    for end in crate::tuning::IPA_FOLD_ENDS {
        if (sensei_shared::N >> start) > 32 {
            expected += end - start;
        }
        start = end;
    }
    assert!(timings.ipa_early_rounds > 0 && timings.ipa_early_rounds <= expected);
    if crate::tuning::IPA_FOLD_ENDS == [3, 6, 11] {
        assert_eq!(timings.ipa_early_rounds, 6);
    }
    for (edge, count) in ["expansion to fold", "fold to inverse", "inverse to MSM"]
        .into_iter()
        .zip(quotient.early_consumers)
    {
        assert!(count > 0, "{edge} was a full barrier");
    }
}
