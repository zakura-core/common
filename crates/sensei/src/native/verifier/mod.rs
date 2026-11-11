//! Shared verifier for the three pinned Orchard circuits.
//!
//! The keys share the evaluation domain, gate and lookup expressions, query
//! order, and opening protocol. Their circuit differences are encoded in the
//! fixed-column and permutation commitments, so [`quotient_evaluation`] and
//! [`super::protocol::opening`] apply to all three. Each proof's transcript
//! absorbs its selected key's representative to bind it to that circuit.
//!
//! Historical instances populate nine rows; post-NU6.3 adds
//! `disable_cross_address` as the tenth. [`VerificationRequest::new`] requires
//! that flag to be false for historical keys. All remaining rows are zero,
//! allowing [`absorb_instances`] and the final equation to use prefixes of the
//! instance generator bank and the shared Lagrange bank.
//!
//! The `pinned_keys_and_instance_prefixes_match_reference` test checks the
//! shared constraint system, commitments, transcript representatives, and
//! instance prefixes against Orchard. Verification trusts these embedded key
//! facts; adding a version requires checking that it fits this shared structure.
//!
//! Each worker folds complete weighted proof equations. Instance commitments
//! enter the transcript as points, but their equation terms are distributed
//! over the populated Lagrange bases and W. Terms for the SRS and deduplicated
//! verifying-key bank accumulate across all proofs before the single final
//! identity check.
//!
//! After [`VerificationRequest::new`] accepts the request shape, malformed
//! encodings, transcript degeneracies, and a nonidentity final equation report
//! [`Error::InvalidProof`]. These concern a fixed proof/statement transcript;
//! resampling batch weights cannot change its challenges. Only a zero weight
//! sampled independently by [`verify`] requests [`Error::RetryRandomness`].
//! MSM shape failures instead report [`Error::InternalInvariant`]: [`Equation`]
//! and [`VerifierRuntime`] assemble their banks, indices, and output sizes
//! internally. Neither a failed proof equation nor a broken MSM shape
//! establishes a particular private-witness failure. See [`Error`] for caller
//! recovery.
//!
//! # Preparation and scratch
//!
//! See [`super::srs`] for the shared runtime owners and workspace retention
//! policy. [`VerifierRuntime::get`] obtains the shared SRS and executor before
//! preparing its own verifying-key bank in that executor. [`RUNTIME`] retains a
//! successful `VerifierRuntime`; unlike the prover's cell it stores no
//! `Result`. The public [`crate::warm_up_verifier`] contract describes this
//! preparation-only entry point, which acquires no verification scratch;
//! [`crate::warm_up_verifier_scratch`] optionally provisions the bounded idle
//! pools below for an expected batch shape.
//!
//! [`verify`] returns immediately for an empty batch. Otherwise it samples batch
//! weights on the calling thread before runtime initialization, scratch
//! acquisition, or pool entry; a singleton needs no draws. The borrowed
//! [`RandomSource`] stays on that thread, allowing reentrant callbacks, and only
//! the weights reach workers. Task budgets follow the work: [`fold_jobs`] cuts
//! at most one chunk per [`tuning::VERIFY_FOLD_MIN_ACTIONS`] Actions (within
//! [`tuning::VERIFY_FOLD_TASK_CAP`] and the proof count), and a single-chunk
//! batch folds on the calling thread without the pool scheduler. Each chunk
//! leases its [`Equation`] from the runtime's bounded scratch pool; instance
//! commitments walk the runtime's fixed-base generator bank, so chunk folding
//! runs no MSM. After merging successful equations — draining each merged
//! shell back to the pool — [`VerifierRuntime::check`] leases a workspace for
//! the final MSM, whose budget [`msm_tasks`] likewise floors the terms per
//! task at [`tuning::VERIFY_MSM_MIN_TERMS`], and whose transcript points enter
//! as [`slice_len`] slices of at least [`tuning::VERIFY_MSM_SLICE_POINTS`] so
//! that no single input's window count bounds the MSM's parallelism.
//!
//! [`VerifierScratch`] owns both pools, with slot counts
//! [`tuning::verifier_equation_slots`] and [`tuning::verifier_workspace_slots`]
//! derive from the pool's budgets: equations and final-MSM workspaces are
//! returned after success and after reported errors, and dropped instead when
//! a pool is full or an entry's retained capacity exceeds its tuning ceiling,
//! so idle verifier memory never exceeds the slot × ceiling bound that
//! [`warm_up_verifier_scratch`] reports in its [`VerificationPlan`]. Unwinding
//! drops the active scratch without returning it. Concurrent calls beyond the
//! slot counts fall back to fresh, discarded allocations.

use super::{
    commitment::{FixedGenerator, MsmWorkspace},
    executor::PoolExecutor,
    expression_layout::{GATE_CONSTRAINT_COUNT, LOOKUPS},
    programs::{self, Algebra},
    protocol::{
        POINT_SETS,
        opening::{
            ActionPolynomial, FixedPolynomial, OPENING_GROUPS, OPENING_POINTS, OPENING_ROTATIONS,
        },
    },
    queries::{ADVICE_QUERIES, ColumnKind, FIXED_QUERIES, PERMUTATION_COLUMNS},
    srs::{PREPARED_POINTS, PreparedSrs},
    transcript::Reader,
    worker::Execution,
};
use crate::{
    Error, RandomSource, VerificationPlan, VerificationRequest, rng::sample_fp, tuning,
    types::NativeStatement,
};
use sensei_shared::{
    ADVICE_COLUMNS, BLINDING_FACTORS, FIXED_COLUMNS, INSTANCE_VALUE_COUNT, K, N,
    PERMUTATION_CHUNK_LEN, PERMUTATION_COLUMN_COUNT, PERMUTATION_SETS, QUOTIENT_PIECES,
    commitment_tables::Codebook,
    records::{VERIFIER_POINT_COUNT, VERIFIER_VERSION_COUNT, VerifierCommitments},
};
#[cfg(test)]
use std::sync::atomic::AtomicUsize;
use std::sync::{Arc, Mutex, MutexGuard, OnceLock};
use udon::{
    curve::{
        PreparedAffinePoint, Vesta, VestaAffine, VestaPoint, VestaProjective, batch_normalize,
    },
    exec::TaskBudget,
    field::{Fp, Fq, batch_invert},
    msm::{AlphaTable, Bases, Input},
};

// Equation::fixed segments: coefficient SRS 0..FIXED_OFFSET, verifying-key
// commitments FIXED_OFFSET..INSTANCE_OFFSET, instance Lagrange bases
// INSTANCE_OFFSET..BLIND_GENERATOR_SLOT, then the blinding generator W and IPA
// generator U at BLIND_GENERATOR_SLOT and IPA_GENERATOR_SLOT.
const FIXED_OFFSET: usize = N;
const INSTANCE_OFFSET: usize = FIXED_OFFSET + VERIFIER_POINT_COUNT;
const BLIND_GENERATOR_SLOT: usize = INSTANCE_OFFSET + INSTANCE_VALUE_COUNT;
const IPA_GENERATOR_SLOT: usize = BLIND_GENERATOR_SLOT + 1;
const BANK_LEN: usize = IPA_GENERATOR_SLOT + 1;
const LOOKUP_COUNT: usize = LOOKUPS.len();
const ROUNDS: usize = K as usize;

// Stored permutation grand-product evaluations at rotations 0, +1, and
// -(BLINDING_FACTORS + 1). The final set omits the last evaluation.
const PERMUTATION_EVAL_CURRENT: usize = 0;
const PERMUTATION_EVAL_NEXT: usize = 1;
const PERMUTATION_EVAL_LAST: usize = 2;

// Stored lookup slots 0/1 hold the grand product at rotations 0/+1. The
// remaining slots hold the permuted input at 0/-1 and permuted table at 0.
const LOOKUP_EVAL_INPUT_CURRENT: usize = 2;
const LOOKUP_EVAL_INPUT_PREVIOUS: usize = 3;
const LOOKUP_EVAL_TABLE: usize = 4;

crate::static_data::embed_struct! {
    /// Default-blinded commitments and each version's column mapping.
    pub(in crate::native) static VK_DATA: VerifierCommitments =
        artifact_path!(verifier_commitments);
}
const VK_COMMITMENTS: &[VestaAffine; VERIFIER_POINT_COUNT] = &VK_DATA.points;
const VERSION_MASKS: usize = 1 << VERIFIER_VERSION_COUNT;

struct VerifierRuntime {
    srs: Arc<PreparedSrs>,
    vk_bases: Vec<PreparedAffinePoint<Vesta>>,
    vk_indices: [Vec<u32>; VERSION_MASKS],
    // Doubling-free tables over the first ten Lagrange bases, used by
    // absorb_instances; the final equation keeps using the shared SRS bank.
    instance_generators: Vec<FixedGenerator>,
    codebook: Arc<Codebook>,
    executor: &'static PoolExecutor,
    scratch: VerifierScratch,
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    // Recovering a poisoned idle pool permits reuse of its slots; it does not
    // turn a panicking computation into a successful one.
    mutex
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// The bounded idle scratch pools described in the module scratch section.
struct VerifierScratch {
    equations: Mutex<Vec<Equation>>,
    workspaces: Mutex<Vec<MsmWorkspace>>,
    /// Slot counts from [`tuning::verifier_equation_slots`] and
    /// [`tuning::verifier_workspace_slots`] for this pool's budgets.
    equation_slots: usize,
    workspace_slots: usize,
    #[cfg(test)]
    counters: ScratchCounters,
}

/// Test-only pool traffic: leases that found the pool empty (`misses`) and
/// returns dropped for exceeding a ceiling or a full pool.
#[cfg(test)]
#[derive(Default)]
struct ScratchCounters {
    equation_misses: AtomicUsize,
    equation_ceiling_drops: AtomicUsize,
    equation_full_drops: AtomicUsize,
    workspace_misses: AtomicUsize,
    workspace_ceiling_drops: AtomicUsize,
    workspace_full_drops: AtomicUsize,
}

/// A snapshot of [`ScratchCounters`], in the same field order.
#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct ScratchSnapshot {
    pub(super) equation_misses: usize,
    pub(super) equation_ceiling_drops: usize,
    pub(super) equation_full_drops: usize,
    pub(super) workspace_misses: usize,
    pub(super) workspace_ceiling_drops: usize,
    pub(super) workspace_full_drops: usize,
}

#[cfg(test)]
fn count(counter: &AtomicUsize) {
    counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

impl VerifierScratch {
    fn new(equation_slots: usize, workspace_slots: usize) -> Self {
        Self {
            equations: Mutex::new(Vec::new()),
            workspaces: Mutex::new(Vec::new()),
            equation_slots,
            workspace_slots,
            #[cfg(test)]
            counters: ScratchCounters::default(),
        }
    }
    /// The idle retention bound: every slot filled to its ceiling.
    fn max_idle_bytes(&self) -> usize {
        self.workspace_slots * tuning::VERIFIER_WORKSPACE_MAX_BYTES
            + self.equation_slots * tuning::VERIFIER_EQUATION_MAX_BYTES
    }
    #[cfg(test)]
    pub(super) fn snapshot(&self) -> ScratchSnapshot {
        use std::sync::atomic::Ordering::Relaxed;
        let counters = &self.counters;
        ScratchSnapshot {
            equation_misses: counters.equation_misses.load(Relaxed),
            equation_ceiling_drops: counters.equation_ceiling_drops.load(Relaxed),
            equation_full_drops: counters.equation_full_drops.load(Relaxed),
            workspace_misses: counters.workspace_misses.load(Relaxed),
            workspace_ceiling_drops: counters.workspace_ceiling_drops.load(Relaxed),
            workspace_full_drops: counters.workspace_full_drops.load(Relaxed),
        }
    }
    fn lease_equation(&self) -> Equation {
        lock(&self.equations).pop().unwrap_or_else(|| {
            #[cfg(test)]
            count(&self.counters.equation_misses);
            Equation::new()
        })
    }
    fn return_equation(&self, mut equation: Equation) {
        equation.reset();
        if equation.retained_bytes() > tuning::VERIFIER_EQUATION_MAX_BYTES {
            #[cfg(test)]
            count(&self.counters.equation_ceiling_drops);
            return;
        }
        let mut idle = lock(&self.equations);
        if idle.len() < self.equation_slots {
            idle.push(equation);
        } else {
            #[cfg(test)]
            count(&self.counters.equation_full_drops);
        }
    }
    fn lease_workspace(&self) -> MsmWorkspace {
        lock(&self.workspaces).pop().unwrap_or_else(|| {
            #[cfg(test)]
            count(&self.counters.workspace_misses);
            MsmWorkspace::new()
        })
    }
    // Callers return a workspace only after draining its batch, the same
    // returned-slot condition `MsmWorkspace::retained_bytes` requires.
    fn return_workspace(&self, workspace: MsmWorkspace) {
        if workspace.retained_bytes() > tuning::VERIFIER_WORKSPACE_MAX_BYTES {
            #[cfg(test)]
            count(&self.counters.workspace_ceiling_drops);
            return;
        }
        let mut idle = lock(&self.workspaces);
        if idle.len() < self.workspace_slots {
            idle.push(workspace);
        } else {
            #[cfg(test)]
            count(&self.counters.workspace_full_drops);
        }
    }
}

static RUNTIME: OnceLock<VerifierRuntime> = OnceLock::new();

impl VerifierRuntime {
    fn get() -> &'static Self {
        RUNTIME.get_or_init(|| Self::new(PreparedSrs::shared(), PoolExecutor::get()))
    }
    fn new(srs: Arc<PreparedSrs>, executor: &'static PoolExecutor) -> Self {
        // Only the VK commitments need verifier-owned point expansions. The
        // residue codebook is shared with every equal-width SRS bank.
        let codebook = srs.codebook(tuning::VERIFIER_FIXED_ALPHA_WIDTH);
        // The shared SRS supplies the codebook for this fixed tuning width;
        // the embedded VK bank's constant length must have representable sizes.
        let requirements = codebook
            .view()
            .description()
            .requirements::<Vesta, PreparedAffinePoint<Vesta>>(VK_COMMITMENTS.len())
            .expect("fixed verifier bank");
        let mut vk_bases = vec![
            PreparedAffinePoint::from_affine(&VestaAffine::GENERATOR);
            requirements.table_entries
        ];
        executor.run(|context| {
            AlphaTable::prepare(
                codebook.view(),
                VK_COMMITMENTS,
                &mut vk_bases,
                &mut vec![VestaProjective::IDENTITY; requirements.projective_scratch],
                &mut vec![Fq::ZERO; requirements.field_scratch],
                executor.budget(),
                context,
            );
        });
        let instance_generators = PREPARED_POINTS.lagrange_bases[..INSTANCE_VALUE_COUNT]
            .iter()
            .map(|base| FixedGenerator::warmed(base, tuning::INSTANCE_FIXED_WIDTH))
            .collect();
        Self {
            srs,
            vk_bases,
            instance_generators,
            vk_indices: core::array::from_fn(|mask| {
                let mut used = [false; VERIFIER_POINT_COUNT];
                for (version, columns) in VK_DATA.columns.iter().enumerate() {
                    if mask & (1 << version) != 0 {
                        for &index in columns {
                            used[index as usize] = true;
                        }
                    }
                }
                used.iter()
                    .enumerate()
                    .filter_map(|(i, &used)| used.then_some(i as u32))
                    .collect()
            }),
            codebook,
            executor,
            scratch: VerifierScratch::new(
                tuning::verifier_equation_slots(
                    executor.budget_capped(tuning::VERIFY_FOLD_TASK_CAP).get(),
                ),
                tuning::verifier_workspace_slots(executor.budget().get()),
            ),
        }
    }
    fn check(
        &self,
        equation: &Equation,
        #[cfg(test)] timing: &mut timing::Recorder,
    ) -> Result<(), Error> {
        let mut scratch = self.scratch.lease_workspace();
        #[cfg(test)]
        {
            timing.facts.workspace_before = scratch.retained_bytes();
        }
        let result = self
            .evaluate_with(
                equation,
                &mut scratch,
                #[cfg(test)]
                timing,
            )
            .and_then(|point| {
                if point.is_identity() {
                    Ok(())
                } else {
                    Err(Error::InvalidProof)
                }
            });
        #[cfg(test)]
        {
            // The batch dropped with `evaluate_with`, so every lease is back.
            timing.facts.workspace_after = scratch.retained_bytes();
            timing.mark(timing::Stage::Finish);
        }
        self.scratch.return_workspace(scratch);
        result
    }
    #[cfg(test)]
    fn evaluate(
        &self,
        equation: &Equation,
        scratch: &mut MsmWorkspace,
    ) -> Result<VestaProjective, Error> {
        self.evaluate_with(equation, scratch, &mut timing::Recorder::disabled())
    }
    fn evaluate_with(
        &self,
        equation: &Equation,
        scratch: &mut MsmWorkspace,
        #[cfg(test)] timing: &mut timing::Recorder,
    ) -> Result<VestaProjective, Error> {
        self.executor.run(|executor| {
            let bases =
                Bases::AlphaPrepared(AlphaTable::bind(self.codebook.view(), &self.vk_bases));
            let indices = &self.vk_indices[usize::from(equation.versions)];
            let mut selected = [Fp::ZERO; VERIFIER_POINT_COUNT];
            // Current-only and complete-prefix unions retain the dense path.
            // Other combinations index the same prepared bank without copying points.
            let vk_input = if indices
                .last()
                .is_none_or(|&last| last as usize + 1 == indices.len())
            {
                Input::new(
                    bases.range(0..indices.len()),
                    &equation.fixed[FIXED_OFFSET..FIXED_OFFSET + indices.len()],
                )
            } else {
                for (scalar, &index) in selected.iter_mut().zip(indices) {
                    *scalar = equation.fixed[FIXED_OFFSET + index as usize];
                }
                // VerifierRuntime::new derives in-bank indices, paired above
                // with one scalar each.
                Input::indexed(bases, indices, &selected[..indices.len()])
                    .map_err(|_| Error::InternalInvariant)?
            };
            // Slicing pairs two chunk iterators, which would drop a trailing
            // chunk silently if these lengths ever differed; `Input::new`
            // checks only each pair.
            if equation.points.len() != equation.scalars.len() {
                return Err(Error::InternalInvariant);
            }
            let budget = self.msm_budget(equation.points.len());
            // Equation::new/point/merge preserve these bank and point/scalar
            // lengths; every input produces exactly one output below.
            let mut inputs = Vec::with_capacity(FIXED_INPUTS + budget.get());
            inputs.extend([
                Input::new(self.srs.coefficient_bases(), &equation.fixed[..N]),
                vk_input,
                Input::new(
                    self.srs.lagrange_bases().range(0..INSTANCE_VALUE_COUNT),
                    &equation.fixed[INSTANCE_OFFSET..BLIND_GENERATOR_SLOT],
                ),
            ]);
            let slice = slice_len(budget.get(), equation.points.len());
            inputs.extend(
                equation
                    .points
                    .chunks(slice)
                    .zip(equation.scalars.chunks(slice))
                    .map(|(points, scalars)| Input::new(Bases::Prepared(points), scalars)),
            );
            let mut output = vec![VestaProjective::IDENTITY; inputs.len()];
            #[cfg(test)]
            timing.msm_inputs(inputs.len());
            let mut batch = scratch
                .prepare(&inputs, budget)
                .map_err(|_| Error::InternalInvariant)?;
            #[cfg(test)]
            {
                timing.mark(timing::Stage::MsmPrepare);
                let (workers, groups) = batch.shape();
                timing.facts.msm_budget = budget.get();
                timing.facts.msm_workers = workers;
                timing.facts.msm_groups = groups;
            }
            #[cfg(test)]
            let executed = batch.execute_probed(&mut output, executor, &timing.msm);
            #[cfg(not(test))]
            let executed = batch.execute(&mut output, executor);
            executed.map_err(|_| Error::InternalInvariant)?;
            #[cfg(test)]
            {
                drop(batch);
                timing.mark(timing::Stage::MsmExecute);
            }
            let fixed = FixedGenerator::sum(
                [&self.srs.blind_generator, &self.srs.ipa_generator],
                &[
                    equation.fixed[BLIND_GENERATOR_SLOT],
                    equation.fixed[IPA_GENERATOR_SLOT],
                ],
            );
            Ok(output.iter().fold(fixed, |sum, point| sum.add(point)))
        })
    }
    fn msm_budget(&self, dynamic_points: usize) -> TaskBudget {
        let cap = self
            .executor
            .budget_capped(tuning::VERIFY_MSM_TASK_CAP)
            .get();
        #[cfg(not(test))]
        let tasks = msm_tasks(cap, dynamic_points);
        #[cfg(test)]
        let tasks = msm_tasks_with(
            bench_override("SENSEI_BENCH_MSM_CAP", cap),
            dynamic_points,
            bench_setting("SENSEI_BENCH_MSM_MIN_TERMS", tuning::VERIFY_MSM_MIN_TERMS),
        );
        TaskBudget::new(tasks).expect("nonzero task floor")
    }
    fn fold_cap(&self) -> usize {
        let cap = self
            .executor
            .budget_capped(tuning::VERIFY_FOLD_TASK_CAP)
            .get();
        #[cfg(test)]
        let cap = bench_override("SENSEI_BENCH_FOLD_CAP", cap);
        cap
    }
}

/// The final MSM's fixed inputs: coefficient SRS, verifying-key bank, and
/// instance Lagrange bases. The transcript points follow as slices.
const FIXED_INPUTS: usize = 3;

/// Final-MSM task budget: one task per [`tuning::VERIFY_MSM_MIN_TERMS`] of the
/// equation's terms, within the capped pool budget. The fixed segments are the
/// coefficient SRS, deduplicated verifying-key bank, and instance Lagrange
/// bases; `dynamic_points` counts the batch's transcript commitments.
fn msm_tasks(cap: usize, dynamic_points: usize) -> usize {
    msm_tasks_with(cap, dynamic_points, tuning::VERIFY_MSM_MIN_TERMS)
}
fn msm_tasks_with(cap: usize, dynamic_points: usize, min_terms: usize) -> usize {
    let terms = N + VERIFIER_POINT_COUNT + INSTANCE_VALUE_COUNT + dynamic_points;
    (terms / min_terms.max(1)).clamp(1, cap.max(1))
}

/// Transcript points per final-MSM input slice: the batch's points split
/// into one slice per [`tuning::VERIFY_MSM_SLICE_POINTS`], never more slices
/// than the MSM task budget, and at least one point per slice.
fn slice_len(budget: usize, dynamic_points: usize) -> usize {
    let slices = (dynamic_points / tuning::VERIFY_MSM_SLICE_POINTS).clamp(1, budget.max(1));
    #[cfg(test)]
    let slices = std::env::var("SENSEI_BENCH_MSM_SLICES")
        .ok()
        .map(|value| value.parse::<usize>().expect("positive slice count"))
        .unwrap_or(slices)
        .clamp(1, dynamic_points.max(1));
    dynamic_points.div_ceil(slices).max(1)
}

/// Fold-chunk budget: one chunk per [`tuning::VERIFY_FOLD_MIN_ACTIONS`]
/// Actions of folding work, never more than the proofs or the capped pool
/// allow. A single-chunk batch folds on the calling thread.
fn fold_jobs(cap: usize, proofs: usize, actions: usize) -> usize {
    (actions / tuning::VERIFY_FOLD_MIN_ACTIONS).clamp(1, cap.max(1).min(proofs.max(1)))
}

/// A benchmark's environment override of a resolved task cap, for sweeping
/// caps without rebuilding; the pool still bounds the result.
#[cfg(test)]
fn bench_override(name: &str, resolved: usize) -> usize {
    bench_setting(name, resolved).clamp(1, resolved.max(1))
}

/// A benchmark's environment override of a tuning value, unbounded.
#[cfg(test)]
fn bench_setting(name: &str, default: usize) -> usize {
    std::env::var(name).ok().map_or(default, |value| {
        value.parse().expect("positive tuning value")
    })
}

pub(crate) fn warm_up_verifier() {
    let _ = VerifierRuntime::get();
}

/// Provisions the bounded idle scratch pools for an expected batch shape and
/// reports its plan; the public [`crate::warm_up_verifier_scratch`] contract
/// describes the sizing. The plan's bytes are measured on the entries just
/// provisioned, so they match what `verify` leases for the same shape.
pub(crate) fn warm_up_verifier_scratch(proofs: usize, actions: usize) -> VerificationPlan {
    let runtime = VerifierRuntime::get();
    let scratch = &runtime.scratch;
    let mut plan = VerificationPlan {
        fold_tasks: 0,
        msm_tasks: 0,
        workspace_bytes: 0,
        equation_bytes: 0,
        pooled_batches: scratch.workspace_slots,
        retained: true,
        max_idle_bytes: scratch.max_idle_bytes(),
    };
    if proofs == 0 {
        return plan;
    }
    let actions = actions.max(proofs);
    let jobs = fold_jobs(runtime.fold_cap(), proofs, actions);
    // Transcript point counts depend only on each proof's Action count; size
    // chunks for a uniform Action split, like the batches being provisioned for.
    let per_proof = super::protocol::transcript_encoding::point_runs(actions.div_ceil(proofs))
        .map_or(0, |runs| runs.iter().map(|(_, count)| count).sum());
    let chunk_points = per_proof * proofs.div_ceil(jobs);
    plan.fold_tasks = jobs;
    plan.msm_tasks = runtime.msm_budget(per_proof * proofs).get();
    // Hold every lease before returning any, so the pool keeps `jobs` distinct
    // provisioned equations rather than re-provisioning one repeatedly.
    let mut equations: Vec<_> = (0..jobs).map(|_| scratch.lease_equation()).collect();
    for equation in &mut equations {
        equation.points.reserve(chunk_points);
        equation.scalars.reserve(chunk_points);
    }
    plan.retained &= jobs <= scratch.equation_slots;
    for equation in equations {
        let bytes = equation.retained_bytes();
        plan.equation_bytes += bytes;
        plan.retained &= bytes <= tuning::VERIFIER_EQUATION_MAX_BYTES;
        scratch.return_equation(equation);
    }
    let mut workspace = scratch.lease_workspace();
    runtime.provision_workspace(&mut workspace, per_proof * proofs);
    plan.workspace_bytes = workspace.retained_bytes();
    plan.retained &= plan.workspace_bytes <= tuning::VERIFIER_WORKSPACE_MAX_BYTES;
    scratch.return_workspace(workspace);
    plan
}

impl VerifierRuntime {
    /// Grows a final-MSM workspace for a batch carrying `dynamic_points`
    /// transcript commitments. Planning inspects scalar shapes, so the
    /// synthetic input uses full-width scalars to match a real batch's
    /// geometry; `prepare` provisions every bank and scratch bundle without
    /// executing arithmetic, and the dropped [`super::commitment::Batch`]
    /// leaves all retained leases in place. A real batch's own `prepare`
    /// still plans normally and tops up any residual mismatch.
    fn provision_workspace(&self, workspace: &mut MsmWorkspace, dynamic_points: usize) {
        let points =
            vec![PreparedAffinePoint::from_affine(&VestaAffine::GENERATOR); dynamic_points];
        let scalars = vec![<Fp>::ZERO.sub(&<Fp>::ONE); N.max(dynamic_points)];
        let bases = Bases::AlphaPrepared(AlphaTable::bind(self.codebook.view(), &self.vk_bases));
        let budget = self.msm_budget(dynamic_points);
        let slice = slice_len(budget.get(), dynamic_points);
        let mut inputs = vec![
            Input::new(self.srs.coefficient_bases(), &scalars[..N]),
            Input::new(
                bases.range(0..VERIFIER_POINT_COUNT),
                &scalars[..VERIFIER_POINT_COUNT],
            ),
            Input::new(
                self.srs.lagrange_bases().range(0..INSTANCE_VALUE_COUNT),
                &scalars[..INSTANCE_VALUE_COUNT],
            ),
        ];
        inputs.extend(
            points
                .chunks(slice)
                .zip(scalars[..dynamic_points].chunks(slice))
                .map(|(points, scalars)| Input::new(Bases::Prepared(points), scalars)),
        );
        let _ = workspace.prepare(&inputs, budget);
    }
}

/// Decodes every point in a proof ahead of transcript reading.
///
/// A canonical proof's point offsets depend only on its Action count, so the
/// encodings can be gathered and decoded together — sharing interleaved
/// square-root chains — before Blake2b absorption consumes the transcript
/// serially. Returns `None` for an unexpected length, an invalid encoding, or
/// an identity point. Every supported version uses this layout, so failure
/// rejects the proof without decoding its points again.
fn prefetch_points(proof: &[u8], actions: usize) -> Option<Vec<VestaAffine>> {
    use super::protocol::transcript_encoding::{POINT_BYTES, point_runs, proof_capacity};
    if proof.len() != proof_capacity(actions)? {
        return None;
    }
    let runs = point_runs(actions)?;
    let total = runs.iter().map(|(_, count)| count).sum();
    let mut encodings = Vec::with_capacity(total);
    for &(offset, count) in &runs {
        let bytes = proof.get(offset..offset + count * POINT_BYTES)?;
        for chunk in bytes.chunks_exact(POINT_BYTES) {
            let encoding = <[u8; 32]>::try_from(chunk).expect("fixed encoding width");
            // Identity is valid for the curve decoder but forbidden in proofs.
            // Reject it before doing any square-root work for this proof.
            if encoding == [0; POINT_BYTES] {
                return None;
            }
            encodings.push(encoding);
        }
    }
    let mut points = vec![VestaPoint::IDENTITY; total];
    VestaPoint::batch_from_bytes(&encodings, &mut points)?;
    points
        .into_iter()
        .map(|point| point.as_affine().copied())
        .collect()
}

#[cfg(all(test, feature = "prover"))]
pub(super) fn prepared_srs_for_test() -> Option<&'static Arc<PreparedSrs>> {
    RUNTIME.get().map(|runtime| &runtime.srs)
}

pub(crate) fn verify(
    requests: &[VerificationRequest<'_>],
    rng: &mut dyn RandomSource,
) -> Result<(), Error> {
    if requests.is_empty() {
        return Ok(());
    }
    #[cfg(test)]
    let mut timing = timing::Recorder::begin();
    // Sample before executor initialization and scratch acquisition. The first
    // proof has weight one; each later equation receives an independent weight.
    let mut weights = vec![<Fp>::ONE; requests.len()];
    for weight in &mut weights[1..] {
        *weight = sample_fp(rng)?;
        if weight.is_zero() {
            // A zero weight would omit a proof's equation. Retry the batch
            // with fresh weights; its proof transcripts need not change.
            return Err(Error::RetryRandomness);
        }
    }
    let runtime = VerifierRuntime::get();
    let total_actions = requests.iter().map(|r| r.statements.len()).sum();
    let jobs = fold_jobs(runtime.fold_cap(), requests.len(), total_actions);
    #[cfg(test)]
    {
        timing.mark(timing::Stage::Weights);
        timing.facts.fold_jobs = jobs;
    }
    let combined = if jobs == 1 {
        // The cheap path for tiny batches: fold on the calling thread without
        // entering the pool scheduler. The final MSM still uses the pool.
        let equation = fold_chunk(
            runtime,
            requests,
            &weights,
            #[cfg(test)]
            &timing,
        )?;
        #[cfg(test)]
        timing.mark(timing::Stage::Fold);
        equation
    } else {
        let chunk = requests.len().div_ceil(jobs);
        #[cfg(test)]
        {
            timing.facts.fold_chunk = chunk;
        }
        #[cfg(test)]
        let fold_timing = &timing;
        let results = runtime.executor.run(|executor| {
            // Bounded number of worker-local fixed banks, chosen by the
            // batch's folding work rather than the full worker budget.
            let execution = Execution::new(executor, TaskBudget::new(jobs).expect("nonzero jobs"));
            execution.map(
                requests.chunks(chunk).zip(weights.chunks(chunk)),
                |(requests, weights), _| {
                    fold_chunk(
                        runtime,
                        requests,
                        weights,
                        #[cfg(test)]
                        fold_timing,
                    )
                },
            )
        });
        #[cfg(test)]
        timing.mark(timing::Stage::Fold);
        // Drain every chunk result — returning each merged shell to the pool —
        // before reporting the batch's first error, so failures keep scratch.
        // The first equation absorbs the rest: sizing it once keeps its
        // capacity exact, so whether it returns to the pool follows the
        // batch's size rather than amortized growth past the ceiling.
        let points: usize = results.iter().flatten().map(|e| e.points.len()).sum();
        let mut combined: Option<Equation> = None;
        let mut failure = None;
        for result in results {
            match result {
                Ok(mut equation) => match &mut combined {
                    Some(combined) => {
                        combined.merge(&mut equation);
                        runtime.scratch.return_equation(equation);
                    }
                    None => {
                        let extra = points - equation.points.len();
                        equation.points.reserve_exact(extra);
                        equation.scalars.reserve_exact(extra);
                        combined = Some(equation);
                    }
                },
                Err(error) => failure = failure.or(Some(error)),
            }
        }
        if let Some(error) = failure {
            if let Some(combined) = combined {
                runtime.scratch.return_equation(combined);
            }
            return Err(error);
        }
        #[cfg(test)]
        timing.mark(timing::Stage::Merge);
        combined.expect("nonempty verification batch")
    };
    let result = runtime.check(
        &combined,
        #[cfg(test)]
        &mut timing,
    );
    runtime.scratch.return_equation(combined);
    #[cfg(test)]
    {
        timing.mark(timing::Stage::Return);
        timing.finish();
    }
    result
}

/// Folds one worker chunk into an equation leased from the runtime's pool,
/// returning the lease before reporting a rejected proof.
fn fold_chunk(
    runtime: &VerifierRuntime,
    requests: &[VerificationRequest<'_>],
    weights: &[Fp],
    #[cfg(test)] timing: &timing::Recorder,
) -> Result<Equation, Error> {
    #[cfg(test)]
    let started = timing.fold.start();
    let mut equation = runtime.scratch.lease_equation();
    for (request, &weight) in requests.iter().zip(weights) {
        let folded = equation.proof_with(
            request,
            weight,
            &runtime.instance_generators,
            #[cfg(test)]
            Some(&timing.prefetch),
        );
        if let Err(error) = folded {
            runtime.scratch.return_equation(equation);
            return Err(error);
        }
    }
    #[cfg(test)]
    timing.fold.record(started);
    Ok(equation)
}

struct Equation {
    versions: u8,
    fixed: Vec<Fp>,
    // Prepared entries cache each point's endomorphism coordinate, saving the
    // MSM one base-field multiplication per nonzero rotated digit per window.
    points: Vec<PreparedAffinePoint<Vesta>>,
    scalars: Vec<Fp>,
    #[cfg(test)]
    challenges: Vec<[u8; 32]>,
}
impl Equation {
    fn new() -> Self {
        Self {
            versions: 0,
            fixed: vec![<Fp>::ZERO; BANK_LEN],
            points: Vec::new(),
            scalars: Vec::new(),
            #[cfg(test)]
            challenges: Vec::new(),
        }
    }
    /// Folds `other` into `self`, draining its points and scalars so the
    /// emptied shell keeps its capacity for the scratch pool.
    fn merge(&mut self, other: &mut Self) {
        self.versions |= other.versions;
        for (a, b) in self.fixed.iter_mut().zip(&other.fixed) {
            *a = a.add(b);
        }
        self.points.append(&mut other.points);
        self.scalars.append(&mut other.scalars);
    }
    /// Restores the leased-equation state `new` produces, keeping capacity.
    fn reset(&mut self) {
        self.versions = 0;
        self.fixed.fill(<Fp>::ZERO);
        self.points.clear();
        self.scalars.clear();
        #[cfg(test)]
        self.challenges.clear();
    }
    /// Retained capacity in bytes, for the pool's per-entry ceiling.
    fn retained_bytes(&self) -> usize {
        self.fixed.capacity() * size_of::<Fp>()
            + self.points.capacity() * size_of::<PreparedAffinePoint<Vesta>>()
            + self.scalars.capacity() * size_of::<Fp>()
            + self.challenge_bytes()
    }
    #[cfg(test)]
    fn challenge_bytes(&self) -> usize {
        self.challenges.capacity() * size_of::<[u8; 32]>()
    }
    #[cfg(not(test))]
    fn challenge_bytes(&self) -> usize {
        0
    }
    fn point(&mut self, reader: &mut Reader<'_>) -> Result<usize, Error> {
        let index = self.points.len();
        self.points
            .push(PreparedAffinePoint::from_affine(&reader.point()?));
        self.scalars.push(<Fp>::ZERO);
        Ok(index)
    }
    fn points<const C: usize>(&mut self, reader: &mut Reader<'_>) -> Result<[usize; C], Error> {
        let mut indices = [0; C];
        for index in &mut indices {
            *index = self.point(reader)?;
        }
        Ok(indices)
    }
    #[cfg(test)]
    fn proof(
        &mut self,
        request: &VerificationRequest<'_>,
        weight: Fp,
        generators: &[FixedGenerator],
    ) -> Result<(), Error> {
        self.proof_with(request, weight, generators, None)
    }
    fn proof_with(
        &mut self,
        request: &VerificationRequest<'_>,
        weight: Fp,
        generators: &[FixedGenerator],
        #[cfg(test)] prefetch: Option<&crate::native::task_stats::TaskStats>,
    ) -> Result<(), Error> {
        #[cfg(test)]
        let started = prefetch.and_then(crate::native::task_stats::TaskStats::start);
        let decoded =
            prefetch_points(request.proof, request.statements.len()).ok_or(Error::InvalidProof)?;
        #[cfg(test)]
        if let Some(prefetch) = prefetch {
            prefetch.record(started);
        }
        let mut reader = Reader::with_decoded(request.proof, &decoded);
        let version = request.version;
        self.versions |= 1 << version.index();
        let columns = &VK_DATA.columns[version.index()];
        let instance_len = version.instance_len();
        reader.common_scalar(&version.vk_representative());
        let statements: Vec<_> = request.statements.iter().map(|s| s.native()).collect();
        absorb_instances(&mut reader, &statements, instance_len, generators)?;
        let mut actions: Vec<_> = (0..statements.len())
            .map(|_| ActionData::default())
            .collect();
        for a in &mut actions {
            a.advice = self.points(&mut reader)?;
        }
        let theta = reader.challenge();
        for a in &mut actions {
            for pair in &mut a.lookup_pairs {
                *pair = self.points(&mut reader)?;
            }
        }
        let beta = reader.challenge();
        let gamma = reader.challenge();
        for a in &mut actions {
            a.permutation = self.points(&mut reader)?;
        }
        for a in &mut actions {
            a.lookup_products = self.points(&mut reader)?;
        }
        let vanishing = self.point(&mut reader)?;
        let y = reader.challenge();
        let quotient: [usize; QUOTIENT_PIECES] = self.points(&mut reader)?;
        let x = reader.challenge();
        // Claimed instance evaluations are proof inputs, including for malformed
        // proofs; substituting honest evaluations changes the reference equation.
        for a in &mut actions {
            a.instance_eval = reader.scalar()?;
        }
        for a in &mut actions {
            a.advice_evals = reader.scalars()?;
        }
        let fixed_evals = reader.scalars::<{ FIXED_QUERIES.len() }>()?;
        let vanishing_eval = reader.scalar()?;
        let sigma_evals = reader.scalars::<PERMUTATION_COLUMN_COUNT>()?;
        for a in &mut actions {
            for (i, set) in a.permutation_evals.iter_mut().enumerate() {
                set[PERMUTATION_EVAL_CURRENT] = reader.scalar()?;
                set[PERMUTATION_EVAL_NEXT] = reader.scalar()?;
                if i + 1 < PERMUTATION_SETS {
                    set[PERMUTATION_EVAL_LAST] = reader.scalar()?;
                }
            }
        }
        for a in &mut actions {
            for lookup in &mut a.lookup_evals {
                *lookup = reader.scalars()?;
            }
        }
        let xn = x.pow_u64(N as u64);
        let h_eval = quotient_evaluation(
            &actions,
            &fixed_evals,
            &sigma_evals,
            Challenges {
                theta,
                beta,
                gamma,
                y,
                x,
                xn,
            },
        )?;
        let x1 = reader.challenge();
        let x2 = reader.challenge();
        let q_prime = self.point(&mut reader)?;
        let x3 = reader.challenge();
        let u: [Fp; POINT_SETS] = reader.scalars()?;
        let x4 = reader.challenge();
        // K = 11 is a fixed circuit parameter within Fp's 2-adicity (32);
        // neither the request nor the transcript chooses this domain.
        let omega = <Fp>::root_of_unity(K).expect("fixed domain");
        let omega_inv = <Fp>::root_of_unity_inverse(K).expect("fixed domain");
        let points = OPENING_ROTATIONS.map(|rotation| {
            x.mul(&if rotation < 0 {
                omega_inv.pow_u64((-rotation) as u64)
            } else {
                omega.pow_u64(rotation as u64)
            })
        });
        if x.is_zero() {
            return Err(Error::InvalidProof);
        }
        let mut eval_sets = [[<Fp>::ZERO; OPENING_POINTS]; POINT_SETS];
        let mut group_weight = weight;
        for (group_index, group) in OPENING_GROUPS.iter().enumerate().rev() {
            let mut power = <Fp>::ONE;
            let evals = &mut eval_sets[group_index];
            for &polynomial in group.fixed().iter().rev() {
                let coefficient = power.mul(&group_weight);
                let eval = match polynomial {
                    FixedPolynomial::Fixed(column) => {
                        let slot = FIXED_OFFSET + columns[column as usize] as usize;
                        self.fixed[slot] = self.fixed[slot].add(&coefficient);
                        fixed_evals[fixed_query(column as usize)]
                    }
                    FixedPolynomial::Sigma(column) => {
                        let slot = FIXED_OFFSET + columns[FIXED_COLUMNS + column as usize] as usize;
                        self.fixed[slot] = self.fixed[slot].add(&coefficient);
                        sigma_evals[column as usize]
                    }
                    FixedPolynomial::Quotient => {
                        let mut coefficient = coefficient;
                        for &index in &quotient {
                            self.scalars[index] = self.scalars[index].add(&coefficient);
                            coefficient = coefficient.mul(&xn);
                        }
                        h_eval
                    }
                    FixedPolynomial::Vanishing => {
                        self.scalars[vanishing] = self.scalars[vanishing].add(&coefficient);
                        vanishing_eval
                    }
                };
                for point in group.point_ids() {
                    evals[point] = evals[point].add(&power.mul(&eval));
                }
                power = power.mul(&x1);
            }
            for (a, statement) in actions.iter().zip(&statements).rev() {
                for &polynomial in group.per_action().iter().rev() {
                    let coefficient = power.mul(&group_weight);
                    match polynomial {
                        ActionPolynomial::Instance => {
                            for (slot, value) in self.fixed
                                [INSTANCE_OFFSET..INSTANCE_OFFSET + instance_len]
                                .iter_mut()
                                .zip(statement.iter())
                            {
                                *slot = slot.add(&coefficient.mul(value));
                            }
                            self.fixed[BLIND_GENERATOR_SLOT] =
                                self.fixed[BLIND_GENERATOR_SLOT].add(&coefficient);
                        }
                        _ => {
                            let index = a.commitment(polynomial);
                            self.scalars[index] = self.scalars[index].add(&coefficient);
                        }
                    }
                    for point in group.point_ids() {
                        evals[point] = evals[point]
                            .add(&power.mul(&a.evaluation(polynomial, OPENING_ROTATIONS[point])));
                    }
                    power = power.mul(&x1);
                }
            }
            group_weight = group_weight.mul(&x4);
        }
        self.scalars[q_prime] = self.scalars[q_prime].add(&group_weight);
        let mut v = multiopen_evaluation(&points, &eval_sets, &u, x2, x3)?;
        for eval in u {
            v = v.mul(&x4).add(&eval);
        }
        self.ipa(&mut reader, v, x3, weight)?;
        #[cfg(test)]
        self.challenges.extend_from_slice(&reader.challenges);
        reader.finish()
    }
    fn ipa(&mut self, reader: &mut Reader<'_>, v: Fp, x: Fp, weight: Fp) -> Result<(), Error> {
        let s = self.point(reader)?;
        self.scalars[s] = self.scalars[s].add(&weight.mul(&reader.challenge()));
        let z = reader.challenge();
        let mut rounds = [[0; 2]; ROUNDS];
        let mut u = [<Fp>::ZERO; ROUNDS];
        for (round, challenge) in rounds.iter_mut().zip(&mut u) {
            *round = self.points(reader)?;
            *challenge = reader.challenge();
        }
        let c = reader.scalar()?;
        let f = reader.scalar()?;
        let mut inv = u;
        invert(&mut inv)?;
        for (([l, r], u), inverse) in rounds.into_iter().zip(u).zip(inv) {
            self.scalars[l] = self.scalars[l].add(&weight.mul(&inverse));
            self.scalars[r] = self.scalars[r].add(&weight.mul(&u));
        }
        let mut b = <Fp>::ONE;
        let mut x_power = x;
        let mut coefficients = [<Fp>::ZERO; N];
        coefficients[0] = c.neg().mul(&weight);
        let mut len = 1;
        for challenge in u.into_iter().rev() {
            b = b.mul(&<Fp>::ONE.add(&challenge.mul(&x_power)));
            x_power = x_power.square();
            for i in 0..len {
                coefficients[len + i] = coefficients[i].mul(&challenge);
            }
            len *= 2;
        }
        for (slot, value) in self.fixed[..N].iter_mut().zip(coefficients) {
            *slot = slot.add(&value);
        }
        self.fixed[0] = self.fixed[0].sub(&weight.mul(&v));
        self.fixed[IPA_GENERATOR_SLOT] =
            self.fixed[IPA_GENERATOR_SLOT].sub(&weight.mul(&c).mul(&b).mul(&z));
        self.fixed[BLIND_GENERATOR_SLOT] = self.fixed[BLIND_GENERATOR_SLOT].sub(&weight.mul(&f));
        Ok(())
    }
}

fn absorb_instances(
    reader: &mut Reader<'_>,
    statements: &[NativeStatement],
    instance_len: usize,
    generators: &[FixedGenerator],
) -> Result<(), Error> {
    // The version selects a prefix of NativeStatement and of the generator
    // bank. Each commitment walks the statement's values through the
    // doubling-free fixed-base tables instead of a general MSM. An Orchard
    // bundle's Actions share one anchor (slot zero), so its term is computed
    // once; statements with distinct anchors fall back to per-statement terms.
    let tables: Vec<_> = generators[..instance_len]
        .iter()
        .map(FixedGenerator::table)
        .collect();
    use crate::public_input::ANCHOR;
    let shared_anchor = match statements {
        [first, rest @ ..]
            if rest
                .iter()
                .all(|s| s[ANCHOR].reduce() == first[ANCHOR].reduce()) =>
        {
            Some(FixedGenerator::sum_tables(&tables[..1], &first[..1]))
        }
        _ => None,
    };
    let mut projective = vec![VestaProjective::IDENTITY; statements.len()];
    for (statement, point) in statements.iter().zip(&mut projective) {
        let anchor = shared_anchor
            .unwrap_or_else(|| FixedGenerator::sum_tables(&tables[..1], &statement[..1]));
        let rest = FixedGenerator::sum_tables(&tables[1..], &statement[1..instance_len]);
        *point = anchor
            .add(&rest)
            .add_mixed(&PREPARED_POINTS.blind_generator);
    }
    let mut points = vec![VestaPoint::IDENTITY; statements.len()];
    let mut scratch = vec![Fq::ZERO; statements.len()];
    batch_normalize(&projective, &mut points, &mut scratch);
    for point in points {
        reader.common_point(&point)?;
    }
    Ok(())
}

#[derive(Default)]
struct ActionData {
    advice: [usize; ADVICE_COLUMNS],
    lookup_pairs: [[usize; 2]; LOOKUP_COUNT],
    permutation: [usize; PERMUTATION_SETS],
    lookup_products: [usize; LOOKUP_COUNT],
    instance_eval: Fp,
    advice_evals: [Fp; ADVICE_QUERIES.len()],
    permutation_evals: [[Fp; 3]; PERMUTATION_SETS],
    lookup_evals: [[Fp; 5]; LOOKUP_COUNT],
}
impl ActionData {
    fn commitment(&self, polynomial: ActionPolynomial) -> usize {
        match polynomial {
            ActionPolynomial::Advice(i) => self.advice[i as usize],
            ActionPolynomial::Permutation(i) => self.permutation[i as usize],
            ActionPolynomial::LookupProduct(i) => self.lookup_products[i as usize],
            ActionPolynomial::LookupInput(i) => self.lookup_pairs[i as usize][0],
            ActionPolynomial::LookupTable(i) => self.lookup_pairs[i as usize][1],
            ActionPolynomial::Instance => unreachable!("instances fold into the fixed bank"),
        }
    }
    fn evaluation(&self, polynomial: ActionPolynomial, rotation: i32) -> Fp {
        match polynomial {
            ActionPolynomial::Instance => self.instance_eval,
            ActionPolynomial::Advice(column) => {
                // OPENING_GROUPS is const-derived from ADVICE_QUERIES; the
                // caller supplies only that group's polynomial/rotation pairs.
                self.advice_evals[ADVICE_QUERIES
                    .iter()
                    .position(|q| q.column == column as usize && q.rotation == rotation)
                    .expect("derived query")]
            }
            ActionPolynomial::Permutation(i) => {
                self.permutation_evals[i as usize][match rotation {
                    0 => PERMUTATION_EVAL_CURRENT,
                    1 => PERMUTATION_EVAL_NEXT,
                    _ => PERMUTATION_EVAL_LAST,
                }]
            }
            ActionPolynomial::LookupProduct(i) => {
                // Slots 0/1 hold the grand product at rotations 0/+1.
                self.lookup_evals[i as usize][usize::from(rotation != 0)]
            }
            ActionPolynomial::LookupInput(i) => {
                self.lookup_evals[i as usize][if rotation == 0 {
                    LOOKUP_EVAL_INPUT_CURRENT
                } else {
                    LOOKUP_EVAL_INPUT_PREVIOUS
                }]
            }
            ActionPolynomial::LookupTable(i) => self.lookup_evals[i as usize][LOOKUP_EVAL_TABLE],
        }
    }
}
fn fixed_query(column: usize) -> usize {
    // Opening fixed columns are derived from FIXED_QUERIES. The other caller
    // uses the pinned PERMUTATION_COLUMNS, whose fixed columns are queried at 0.
    FIXED_QUERIES
        .iter()
        .position(|q| q.column == column)
        .expect("fixed column query")
}
struct Evaluations<'a> {
    fixed: &'a [Fp],
    advice: &'a [Fp],
}
impl Algebra for Evaluations<'_> {
    type Value = Fp;
    fn fixed(&self, index: u8) -> Fp {
        self.fixed[index as usize]
    }
    fn advice(&self, index: u8) -> Fp {
        self.advice[index as usize]
    }
    fn gated(&self, factor: impl FnOnce() -> Fp, body: Fp) -> Fp {
        factor().mul(&body)
    }
}
struct Challenges {
    theta: Fp,
    beta: Fp,
    gamma: Fp,
    y: Fp,
    x: Fp,
    xn: Fp,
}
fn quotient_evaluation(
    actions: &[ActionData],
    fixed: &[Fp],
    sigma: &[Fp],
    Challenges {
        theta,
        beta,
        gamma,
        y,
        x,
        xn,
    }: Challenges,
) -> Result<Fp, Error> {
    // The same fixed K/Fp domain used by Equation::proof; no proof input
    // affects root availability.
    let omega_inv = <Fp>::root_of_unity_inverse(K).expect("fixed domain");
    let mut roots = [<Fp>::ONE; BLINDING_FACTORS + 2];
    for i in 1..roots.len() {
        roots[i] = roots[i - 1].mul(&omega_inv);
    }
    let mut denominators = roots.map(|root| x.sub(&root));
    invert(&mut denominators)?;
    let scale = xn.sub(&<Fp>::ONE).mul(&<Fp>::power_of_two_inverse(K));
    let lagrange = core::array::from_fn::<_, { BLINDING_FACTORS + 2 }, _>(|i| {
        roots[i].mul(&scale).mul(&denominators[i])
    });
    let l0 = lagrange[0];
    let last = lagrange[BLINDING_FACTORS + 1];
    let active = <Fp>::ONE.sub(&lagrange[1..].iter().fold(<Fp>::ZERO, |a, b| a.add(b)));
    let mut fold = <Fp>::ZERO;
    let mut push = |term| {
        fold = fold.mul(&y).add(&term);
    };
    for a in actions {
        let algebra = Evaluations {
            fixed,
            advice: &a.advice_evals,
        };
        for index in 0..GATE_CONSTRAINT_COUNT {
            push(programs::expression(&algebra, index));
        }
        push(l0.mul(&<Fp>::ONE.sub(&a.permutation_evals[0][PERMUTATION_EVAL_CURRENT])));
        let last_z = a.permutation_evals[PERMUTATION_SETS - 1][PERMUTATION_EVAL_CURRENT];
        push(last.mul(&last_z.square().sub(&last_z)));
        for i in 1..PERMUTATION_SETS {
            push(
                l0.mul(
                    &a.permutation_evals[i][PERMUTATION_EVAL_CURRENT]
                        .sub(&a.permutation_evals[i - 1][PERMUTATION_EVAL_LAST]),
                ),
            );
        }
        let mut delta = beta.mul(&x);
        for (set, columns) in PERMUTATION_COLUMNS
            .chunks(PERMUTATION_CHUNK_LEN)
            .enumerate()
        {
            let mut left = a.permutation_evals[set][PERMUTATION_EVAL_NEXT];
            let mut right = a.permutation_evals[set][PERMUTATION_EVAL_CURRENT];
            for (i, column) in columns.iter().enumerate() {
                let eval = match column.kind {
                    ColumnKind::Instance => a.instance_eval,
                    ColumnKind::Advice => {
                        a.evaluation(ActionPolynomial::Advice(column.index as u8), 0)
                    }
                    ColumnKind::Fixed => fixed[fixed_query(column.index)],
                };
                left = left.mul(
                    &eval
                        .add(&beta.mul(&sigma[set * PERMUTATION_CHUNK_LEN + i]))
                        .add(&gamma),
                );
                right = right.mul(&eval.add(&delta).add(&gamma));
                delta = delta.mul(&<Fp>::DELTA);
            }
            push(active.mul(&left.sub(&right)));
        }
        for (lookup, [z, z_next, input, input_prev, table]) in LOOKUPS.iter().zip(a.lookup_evals) {
            let compress = |range: super::expression_layout::ExpressionRange| {
                range.indices().fold(<Fp>::ZERO, |acc, i| {
                    acc.mul(&theta).add(&programs::expression(&algebra, i))
                })
            };
            push(l0.mul(&<Fp>::ONE.sub(&z)));
            push(last.mul(&z.square().sub(&z)));
            push(
                active.mul(
                    &z_next.mul(&input.add(&beta)).mul(&table.add(&gamma)).sub(
                        &z.mul(&compress(lookup.inputs()).add(&beta))
                            .mul(&compress(lookup.tables()).add(&gamma)),
                    ),
                ),
            );
            push(l0.mul(&input.sub(&table)));
            push(active.mul(&input.sub(&table)).mul(&input.sub(&input_prev)));
        }
    }
    Ok(fold.mul(&xn.sub(&<Fp>::ONE).invert().ok_or(Error::InvalidProof)?))
}

fn invert(values: &mut [Fp]) -> Result<(), Error> {
    // These denominators/challenges come from the supplied proof transcript.
    // Unlike prover retries, fresh verifier batch weights cannot change them.
    if values.iter().any(<Fp>::is_zero) {
        return Err(Error::InvalidProof);
    }
    // All callers invert small fixed protocol sets, never one value per Action.
    let mut scratch = [<Fp>::ZERO; POINT_SETS * (OPENING_POINTS + 1)];
    batch_invert(values, &mut scratch[..values.len()]);
    Ok(())
}
fn multiopen_evaluation(
    points: &[Fp; OPENING_POINTS],
    evals: &[[Fp; OPENING_POINTS]; POINT_SETS],
    u: &[Fp; POINT_SETS],
    x2: Fp,
    x3: Fp,
) -> Result<Fp, Error> {
    let mut denominators = Vec::with_capacity(POINT_SETS * (OPENING_POINTS + 1));
    for group in &OPENING_GROUPS {
        for j in group.point_ids() {
            denominators.push(
                group
                    .point_ids()
                    .filter(|&k| k != j)
                    .fold(<Fp>::ONE, |a, k| a.mul(&points[j].sub(&points[k]))),
            );
        }
        denominators.push(
            group
                .point_ids()
                .fold(<Fp>::ONE, |a, j| a.mul(&x3.sub(&points[j]))),
        );
    }
    invert(&mut denominators)?;
    // The identical OPENING_GROUPS traversal below consumes the interpolation
    // entries and then one vanishing entry appended for each group above.
    let mut inverse = denominators.into_iter();
    let mut v = <Fp>::ZERO;
    for ((group, evals), &u) in OPENING_GROUPS.iter().zip(evals).zip(u) {
        let mut r = <Fp>::ZERO;
        for j in group.point_ids() {
            let numerator = group
                .point_ids()
                .filter(|&k| k != j)
                .fold(<Fp>::ONE, |a, k| a.mul(&x3.sub(&points[k])));
            r = r.add(
                &evals[j]
                    .mul(&numerator)
                    .mul(&inverse.next().expect("interpolation denominator")),
            );
        }
        v = v.mul(&x2).add(
            &u.sub(&r)
                .mul(&inverse.next().expect("vanishing denominator")),
        );
    }
    Ok(v)
}

#[cfg(test)]
mod tests;
#[cfg(test)]
pub(super) mod timing;
