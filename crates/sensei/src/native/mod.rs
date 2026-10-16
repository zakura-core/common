//! Circuit preparation and the transcript-ordered proof pipeline.
//!
//! # Expression execution paths
//!
//! [`sensei_shared::programs`] owns the recipes: [`expression`](programs::expression)
//! evaluates them through an algebra, while [`expression_programs`](programs::expression_programs)
//! builds [`Expression`](sensei_shared::expressions::Expression) trees for host
//! macros and tests. Native paths below are relative to this module. The
//! schedule, preflight, and quotient paths require `prover`; the verifier
//! path requires `verifier`.
//!
//! | Path | Consumer |
//! | --- | --- |
//! | `compiled_expressions` | `sensei_macros::expression_programs!` lowers trees to compact schedules. `target` uses fixed-factor schedules to prepare active gate rows; `prover::lookup` prepares fixed table values; `evaluation::evaluate_expression` supplies ordinary-domain lookup fallbacks. |
//! | `compiled_gates` | `preflight` uses specialized recipe bodies on prepared active rows, omitting each gate's nonzero fixed root factor for the zero test. Grouped Poseidon checks share the three bodies' S-box work. |
//! | `generated_expressions` + `prover::quotient::rows` | Hand-maintained fused gate kernels, including macro-generated weighted subkernels, feed the quotient's extended-domain folds. `prover::lookup` supplies its fused lookup compression. |
//! | `generated_expressions::LookupInputKernel` | Ordinary-domain preflight lookup membership and `prover::lookup`'s recomputation of rows affected by advice blinding use fused input kernels. Compact schedules remain the fallback when a kernel is unavailable for the columns. |
//! | `verifier::quotient_evaluation` | Directly evaluates the shared recipes over claimed query values, including fixed factors, to reconstruct the quotient evaluation. |
//! | `generated_expressions::{TREES, program_trees, evaluate}` | With `cfg(test)` and `prover`, the `generated_expressions/reference.rs` owner retains source trees and recursively evaluates them for the schedule, gate-body, and quotient references through these unchanged caller paths. |
//!
//! Agreement is checked by these `cfg(test)` paths, also relative to `native`:
//!
//! - `compiled_expressions::tests::compiled_programs_match_source_trees_and_splits`
//!   compares full expressions and both fixed-root operands with tree evaluation.
//! - `compiled_gates::tests::compiled_gate_bodies_match_tree_reference` compares
//!   every body at every base-domain row, including grouped Poseidon outputs.
//!   `preflight::tests::native_preflight_accepts_checked_fixtures` and
//!   `preflight::tests::grouped_poseidon_preflight_rejects_corrupted_outputs`
//!   compare sparse and full-row checks on valid and corrupted fixtures.
//! - `generated_expressions::tests::fused_gate_kernel_matches_tree_reference`
//!   compares the weighted gate fold with tree evaluation;
//!   `prover::tests::lookup_compression::shared_sinsemilla_cubics_match_lookup_trees_and_rotations`
//!   checks fused lookup arithmetic and rotations, and
//!   `generated_expressions::tests::sinsemilla_input_kernel_matches_tree_reference`
//!   compares the ordinary-domain lookup input kernels with compact schedules.
//! - `prover::tests::quotient::class_split_quotient_matches_dense_reference_on_fixtures`
//!   compares quotient coefficients with a dense, protocol-ordered reference
//!   whose gate terms use the tree evaluator.
//! - `verifier::tests::versions::transcript_and_equations_match_reference_for_valid_and_invalid_proofs`
//!   compares transcript challenges and assembled equations with frozen
//!   independent captures for each supported circuit version.
//!
//! The recursive evaluator is separate from the optimized evaluators, but its
//! trees come from the same recipes: their agreement establishes evaluator
//! consistency, not an independent circuit specification.
//! `generated_expressions::tests::tree_spec_matches_historical_container_digest`
//! separately pins recipe structure to frozen digests, including the reviewed
//! curve-selector reassociation.
//!
//! # Oracle independence
//!
//! Keep these references separate from the helpers they check. Independence
//! is specific to the boundary below: shared circuit facts, inputs, or field
//! and curve arithmetic do not supply an independent circuit specification.
//! Native source paths are relative to this module; other paths start at the
//! repository root. Test-only symbols are written as code paths because normal
//! rustdoc builds omit them. Update these paths when moving their owners.
//!
//! | Reference | What it establishes; helpers deliberately avoided |
//! | --- | --- |
//! | Tree interpreter (`generated_expressions/reference.rs`) and structural pin (`generated_expressions/tests.rs`) | The [expression execution map](#expression-execution-paths) lists evaluator comparisons. Recursive evaluation avoids compact schedules and fused kernels but uses the same recipes. `tree_spec_matches_historical_container_digest` separately checks frozen historical structure and the reviewed reassociation; evaluator agreement alone cannot establish that structure. |
//! | Shadow writer and rational finalizer (`witness/writer/shadow.rs`) | `ShadowWriter` and `batch_finalize_rationals` use enum cells and a separate denominator-product scan to check writes, final columns, and errors, avoiding the dense support mask, rational event log, and `finalize_rational_cells`. They receive the same gadget assignments; they do not independently specify synthesis. |
//! | Serial, fixed-assignment, and full-row preflight (`preflight/reference.rs`) | `check_gates_serial` and `check_gates_fixed` avoid production task grouping but share `sparse_gate_expression_is_zero` and its specialized bodies. `check_gates_full` checks all rows and full expressions through `evaluate_expression`, avoiding active-row selection and omitted fixed factors; its compact schedules still come from shared recipes. |
//! | Dynamic opening grouping (`prover/opening/reference.rs`) | `opening_query_plan` and `group_opening_queries` reconstruct first-appearance polynomial/point-set order by comparing actual points, without the compile-time `opening_schedule`. Prover tests compare groups and folding order; query facts and rotation arithmetic remain shared. |
//! | Artifact reference transforms (`crates/sensei-artifacts/src/polynomials/{coefficients,cosets}.rs`, `crates/sensei-artifacts/src/points/srs.rs`) | `udon::fft::reference` derives coefficients, cosets, and the Lagrange SRS without using the prover's optimized FFT/LDE outputs as expectations. Inputs, reconstruction recipes, and arithmetic are shared. `target/tests.rs` compares derived data and frozen stored-form/canonical digests. `crates/sensei-artifacts/tests/determinism.rs` alone checks repeat generation, not baseline byte compatibility. |
//! | Unit and integration fixture codecs (`crates/sensei/src/test_codec.rs`, `crates/sensei/tests/support/`) | Unit corpus/decoder/tape support stays separate from the public-API decoder and `crates/sensei/tests/golden.rs`'s own corpus/tape replay. Golden bytes and RNG counts come from committed fixtures, not the current prover. `crates/sensei/tests/support/verification.rs` also decodes instance columns without the native statement conversion. Public field/point decoding is shared; these codecs do not specify the circuit. |
//! | Word decomposition (`witness/decomposition/bitstream.rs`, `witness/tests.rs`) | Single-view words/running sums and `words_with_running_sums` avoid `WordStream`/`fill_words_and_running_sums`; byte/bit references in the tests additionally check canonical integer extraction. Integer and field operations remain shared. |
//! | Complete-addition Sinsemilla reference (`crates/sensei/src/primitives/sinsemilla/{mod,addition}.rs`) | `hash_to_point_with_two_additions` and addition tests use two additions built on complete group arithmetic with incomplete-addition validity checks, avoiding fused `double_and_add` and checking exceptional outcomes too. The hash reference shares message words and generators; a separate comparison with padded bit chunks checks `MessageWords`. |
//! | Frozen migration equations/challenges (`verifier/{tests,versions}.rs`) | Captured `equations.bin` records supply weighted equation results and ordered challenges for all three versions, including mutated and adversarial proofs. Expected values do not run the current transcript, quotient reconstruction, or equation assembler; matching rejection alone would miss these differences. |
//! | Historical acceptance (`crates/sensei/tests/verification.rs`) | Archived proofs and `historical_suffixes_preserve_singleton_and_batch_verification` retain pre-NU6.2 suffix acceptance at 1, 2, 3, 65, and 128 Actions, plus consumed-prefix mutation rejection. The historical expectations were checked with the archived verifier, not inferred from current size checks. |
//! | Large-proof hashes (`crates/sensei/tests/large_proofs.rs`) | Frozen hashes pin deterministic 17/65/128-Action baseline Sensei proofs independently accepted by the legacy verifier. The test also checks RNG counts and sizes; current self-verification does not supply the expected hashes or establish compatibility by itself. |
//! | Primitive/signature fixtures (`crates/sensei/tests/{primitives_interop,redpallas}.rs`) | Legacy bytes pin field operations, hash-to-curve, agreement, Poseidon, both signature domains, and spend-key randomization. Expected bytes are not computed by current primitive/signature helpers; signature replay also checks consumption of its supplied randomness. |
//!
//! The manifests in `tests/fixtures/migration/` and `tests/fixtures/legacy/`
//! record archive revisions and fixture digests. Fixture values and expectations
//! must not be regenerated to accommodate cleanup changes.

#[cfg(all(test, feature = "prover"))]
mod test_support;

mod buffer;
mod commitment;
#[cfg(feature = "prover")]
mod compiled_expressions;
#[cfg(feature = "prover")]
mod compiled_gates;
#[cfg(feature = "prover")]
mod evaluation;
mod executor;
mod expression_layout;
#[cfg(all(test, feature = "prover"))]
mod expressions;
#[cfg(feature = "prover")]
mod generated_expressions;
#[cfg(feature = "prover")]
pub(crate) mod invariant;
#[cfg(feature = "prover")]
pub(crate) mod polynomial;
#[cfg(feature = "prover")]
pub(crate) mod preflight;
pub(crate) mod protocol;
#[cfg(feature = "prover")]
mod runtime;
pub(crate) mod srs;
mod storage;
#[cfg(feature = "verifier")]
pub(crate) mod verifier;

#[cfg(feature = "prover")]
pub(crate) mod prover;
mod queries;
#[cfg(feature = "prover")]
pub(crate) mod randomness;
#[cfg(feature = "prover")]
pub(crate) mod regions;
#[cfg(feature = "prover")]
pub(crate) mod target;
pub(crate) mod transcript;
#[cfg(feature = "prover")]
pub(crate) mod witness;
pub(crate) mod worker;

#[cfg(all(feature = "prover", feature = "benchmark-internals"))]
pub(crate) use runtime::benchmark_initialize;
#[cfg(all(test, feature = "prover", feature = "verifier"))]
pub(crate) use runtime::benchmark_resources;
#[cfg(feature = "prover")]
pub(crate) use runtime::{prove, warm_up_prover};
#[cfg(feature = "prover")]
pub(crate) use sensei_shared::fixed_columns;
pub(crate) use sensei_shared::programs;
pub(crate) use udon::{curve, field};

#[cfg(all(test, feature = "prover"))]
use crate::RandomSource;
#[cfg(feature = "prover")]
use crate::{Error, types::ProvingRequest};
#[cfg(feature = "prover")]
use alloc::{sync::Arc, vec::Vec};
#[cfg(feature = "prover")]
use udon::exec::{Executor, TaskBudget};

/// Immutable circuit data, polynomial preparation, and commitment tables.
///
/// Share this owner across proofs. Each concurrent call needs a separate
/// [`ProverWorkspace`]. Preparation performs no global initialization.
#[cfg(feature = "prover")]
pub(crate) struct PreparedProver {
    target: target::FixedTarget,
}

/// Caller-owned temporary storage retained across proof stages and calls.
///
/// Storage grows to meet a request and remains available for later proofs.
/// Use one workspace per concurrent proof.
#[cfg(feature = "prover")]
pub(crate) struct ProverWorkspace {
    pub(crate) msm: commitment::MsmWorkspace,
    pub(crate) ipa: prover::IpaWorkspace,
    pub(crate) fft: polynomial::FftWorkspace,
    pub(crate) buffers: buffer::BufferPool<field::Fp>,
    pub(crate) lookup: prover::LookupWorkspace,
}
#[cfg(feature = "prover")]
impl ProverWorkspace {
    /// Creates an empty workspace; buffers grow when first needed.
    pub(crate) fn new() -> Self {
        let buffers = buffer::BufferPool::default();
        Self {
            msm: commitment::MsmWorkspace::new(),
            ipa: prover::IpaWorkspace::default(),
            fft: polynomial::FftWorkspace::new(buffers.clone()),
            buffers,
            lookup: prover::LookupWorkspace::default(),
        }
    }
}
#[cfg(feature = "prover")]
impl Default for ProverWorkspace {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "prover")]
impl PreparedProver {
    /// Prepares the pinned circuit over shared SRS and the caller's execution resources.
    /// Returns an error if the embedded circuit data is inconsistent.
    /// No request values participate: target errors describe an internal
    /// preparation failure, not an invalid statement, witness, or proof.
    pub(crate) fn new<E: Executor>(
        srs: Arc<srs::PreparedSrs>,
        executor: &E,
        budget: TaskBudget,
    ) -> Result<Self, Error> {
        let execution = worker::Execution::new(executor, budget);
        Ok(Self {
            target: target::FixedTarget::build(srs, execution)
                .map_err(|_| Error::InternalInvariant)?,
        })
    }

    /// Creates verifier-facing proof bytes with the supplied randomness.
    ///
    /// See [`RandomSource`] for randomness requirements. The request is checked
    /// against the circuit before commitments are published. Returns an error
    /// for an invalid witness, failed randomness, or a degenerate challenge.
    #[cfg(all(test, feature = "prover"))]
    pub(crate) fn create_proof<E: Executor>(
        &self,
        request: &ProvingRequest,
        rng: &mut dyn RandomSource,
        workspace: &mut ProverWorkspace,
        executor: &E,
        budget: TaskBudget,
    ) -> Result<Vec<u8>, Error> {
        let execution = worker::Execution::new(executor, budget);
        let timing = stage_timing::Recorder::begin();
        let randomness = randomness::ProvingRandomness::sample(rng, request.action_count())?;
        self.create_proof_sampled(request, randomness, workspace, execution, timing)
    }

    fn create_proof_sampled(
        &self,
        request: &ProvingRequest,
        randomness: randomness::ProvingRandomness,
        workspace: &mut ProverWorkspace,
        execution: worker::Execution<'_>,
        #[cfg(all(test, feature = "prover"))] mut timing: stage_timing::Recorder,
    ) -> Result<Vec<u8>, Error> {
        let buffers = workspace.buffers.clone();
        let execution = execution.with_buffers(&buffers);
        let statements = alloc::sync::Arc::from(request.native_statements());
        let (witness_matrices, mut witness_feeds) = witness::build_native_witness_matrices(
            &self.target,
            execution,
            request,
            &statements,
            &workspace.lookup,
        )?;
        #[cfg(all(test, feature = "prover"))]
        timing.mark(stage_timing::Stage::Witness);
        let mut prover = prover::ProverPrefix::initialize_checked(
            &self.target,
            workspace,
            execution,
            request,
            statements,
            core::mem::take(&mut witness_feeds.instances),
        )?;
        #[cfg(all(test, feature = "prover"))]
        timing.mark(stage_timing::Stage::Initialize);
        let advice = prover.commit_advice(witness_matrices, randomness.advice)?;
        #[cfg(all(test, feature = "prover"))]
        timing.mark(stage_timing::Stage::Advice);
        let lookup = prover.commit_lookup_permutations(
            &advice,
            witness_feeds,
            randomness.lookup_permutations,
        )?;
        #[cfg(all(test, feature = "prover"))]
        timing.mark(stage_timing::Stage::LookupPermutations);
        let (permutations, lookup_products) = prover.commit_product_arguments(
            &advice,
            &lookup,
            randomness.permutation_products,
            randomness.lookup_products,
        )?;
        #[cfg(all(test, feature = "prover"))]
        timing.mark(stage_timing::Stage::ProductArguments);
        let vanishing = prover.commit_vanishing_random_polynomial(
            &permutations,
            &lookup_products,
            randomness.vanishing,
        )?;
        #[cfg(all(test, feature = "prover"))]
        timing.mark(stage_timing::Stage::Vanishing);
        let quotient = prover.construct_quotient(
            advice,
            lookup,
            permutations,
            lookup_products,
            &vanishing,
            randomness.quotient_piece_blinds,
            randomness.ipa_mask,
        )?;
        #[cfg(all(test, feature = "prover"))]
        timing.mark(stage_timing::Stage::Quotient);
        let evaluations = prover.write_evaluations(&vanishing, &quotient)?;
        #[cfg(all(test, feature = "prover"))]
        timing.mark(stage_timing::Stage::Evaluations);
        let multiopen = prover.commit_multiopen_quotient(
            vanishing,
            quotient,
            evaluations,
            randomness.multiopen_quotient_blind,
        )?;
        #[cfg(all(test, feature = "prover"))]
        timing.mark(stage_timing::Stage::MultiopenQuotient);
        let ipa = prover.commit_ipa_mask(multiopen)?;
        #[cfg(all(test, feature = "prover"))]
        timing.mark(stage_timing::Stage::IpaMask);
        prover.finish_ipa(ipa, randomness.ipa_rounds)?;
        #[cfg(all(test, feature = "prover"))]
        timing.mark(stage_timing::Stage::IpaFinish);
        let proof = prover.into_proof();
        if proof.len() != request.shape.proof_bytes {
            return Err(Error::InternalInvariant);
        }
        #[cfg(all(test, feature = "prover"))]
        {
            timing.mark(stage_timing::Stage::ProofCopy);
            timing.finish();
        }
        Ok(proof)
    }
}

#[cfg(all(test, feature = "prover"))]
mod optimization_tests;
#[cfg(all(test, feature = "prover"))]
pub(crate) mod stage_timing;

/// Builds an array by calling `entry` in index order (`0..LEN`).
///
/// If `entry` returns an error, no later indices are visited. The local array
/// of `Option<T>` slots drops all previously initialized entries before the
/// error is returned.
#[cfg(feature = "prover")]
pub(crate) fn try_array_from_fn<T, const LEN: usize>(
    mut entry: impl FnMut(usize) -> Result<T, crate::Error>,
) -> Result<[T; LEN], crate::Error> {
    let mut slots = core::array::from_fn(|_| None);
    for (index, slot) in slots.iter_mut().enumerate() {
        *slot = Some(entry(index)?);
    }
    Ok(slots.map(|slot| slot.expect("all fixed record entries were initialized")))
}
