//! Inner-product argument masking and recursive opening proof.
//!
//! Generator folds stay virtual between periodic materializations, reducing
//! the bases visited by later rounds. Challenges and pre-sampled round blinds
//! are consumed in the transcript order described on the stage methods.

use crate::Error;
use crate::native::buffer::{Buffer, BufferPool};
use crate::native::field::{Fp, ProductSum};
use crate::native::randomness::IpaRoundBlinds;
use crate::native::target::{K, N};
use crate::native::worker::Execution;
#[cfg(test)]
use alloc::sync::Arc;
use alloc::vec::Vec;
use udon::polynomial::EvaluationPlan;

mod generators;
mod run;

/// Proof-owned leases survive phase changes and return after the last reader.
#[derive(Default)]
pub(crate) struct IpaWorkspace {
    indices: BufferPool<u32>,
    partials: BufferPool<crate::native::curve::VestaProjective>,
    generators: generators::Workspace,
}
impl IpaWorkspace {
    #[cfg(test)]
    pub(crate) fn capacities(&self) -> Vec<usize> {
        let mut capacities = self.generators.capacities();
        for inventory in [self.indices.inventory(), self.partials.inventory()] {
            capacities.extend([inventory.allocations, inventory.buffers, inventory.bytes]);
        }
        capacities
    }
    #[cfg(all(test, feature = "verifier"))]
    pub(crate) fn retained_bytes(&self) -> usize {
        self.indices.inventory().bytes
            + self.partials.inventory().bytes
            + self.generators.retained_bytes()
    }
    #[cfg(test)]
    pub(crate) fn dirty(&mut self) {
        self.indices.dirty(u32::MAX);
        self.partials
            .dirty(crate::native::curve::VestaProjective::GENERATOR);
        self.generators.dirty();
    }
}

use super::inventory::ipa_stage;
use super::opening::{PolySource, parallel_deferred_horner_fold};
use super::{
    EvaluationJob, EvaluationSource, IpaMaskPrefix, MultiopenPrefix, ProverPrefix,
    parallel_evaluate_polynomials,
};

// Test-only attribution of the round phases (`ipa_finish.*` tokens); the
// production build has no `stage_timing` module and these fold to nothing.
#[cfg(test)]
use crate::native::stage_timing::{IpaPhase, ipa_phase_finish, ipa_phase_start};
#[cfg(not(test))]
#[derive(Clone, Copy)]
enum IpaPhase {
    Rounds,
    Generators,
}
#[cfg(not(test))]
#[inline(always)]
fn ipa_phase_start() -> Option<()> {
    None
}
#[cfg(not(test))]
#[inline(always)]
fn ipa_phase_finish(_phase: IpaPhase, _started: Option<()>) {}

impl ProverPrefix<'_> {
    /// Writes the collapsed `Q_i` evaluations, folds the multi-opening input
    /// at `x_4`, and commits to the exact sparse IPA masking polynomial before
    /// squeezing `xi` and `z`.
    ///
    /// # Transcript contract
    ///
    /// - **Requires** `x_3` from the [`MultiopenPrefix`]; no other challenge.
    /// - **Publishes**, in two transcript-ordered steps separated by a
    ///   challenge: first every `Q_i(x_3)` as scalars in point-set group
    ///   order; then, after `x_4`, one commitment to the sparse IPA mask
    ///   `s(X)` (coefficients at degrees `2^i`, constant term fixing
    ///   `s(x_3) = 0`).
    /// - **Squeezes** `x_4` between the two steps, then `ξ` and `z` after the
    ///   mask commitment, in that order; `ξ`, `z`, and `x_3` are carried on
    ///   the returned [`IpaMaskPrefix`].
    /// - **Draws** no randomness: the `K` mask coefficients (one per doubling
    ///   exponent, ascending) and the mask blind arrive pre-sampled, carried
    ///   on the multi-opening prefix together with their challenge-independent
    ///   commitment part `Σ α_i·G_{2^i} + blind·W`, which the quotient stage's
    ///   piece batch already formed (see [`super::IpaMaskEarly`]).
    ///
    /// The `x_4` fold of `Q'` and the `Q_i` into the IPA input, and the fold
    /// of their blinds, are preparation for the next stage that depends on
    /// `x_4` and therefore sits between the two publications; nothing here
    /// runs out of transcript order. The mask commitment's only
    /// `x_3`-dependent term, its constant `−Σ_i α_i x_3^{2^i}` on `G_0`, is one
    /// prepared fixed-base multiplication added to the early part.
    ///
    /// # Work and buffer inventory
    ///
    /// Logical counts from [`super::inventory::opening_stage`] and [`ipa_stage`]: `POINT_SETS`
    /// dense `N`-coefficient evaluations at `x_3` (one pool phase); one
    /// `x_4`-weighted fold of `Q'` and the `Q_i` into the
    /// `FOLDED_POLYNOMIAL`-coefficient IPA input (one pass over each, as one
    /// pool phase over coefficient chunks reusing the uniquely owned `Q′`
    /// buffer); one fixed-base multiplication completing the sparse mask commitment. This
    /// stage consumes the multi-opening prefix and releases the `Q_i` after
    /// the fold. Alive at return: the folded polynomial (`N`, in `Q′`'s former
    /// storage) and its blind; see the
    /// [ownership table](super#stage-buffer-ownership).
    pub(crate) fn commit_ipa_mask(
        &mut self,
        multiopen: MultiopenPrefix,
    ) -> Result<IpaMaskPrefix, Error> {
        let MultiopenPrefix {
            q_polynomials,
            q_blinds,
            q_prime_polynomial,
            q_prime_blind,
            x_3,
            ipa_mask,
        } = multiopen;
        if q_polynomials.is_empty()
            || q_polynomials.len() != q_blinds.len()
            || q_polynomials.iter().any(|polynomial| polynomial.len() != N)
            || q_prime_polynomial.len() != N
            || ipa_mask.alphas.len() != K as usize
        {
            return Err(Error::InternalInvariant);
        }

        // The challenge-dependent work after each squeeze runs as pool
        // phases — the `Q_i(x_3)` evaluations as one
        // evaluation phase, the `x_4` fold over coefficient chunks — instead
        // of a serial walk on the transcript-ordered tail. Both are exact, so
        // every written scalar and the folded polynomial are unchanged.
        let q_evaluations = parallel_evaluate_polynomials(
            self.execution,
            q_polynomials
                .iter()
                .map(|polynomial| EvaluationJob {
                    coefficients: EvaluationSource::Dense(PolySource::Borrowed(polynomial)),
                    point: x_3,
                })
                .collect::<Vec<_>>(),
        )?;
        for evaluation in &q_evaluations {
            self.transcript.write_scalar(evaluation);
        }
        let x_4 = self.transcript.squeeze_challenge();

        // Fold order is unchanged: `Q'` is the leading term, then the `Q_i`
        // in point-set group order. Reuse the uniquely owned `Q'` buffer as
        // the IPA input and release the `Q_i` after the fold.
        let polynomial = parallel_deferred_horner_fold(
            self.execution,
            q_prime_polynomial,
            &q_polynomials,
            &x_4,
        )?;
        drop(q_polynomials);
        let mut blind = q_prime_blind;
        for q_blind in &q_blinds {
            blind = blind.mul_add(&x_4, q_blind);
        }

        // Sparse IPA mask `s(X)`: support contract — exactly the degrees
        // `{0} ∪ {2^i : i < K}`, `K + 1` terms standing for the dense
        // `N`-coefficient polynomial that is zero elsewhere, with the constant
        // term fixed so `s(x_3) = 0`; committed as those terms plus its blind,
        // and folded into the IPA input by the same degrees.
        let mut mask_evaluation = ProductSum::new();
        let mut mask = [(0, Fp::ZERO); K as usize + 1];
        let mut x_power = x_3;
        for (exponent, alpha) in ipa_mask.alphas.iter().enumerate() {
            mask_evaluation.add_product(alpha, &x_power);
            mask[exponent + 1] = (1usize << exponent, *alpha);
            x_power = x_power.square();
        }
        // Reduce the product sum once, then negate it to make s(x_3) = 0.
        let constant = mask_evaluation.finish().neg();
        mask[0].1 = constant;
        let mask_blind = ipa_mask.blind;
        let target = self.target;
        // As described by IpaMaskEarly, every term but the constant was
        // committed with the quotient pieces; `constant · G_0` is the one
        // term that had to wait for `x_3`, applied through the prepared first
        // generator's window tables. The sum is exactly the sparse
        // commitment of `mask`.
        let late_term = target
            .parameters()
            .prepared_first_coefficient_generator()
            .mul(&constant);
        let mask_commitment = ipa_mask.commitment.add(&late_term).to_point();
        // The random mask/blind may produce identity; retry proof creation
        // because the transcript has no affine encoding for it.
        self.transcript
            .write_point(&mask_commitment)
            .map_err(|_| Error::RetryRandomness)?;
        let xi = self.transcript.squeeze_challenge();
        let z = self.transcript.squeeze_challenge();

        Ok(IpaMaskPrefix {
            x_3,
            polynomial,
            blind,
            mask,
            mask_blind,
            xi,
            z,
        })
    }
}

impl ProverPrefix<'_> {
    /// Opens the folded polynomial at `x_3` with the fixed eleven-round IPA,
    /// writing every round commitment and the final `c` and `f` scalars.
    ///
    /// # Transcript contract
    ///
    /// - **Requires** `ξ`, `z`, and `x_3` from the [`IpaMaskPrefix`]; no
    ///   other challenge.
    /// - **Publishes**, per round for `K` rounds (halving the polynomial each
    ///   time): the `L` commitment, then the `R` commitment, then a squeeze
    ///   of that round's challenge `u_j` — eleven genuine challenge barriers,
    ///   since round `j + 1`'s folded polynomial, generators, and blinds are
    ///   functions of `u_j`. After the last round: the scalars `c` (the
    ///   surviving coefficient) then `f` (the folded blind).
    /// - **Squeezes** the `K` round challenges, one inside each round as
    ///   above; the stage returns nothing further.
    /// - **Draws** no randomness: two blinds per round (`L` then `R`) arrive
    ///   pre-sampled in round order.
    ///
    /// Within one round the preparation (one pool phase over the generator
    /// chunks: the pending challenge's coefficient fold, the polynomial fold,
    /// the L/R staging and the upper half's inner product) and the two
    /// commitments' MSMs are free to run in any task order; the `L`/`R`
    /// writes and the squeeze are the round's transcript-ordered section,
    /// and no work for round `j + 1` can start before `u_j` exists.
    ///
    /// # Work and buffer inventory
    ///
    /// Logical counts from [`ipa_stage`]: `ROUNDS` rounds, each with
    /// `MSMS_PER_ROUND` commitments over the logical half-length, an inner
    /// product of `round_terms(j)` terms, and a polynomial fold. Generator
    /// folds are materialized after rounds 3 and 6 with shared scalar weights;
    /// the actual index-selected MSMs use 1024, 128, then 16 terms each.
    /// Alive across rounds: the folded polynomial (at most
    /// `FOLDED_POLYNOMIAL`), the `N/2`-length evaluation power vector, the
    /// current generator bank, and its index/scalar staging. Polynomial leases
    /// return to the workspace when the stage releases them.
    pub(crate) fn finish_ipa(
        &mut self,
        ipa: IpaMaskPrefix,
        round_blinds: [IpaRoundBlinds; crate::native::randomness::IPA_ROUNDS],
    ) -> Result<(), Error> {
        // Consumed: nothing after this stage needs the prefix, so the
        // `N`-element polynomial moves into the masking path instead of being
        // cloned.
        let IpaMaskPrefix {
            x_3,
            polynomial,
            blind,
            mask,
            mask_blind,
            xi,
            z,
        } = ipa;
        if polynomial.len() != N
            || round_blinds.len() != ipa_stage::ROUNDS
            || mask.len() != K as usize + 1
            || mask.first().map(|entry| entry.0) != Some(0)
            || mask
                .iter()
                .skip(1)
                .enumerate()
                .any(|(exponent, entry)| entry.0 != 1usize << exponent)
        {
            return Err(Error::InternalInvariant);
        }

        let mut masked_polynomial = polynomial;
        for (index, coefficient) in &mask {
            let value = masked_polynomial
                .get_mut(*index)
                .ok_or(Error::InternalInvariant)?;
            *value = value.add(&coefficient.mul(&xi));
        }
        let (evaluation_powers, x_to_half) =
            subtract_ipa_evaluation(self.execution, &mut masked_polynomial, &x_3)?;
        let initial_blind = mask_blind.mul_add(&xi, &blind);

        let parameters = self.target.parameters();
        if parameters.coefficient_bases().len() != N {
            return Err(Error::InternalInvariant);
        }
        run::finish(
            &mut self.workspace.msm,
            &mut self.workspace.ipa,
            self.execution,
            &mut self.transcript,
            parameters.coefficient_bases(),
            parameters.folding_bases(),
            parameters.prepared_ipa_generator(),
            parameters.prepared_blind_generator(),
            masked_polynomial,
            evaluation_powers,
            x_to_half,
            z,
            initial_blind,
            round_blinds,
        )
    }
}

/// Subtracts `p(x)` from the constant coefficient and retains the powers needed
/// by the IPA rounds. Splitting `p = low + X^(N/2) * high` lets both evaluations
/// share that half-length table, without preparing the upper half's powers.
pub(super) fn subtract_ipa_evaluation(
    execution: Execution<'_>,
    polynomial: &mut [Fp],
    point: &Fp,
) -> Result<(Buffer<Fp>, Fp), Error> {
    if polynomial.len() != N {
        return Err(Error::InternalInvariant);
    }

    let mut powers = execution.buffer(N / 2, false);
    powers[0] = <Fp>::ONE;
    // EvaluationPlan omits x^0; the round vector includes it.
    let plan = EvaluationPlan::prepare(point, &mut powers[1..]);
    let (low, high) = polynomial.split_at(N / 2);
    let mut evaluations = [<Fp>::ZERO; 2];
    // Both halves fit the powers prepared above, with one output per half.
    plan.evaluate_many(&[low, high], &mut evaluations)
        .map_err(|_| Error::InternalInvariant)?;
    let x_to_half = powers[N / 2 - 1].mul(point);
    let evaluation = evaluations[1].mul_add(&x_to_half, &evaluations[0]);
    polynomial[0] = polynomial[0].sub(&evaluation);
    Ok((powers, x_to_half))
}

/// Reference scheduling of virtual folds over one generator bank.
///
/// Between materializations, the folded generator vector is read through each
/// round's L and R commitments. This tracks one field coefficient per bank
/// entry: after `j` virtual rounds the vector of length `len = N >> j` satisfies
/// `g_j[i] = sum over m with m mod len == i of coefficients[m] * g_0[m]`,
/// which turns L and R into constant-size `N/2` index-selected MSMs over the
/// bank. The production scheduler periodically replaces this bank with its
/// folded generators; this test helper keeps every fold virtual.
///
/// The coefficients live in [`PREPARATION_CHUNKS`] owned chunks so a round's
/// preparation ([`Self::prepare_round`]) runs as one pool phase: every chunk
/// folds the previous round's challenge into its own coefficients, forms the
/// round's polynomial values from the previous polynomial and the challenge
/// inverse, stages its generators' L/R indices and scalars, materializes its
/// slice of the folded polynomial and returns its part of the round's
/// upper-half inner product. The staged index/scalar buffers are shared
/// with the round's MSM tasks and refilled in place once those have finished.
#[cfg(test)]
pub(super) struct VirtualGeneratorFold {
    /// Coefficient chunks by generator range: chunk `k` owns generators
    /// `k * chunk_len..`, `chunk_len` generators each (the last may be short).
    chunks: Vec<Buffer<Fp>>,
    chunk_len: usize,
    /// The last round's challenge and half, not yet folded into the
    /// coefficients: the next preparation applies it, so each round makes
    /// one coefficient pass instead of two.
    pub(super) pending_challenge: Option<(Fp, usize)>,
    pub(super) left_indices: Arc<Vec<u32>>,
    pub(super) left_scalars: Arc<Buffer<Fp>>,
    pub(super) right_indices: Arc<Vec<u32>>,
    pub(super) right_scalars: Arc<Buffer<Fp>>,
}

/// Generator chunks one round's preparation is split into (initially eight
/// tasks of 256 generators for `N = 2048`).
pub(super) const PREPARATION_CHUNKS: usize = 8;

/// A round's prepared inputs: the round's polynomial (the previous one
/// folded by the pending challenge inverse, or the opened polynomial itself
/// in round 0) and its upper half's inner product with the evaluation
/// powers.
#[cfg(test)]
pub(super) struct RoundPreparation {
    pub(super) polynomial: Buffer<Fp>,
    pub(super) upper_inner_product: Fp,
}

/// Read-only inputs one preparation phase shares with its chunk tasks.
struct PreparationInputs<'a> {
    previous: &'a [Fp],
    powers: &'a [Fp],
    polynomial_fold: Option<Fp>,
    pending_challenge: Option<(Fp, usize)>,
    half: usize,
    chunk_len: usize,
    chunk_count: usize,
}

impl PreparationInputs<'_> {
    /// The round's polynomial value at `index` (below `2 · half`): the
    /// previous polynomial's, folded by the pending challenge inverse.
    #[inline(always)]
    fn value(&self, index: usize) -> Fp {
        match self.polynomial_fold {
            Some(inverse) => {
                self.previous[index].add(&inverse.mul(&self.previous[index + 2 * self.half]))
            }
            None => self.previous[index],
        }
    }

    /// The slice of the round's polynomial chunk `chunk` materializes.
    fn polynomial_range(&self, chunk: usize) -> core::ops::Range<usize> {
        let len = 2 * self.half;
        (chunk * len / self.chunk_count)..((chunk + 1) * len / self.chunk_count)
    }
}

/// Disjoint staging slices for one generator chunk.
struct PreparationChunk<'a> {
    coefficients: &'a mut [Fp],
    left_indices: &'a mut [u32],
    left_scalars: &'a mut [Fp],
    right_indices: &'a mut [u32],
    right_scalars: &'a mut [Fp],
    polynomial: &'a mut [Fp],
}

#[cfg(test)]
impl VirtualGeneratorFold {
    #[cfg(test)]
    pub(super) fn new(generator_count: usize) -> Self {
        Self::new_in(
            generator_count,
            Execution::new(&udon::exec::SerialExecutor, udon::exec::TaskBudget::SERIAL),
        )
    }

    fn new_in(generator_count: usize, execution: Execution<'_>) -> Self {
        let half = generator_count / 2;
        let chunk_len = generator_count.div_ceil(PREPARATION_CHUNKS).max(1);
        let chunks = (0..generator_count)
            .step_by(chunk_len)
            .map(|start| {
                let mut values = execution.buffer(chunk_len.min(generator_count - start), false);
                values.fill(<Fp>::ONE);
                values
            })
            .collect();
        Self {
            chunks,
            chunk_len,
            pending_challenge: None,
            left_indices: Arc::new(alloc::vec![0; half]),
            left_scalars: Arc::new(execution.buffer(half, false)),
            right_indices: Arc::new(alloc::vec![0; half]),
            right_scalars: Arc::new(execution.buffer(half, false)),
        }
    }

    /// Prepares a round whose midpoint is `half` (a power of two): folds the
    /// pending challenge into the coefficients, forms the round's polynomial
    /// from `previous` — folded by `polynomial_fold` (the previous round's
    /// challenge inverse; `previous` then has `4 · half` coefficients) or
    /// taken as is (`2 · half` coefficients) — stages the L/R generator
    /// indices and scalars in ascending generator order, and returns the
    /// materialized polynomial with its upper half's inner product against
    /// `powers[..half]`. One pool phase over the coefficient chunks; the
    /// arithmetic is exact, so the staged scalars equal a serial walk's.
    ///
    /// Fixed generator `m` lands in the folded lower half (the L side) when
    /// `m mod 2 * half < half`, pairing with the upper polynomial
    /// coefficient at its folded index; otherwise it lands in R with the
    /// lower one.
    pub(super) fn prepare_round(
        &mut self,
        execution: super::super::worker::Execution<'_>,
        previous: impl Into<Buffer<Fp>>,
        polynomial_fold: Option<Fp>,
        half: usize,
        powers: &Arc<Vec<Fp>>,
    ) -> Result<RoundPreparation, Error> {
        let previous = previous.into();
        let expected_len = if polynomial_fold.is_some() {
            4 * half
        } else {
            2 * half
        };
        if half == 0
            || !half.is_power_of_two()
            || previous.len() != expected_len
            || powers.len() < half
            || self.chunks.is_empty()
        {
            return Err(Error::InternalInvariant);
        }
        let inputs = PreparationInputs {
            previous: &previous,
            powers,
            polynomial_fold,
            pending_challenge: self.pending_challenge.take(),
            half,
            chunk_len: self.chunk_len,
            chunk_count: self.chunks.len(),
        };
        let mut polynomial = execution.buffer(2 * half, false);
        let mut polynomial_tail = polynomial.as_mut_slice();
        let mut left_indices = Arc::make_mut(&mut self.left_indices).as_mut_slice();
        let mut left_scalars = Arc::make_mut(&mut self.left_scalars).as_mut_slice();
        let mut right_indices = Arc::make_mut(&mut self.right_indices).as_mut_slice();
        let mut right_scalars = Arc::make_mut(&mut self.right_scalars).as_mut_slice();
        let mut jobs = Vec::with_capacity(self.chunks.len());
        // Generator order determines contiguous output spans even when a chunk
        // spans several folded halves. Each task writes its final staging rows.
        let left_before = |m: usize| m / (2 * half) * half + (m % (2 * half)).min(half);
        for (chunk, coefficients) in self.chunks.iter_mut().enumerate() {
            let first = chunk * self.chunk_len;
            let left_len = left_before(first + coefficients.len()) - left_before(first);
            let right_len = coefficients.len() - left_len;
            let (li, remaining) = left_indices.split_at_mut(left_len);
            left_indices = remaining;
            let (ls, remaining) = left_scalars.split_at_mut(left_len);
            left_scalars = remaining;
            let (ri, remaining) = right_indices.split_at_mut(right_len);
            right_indices = remaining;
            let (rs, remaining) = right_scalars.split_at_mut(right_len);
            right_scalars = remaining;
            let (values, remaining) =
                polynomial_tail.split_at_mut(inputs.polynomial_range(chunk).len());
            polynomial_tail = remaining;
            jobs.push((
                chunk,
                PreparationChunk {
                    coefficients,
                    left_indices: li,
                    left_scalars: ls,
                    right_indices: ri,
                    right_scalars: rs,
                    polynomial: values,
                },
            ));
        }
        let upper_inner_product = execution
            .map(jobs, |(chunk, output), _| {
                prepare_chunk::<true>(&inputs, chunk, output)
            })
            .into_iter()
            .fold(<Fp>::ZERO, |sum, partial| sum.add(&partial));
        Ok(RoundPreparation {
            polynomial,
            upper_inner_product,
        })
    }

    /// Records the round's challenge for the upper half; the next preparation
    /// scales the affected coefficients (each absorbs one factor of
    /// `challenge`) as it passes them.
    pub(super) fn apply_challenge(&mut self, challenge: &Fp, half: usize) {
        debug_assert!(self.pending_challenge.is_none());
        self.pending_challenge = Some((*challenge, half));
    }
}

/// One chunk's preparation: the coefficient fold, the staging of its
/// generators, its polynomial slice and its inner-product partial.
fn prepare_chunk<const WRITE_INDICES: bool>(
    inputs: &PreparationInputs<'_>,
    chunk: usize,
    output: PreparationChunk<'_>,
) -> Fp {
    let half = inputs.half;
    let first = chunk * inputs.chunk_len;
    let mut left = output.left_scalars.iter_mut();
    let mut right = output.right_scalars.iter_mut();
    let mut left_indices = output.left_indices.iter_mut();
    let mut right_indices = output.right_indices.iter_mut();
    for (offset, coefficient) in output.coefficients.iter_mut().enumerate() {
        let m = first + offset;
        if let Some((challenge, previous_half)) = inputs.pending_challenge
            && m & previous_half != 0
        {
            *coefficient = coefficient.mul(&challenge);
        }
        let folded_index = m & (half - 1);
        let (destination, value) = if m & half == 0 {
            if WRITE_INDICES {
                *left_indices.next().unwrap() = m as u32;
            }
            (left.next().unwrap(), inputs.value(folded_index + half))
        } else {
            if WRITE_INDICES {
                *right_indices.next().unwrap() = m as u32;
            }
            (right.next().unwrap(), inputs.value(folded_index))
        };
        *destination = coefficient.mul(&value);
    }
    let mut upper = ProductSum::new();
    for (index, value) in inputs.polynomial_range(chunk).zip(output.polynomial) {
        *value = inputs.value(index);
        if index >= half {
            upper.add_product(value, &inputs.powers[index - half]);
        }
    }
    upper.finish()
}

/// Inverts one IPA round challenge under the **retry-on-zero** policy: a
/// zero challenge is a transcript-derived event the prover cannot proceed
/// from, so it surfaces as [`Error::RetryRandomness`] (the caller re-proves
/// with fresh randomness) rather than as an internal invariant. Never
/// batched: one inversion per round is the protocol's schedule.
pub(super) fn invert_ipa_challenge(challenge: &Fp) -> Result<Fp, Error> {
    challenge.invert().ok_or(Error::RetryRandomness)
}
