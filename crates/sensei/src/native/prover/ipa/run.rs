//! Challenge-fenced rounds with periodic generator materialization.

use super::{
    IpaWorkspace, PREPARATION_CHUNKS, PreparationChunk, PreparationInputs,
    generators::{self, Generators},
    invert_ipa_challenge, prepare_chunk,
};
use crate::{
    Error,
    native::{
        buffer::{Buffer, BufferPool},
        commitment::{
            FixedGenerator, MsmWorkspace,
            msm::{self, Raw, SourceIndices},
        },
        curve::{Vesta, VestaPoint, VestaProjective},
        field::{Fp, Fq},
        randomness::IpaRoundBlinds,
        target::{K, N},
        transcript::Transcript,
        worker::{
            Execution,
            run::{self, Coordinator, Work},
        },
    },
};
use alloc::sync::Arc;
use udon::msm::{Bases, execution::ProducedInput};

// A bank of at most 32 generators has too little preparation work to
// amortize eight tasks. Earlier banks keep their producer/MSM overlap.
const LATE_PREPARATION_CHUNKS: usize = 1;

static IDENTITY_INDICES: [u32; N] = {
    assert!(N <= u32::MAX as usize);
    let mut indices = [0; N];
    let mut i = 0;
    while i < N {
        indices[i] = i as u32;
        i += 1;
    }
    indices
};

// Every chunk must stay entirely on one side throughout the phase, including
// its last round. Otherwise its physical indices require the owned writer.
fn static_phase_indices(bank: usize, chunks: usize, half: usize, rounds: usize) -> bool {
    if rounds == 0
        || !half.is_power_of_two()
        || half.checked_mul(2) != Some(bank)
        || bank > IDENTITY_INDICES.len()
        || chunks == 0
        || !bank.is_multiple_of(chunks)
    {
        return false;
    }
    let chunk_len = bank / chunks;
    let Some(last_half) = u32::try_from(rounds - 1)
        .ok()
        .and_then(|shift| half.checked_shr(shift))
    else {
        return false;
    };
    chunk_len.is_power_of_two() && chunk_len <= last_half
}

fn source_indices(
    pool: &BufferPool<u32>,
    chunk: usize,
    chunk_len: usize,
    use_static: bool,
) -> SourceIndices {
    if use_static {
        let first = chunk * chunk_len;
        SourceIndices::Static(&IDENTITY_INDICES[first..first + chunk_len])
    } else {
        SourceIndices::Owned(pool.take(chunk_len, 0, false))
    }
}

/// State carried through each round's `L`, `R`, challenge transcript fence.
///
/// [`super::super::ProverPrefix::finish_ipa`] supplies the masked polynomial
/// after [`super::subtract_ipa_evaluation`] subtracts its opened evaluation,
/// together with the powers of `x = x_3`. The table follows successful rounds;
/// `h` is `half` before the fence and `u` is the challenge squeezed there.
///
/// | Fields | Available to the current round | After [`Finish::finish`] succeeds |
/// | --- | --- | --- |
/// | `previous`, `fold` | Initially the `N` coefficients and `None`. Later, the valid prefix has `4h` coefficients and `fold = Some(u_previous^-1)`. [`PreparationInputs::value`] applies that inverse on demand; [`prepare_chunk`] also writes the current `2h` coefficients into disjoint storage slices. | Copies those slices into `previous[..2h]`, retaining the buffer's full length, then records `fold = Some(u^-1)` for the next preparation. |
/// | `pending` | Initially `None`. Within a generator phase, `Some((u_previous, 2h))` tells each preparation chunk to multiply the affected bank coefficients by the previous challenge before staging L/R. | Records `Some((u, h))`; the bank coefficients still lack this newest challenge. |
/// | `powers`, `x_to_half` | Immutable `powers[i] = x^i` for `i < N/2`; preparation reads `powers[..h]`. Initially `x_to_half = x^(N/2)` is supplied separately, outside that table. | If another round remains, sets `x_to_half = powers[half]` after halving; the powers buffer is never folded or shortened. |
/// | `scale`, `evaluation` | Initially one and zero. The evaluation vector is `scale * x^i`, represented by `powers` and `x_to_half`; `evaluation` is the current polynomial's unscaled inner product. [`Values`] sums the upper-half inner products and derives the lower half using `x_to_half`. | Multiplies `scale` by `1 + u * x^h` and sets `evaluation = lower + upper * u^-1`, avoiding a folded evaluation-vector buffer. |
/// | `z`, `blind` | `z` stays fixed; `blind` starts with the masked polynomial's blind. | Adds `left_blind * u^-1 + right_blind * u` to `blind`; `z` is unchanged. |
/// | `half`, `index` | Initially `N/2` and zero. `2h` is the current polynomial length; `index` counts completed rounds and selects the current round's pre-sampled blinds. | Halves `half` and increments `index`, including at a phase boundary. |
/// | `chunk_len`, `chunk_count` | [`phase`] sets these from the current generator bank, using one chunk for a bank of at most 32 entries and [`PREPARATION_CHUNKS`] otherwise. | Unchanged within the phase; the next phase recomputes them for its materialized bank. |
///
/// Applying a deferred value is logical consumption, not an `Option::take`:
/// preparation leaves both options unchanged. When present, `pending` is
/// applied once per chunk to its own bank entries; polynomial reads apply
/// `fold` without mutating `previous`. The next fence overwrites both options.
/// No next-round
/// preparation is admitted before the current [`Finish`] completes. Thus these
/// folds can join the next round's staging pass without crossing a challenge
/// dependency or overwriting another task's input. Between materializations,
/// bank coefficients represent the virtual generator folds: applying their
/// weights to the staged scalars gives the same L/R MSMs by linearity.
///
/// At a nonfinal phase boundary, [`phase`] combines the bank coefficients with
/// the newest, still-pending challenge to form tensor weights. [`finish`] then
/// calls [`generators::materialize`] and clears only `pending`: the new bank
/// already includes every generator fold, and its next phase starts with unit
/// coefficients. `fold` remains `Some` because the polynomial still needs the
/// newest inverse. At `h = 1`, [`Finish::finish`] instead writes the final `c`
/// directly from the two prepared coefficients and the new inverse, then the
/// updated blind `f`. It leaves `half = 0`, `index = K`, and both options `Some`,
/// with no further preparation or materialization to consume them.
///
/// See the [stage-buffer ownership table](super::super#stage-buffer-ownership)
/// for input transfers and buffer release, and [`Ipa`] for the task fence.
struct Round {
    previous: Buffer<Fp>,
    powers: Buffer<Fp>,
    half: usize,
    fold: Option<Fp>,
    pending: Option<(Fp, usize)>,
    x_to_half: Fp,
    scale: Fp,
    evaluation: Fp,
    z: Fp,
    blind: Fp,
    index: usize,
    chunk_len: usize,
    chunk_count: usize,
}
impl Round {
    fn inputs(&self) -> PreparationInputs<'_> {
        PreparationInputs {
            previous: &self.previous,
            powers: &self.powers,
            polynomial_fold: self.fold,
            pending_challenge: self.pending,
            half: self.half,
            chunk_len: self.chunk_len,
            chunk_count: self.chunk_count,
        }
    }
    fn left_before(&self, m: usize) -> usize {
        m / (2 * self.half) * self.half + (m % (2 * self.half)).min(self.half)
    }
    fn ranges(&self, chunk: usize) -> [core::ops::Range<usize>; 2] {
        let start = chunk * self.chunk_len;
        let left = self.left_before(start)..self.left_before(start + self.chunk_len);
        let right = start - left.start..start + self.chunk_len - left.end;
        [left, right]
    }
}
struct Storage {
    coefficients: Buffer<Fp>,
    left: Arc<Raw<Vesta>>,
    right: Arc<Raw<Vesta>>,
    polynomial: Buffer<Fp>,
    upper: Fp,
}
struct Prepare {
    round: Arc<Round>,
    chunk: usize,
    storage: Storage,
}
impl Work for Prepare {
    fn execute(&mut self) {
        let inputs = self.round.inputs();
        let [left_range, right_range] = self.round.ranges(self.chunk);
        // Fresh phase storage, or Ipa's completed-MSM/restart fence (see Ipa),
        // leaves each source Arc with only this storage owner.
        let left = Arc::get_mut(&mut self.storage.left).expect("previous source readers drained");
        let right = Arc::get_mut(&mut self.storage.right).expect("previous source readers drained");
        let use_static = match (&left.indices, &right.indices) {
            (SourceIndices::Static(_), SourceIndices::Static(_)) => true,
            (SourceIndices::Owned(_), SourceIndices::Owned(_)) => false,
            _ => panic!("paired IPA sources use the same index storage"),
        };
        let output = PreparationChunk {
            coefficients: &mut self.storage.coefficients,
            left_indices: if use_static {
                &mut []
            } else {
                &mut left.indices.owned_mut()[..left_range.len()]
            },
            left_scalars: &mut left.scalars[..left_range.len()],
            right_indices: if use_static {
                &mut []
            } else {
                &mut right.indices.owned_mut()[..right_range.len()]
            },
            right_scalars: &mut right.scalars[..right_range.len()],
            polynomial: &mut self.storage.polynomial[..inputs.polynomial_range(self.chunk).len()],
        };
        self.storage.upper = if use_static {
            prepare_chunk::<false>(&inputs, self.chunk, output)
        } else {
            prepare_chunk::<true>(&inputs, self.chunk, output)
        };
    }
}
struct Values<'i> {
    round: Arc<Round>,
    upper: [Fp; PREPARATION_CHUNKS],
    base: &'i FixedGenerator,
    blind_base: &'i FixedGenerator,
    blinds: [Fp; 2],
    output: Option<ValueOutput>,
}
struct ValueOutput {
    upper: Fp,
    lower: Fp,
    points: [VestaProjective; 2],
}
impl Work for Values<'_> {
    fn execute(&mut self) {
        let upper = self
            .upper
            .iter()
            .fold(<Fp>::ZERO, |sum, value| sum.add(value));
        // The unscaled inner product starts at zero after subtracting the
        // opened evaluation. Only its upper half needs a new dot product;
        // the lower half follows from the running value and x^h.
        let lower = self.round.evaluation.sub(&self.round.x_to_half.mul(&upper));
        let left = upper.mul(&self.round.scale).mul(&self.round.z);
        let right = lower
            .mul(&self.round.scale)
            .mul(&self.round.x_to_half)
            .mul(&self.round.z);
        self.output = Some(ValueOutput {
            upper,
            lower,
            points: if crate::tuning::JOINT_FIXED_SUM {
                core::array::from_fn(|i| {
                    FixedGenerator::sum(
                        [self.base, self.blind_base],
                        &[[left, right][i], self.blinds[i]],
                    )
                })
            } else {
                [self.base.mul(&left), self.base.mul(&right)]
            },
        });
    }
}
struct Blinds<'i> {
    base: &'i FixedGenerator,
    scalars: [Fp; 2],
    points: [VestaProjective; 2],
}
impl Work for Blinds<'_> {
    fn execute(&mut self) {
        if !crate::tuning::JOINT_FIXED_SUM {
            self.points = self.scalars.map(|scalar| self.base.mul(&scalar));
        }
    }
}
struct Finish<'t> {
    round: Arc<Round>,
    storage: [Option<Storage>; PREPARATION_CHUNKS],
    transcript: &'t mut Transcript,
    partials: Buffer<VestaProjective>,
    values: ValueOutput,
    blind_points: [VestaProjective; 2],
    blinds: [Fp; 2],
    result: Result<(), Error>,
}
impl Work for Finish<'_> {
    fn execute(&mut self) {
        self.result = self.finish();
    }
}
impl Finish<'_> {
    fn finish(&mut self) -> Result<(), Error> {
        let middle = self.partials.len() / 2;
        let sum = |points: &[VestaProjective]| {
            points
                .iter()
                .fold(VestaProjective::IDENTITY, |sum, point| sum.add(point))
        };
        let left = sum(&self.partials[..middle])
            .add(&self.values.points[0])
            .add(&self.blind_points[0]);
        let right = sum(&self.partials[middle..])
            .add(&self.values.points[1])
            .add(&self.blind_points[1]);
        let mut points = [VestaPoint::IDENTITY; 2];
        let mut scratch = [Fq::ZERO; 2];
        udon::curve::batch_normalize(&[left, right], &mut points, &mut scratch);
        let [left, right] = points;
        // Randomly blinded L/R may be identity; the transcript rejects those
        // points, so this proof attempt needs fresh randomness.
        self.transcript
            .write_point(&left)
            .map_err(|_| Error::RetryRandomness)?;
        self.transcript
            .write_point(&right)
            .map_err(|_| Error::RetryRandomness)?;
        let challenge = self.transcript.squeeze_challenge();
        let inverse = invert_ipa_challenge(&challenge)?;
        // Ipa::claim admits Finish only after all Prepare/Values readers and
        // active storage have returned; see Ipa's task-fence contract.
        let round = Arc::get_mut(&mut self.round).expect("round tasks drained before challenge");
        for (chunk, storage) in self.storage.iter().take(round.chunk_count).enumerate() {
            let storage = storage
                .as_ref()
                .expect("active preparation storage returned");
            let range = round.inputs().polynomial_range(chunk);
            round.previous[range.clone()].copy_from_slice(&storage.polynomial[..range.len()]);
        }
        round.blind = round
            .blind
            .add(&self.blinds[0].mul(&inverse))
            .add(&self.blinds[1].mul(&challenge));
        if round.half == 1 {
            let c = round.previous[0].add(&inverse.mul(&round.previous[1]));
            self.transcript.write_scalar(&c);
            self.transcript.write_scalar(&round.blind);
        }
        round.fold = Some(inverse);
        round.pending = Some((challenge, round.half));
        round.scale = round
            .scale
            .mul(&<Fp>::ONE.add(&challenge.mul(&round.x_to_half)));
        round.evaluation = self.values.lower.add(&self.values.upper.mul(&inverse));
        round.half /= 2;
        round.index += 1;
        if round.half != 0 {
            round.x_to_half = round.powers[round.half];
        }
        Ok(())
    }
}

#[expect(
    clippy::large_enum_variant,
    reason = "own admitted leases without allocating each task"
)]
enum Job<'a, 'i, 'b, 't> {
    Prepare(Prepare),
    Msm(msm::MsmTask<'a, 'i, 'b, Vesta>),
    Values(Values<'i>),
    Blinds(Blinds<'i>),
    Finish(Finish<'t>),
}
impl Work for Job<'_, '_, '_, '_> {
    fn execute(&mut self) {
        match self {
            Self::Prepare(j) => j.execute(),
            Self::Msm(j) => j.execute(),
            Self::Values(j) => j.execute(),
            Self::Blinds(j) => j.execute(),
            Self::Finish(j) => j.execute(),
        }
    }
}
/// Owns one generator phase under the worker [`Coordinator`] contract.
///
/// On the successful path, `next` counts preparation claims and `remaining`
/// counts chunks not yet returned and published. They start at zero and
/// `chunk_count`, respectively. Once `remaining` reaches zero, `Values` can be
/// claimed; its completion fills `values`, while the independent `Blinds`
/// completion fills `blind_points`.
/// Their claim flags prevent duplicate admission before those outputs arrive.
///
/// `Finish` requires both outputs and the completed MSM results. Claiming it
/// takes `round`, `partials`, `transcript`, the storage slots, and both outputs,
/// leaving their coordinator slots empty. All `Prepare`/`Values` round readers
/// have returned, allowing `Finish` to mutate the sole round Arc. Completion
/// restores the round, partials, transcript, and storage; the consumed outputs
/// stay `None`. For another round in this phase, it resets the counters/flags
/// and restarts the MSMs. MSM completion has dropped task source readers;
/// restart clears source registrations, so the next `Prepare` can mutably
/// borrow its sole left/right Arcs. At a phase end, `result` stops admission
/// and those registrations drop with the coordinator instead. See the
/// [MSM lease lifecycle](msm) for that separate reader/registration distinction.
struct Ipa<'a, 'i, 'b, 't> {
    msm: msm::Coordinator<'a, 'i, 'b, Vesta>,
    round: Option<Arc<Round>>,
    partials: Option<Buffer<VestaProjective>>,
    storage: [Option<Storage>; PREPARATION_CHUNKS],
    next: usize,
    remaining: usize,
    values_claimed: bool,
    values: Option<ValueOutput>,
    blinds_claimed: bool,
    blind_points: Option<[VestaProjective; 2]>,
    round_blinds: &'i [IpaRoundBlinds],
    end_round: usize,
    value_base: &'i FixedGenerator,
    blind_base: &'i FixedGenerator,
    transcript: Option<&'t mut Transcript>,
    result: Option<Result<(), Error>>,
    #[cfg(test)]
    started: Option<std::time::Instant>,
    #[cfg(test)]
    prepare_ns: u128,
    #[cfg(test)]
    batch_ns: u128,
    #[cfg(test)]
    round_prepare_ns: u128,
    #[cfg(test)]
    early_window: bool,
    #[cfg(test)]
    early_rounds: usize,
}
impl<'a, 'i, 'b, 't> Coordinator for Ipa<'a, 'i, 'b, 't> {
    type Task = Job<'a, 'i, 'b, 't>;
    fn claim(&mut self) -> Option<Self::Task> {
        if self.result.is_some() || self.msm.failed() {
            return None;
        }
        let round = self.round.as_ref()?;
        if self.remaining == 0 && !self.values_claimed {
            self.values_claimed = true;
            return Some(Job::Values(Values {
                round: Arc::clone(round),
                upper: core::array::from_fn(|i| {
                    if i < round.chunk_count {
                        self.storage[i].as_ref().unwrap().upper
                    } else {
                        Fp::ZERO
                    }
                }),
                base: self.value_base,
                blind_base: self.blind_base,
                blinds: [
                    self.round_blinds[round.index].left,
                    self.round_blinds[round.index].right,
                ],
                output: None,
            }));
        }
        let blinds = &self.round_blinds[round.index];
        if !self.blinds_claimed {
            self.blinds_claimed = true;
            return Some(Job::Blinds(Blinds {
                base: self.blind_base,
                scalars: [blinds.left, blinds.right],
                points: [VestaProjective::IDENTITY; 2],
            }));
        }
        if let Some(task) = self.msm.claim() {
            #[cfg(test)]
            if self.remaining != 0 && task.writes_partial() {
                self.early_window = true;
            }
            return Some(Job::Msm(task));
        }
        if self.next < round.chunk_count {
            let chunk = self.next;
            self.next += 1;
            return Some(Job::Prepare(Prepare {
                round: Arc::clone(round),
                chunk,
                storage: self.storage[chunk].take().unwrap(),
            }));
        }
        if self.remaining == 0
            && self.values.is_some()
            && self.blind_points.is_some()
            && let Some(results) = self.msm.results()
        {
            #[cfg(test)]
            if let Some(started) = self.started {
                self.batch_ns += started.elapsed().as_nanos() - self.round_prepare_ns;
            }
            let mut partials = self.partials.take().expect("returned round partials");
            assert_eq!(partials.len(), results.len());
            for (output, result) in partials.iter_mut().zip(results) {
                *output = result;
            }
            return Some(Job::Finish(Finish {
                blinds: [blinds.left, blinds.right],
                round: self.round.take().unwrap(),
                storage: core::mem::take(&mut self.storage),
                transcript: self.transcript.take().unwrap(),
                partials,
                values: self.values.take().unwrap(),
                blind_points: self.blind_points.take().unwrap(),
                result: Ok(()),
            }));
        }
        None
    }
    fn complete(&mut self, task: Self::Task) {
        match task {
            Job::Prepare(task) => {
                let [left, right] = task.round.ranges(task.chunk);
                self.msm.sources[0].publish(left, Arc::clone(&task.storage.left));
                self.msm.sources[1].publish(right, Arc::clone(&task.storage.right));
                self.storage[task.chunk] = Some(task.storage);
                self.remaining -= 1;
                #[cfg(test)]
                if self.remaining == 0
                    && let Some(started) = self.started
                {
                    self.round_prepare_ns = started.elapsed().as_nanos();
                    self.prepare_ns += self.round_prepare_ns;
                }
            }
            Job::Msm(task) => self.msm.complete(task),
            Job::Values(task) => self.values = task.output,
            Job::Blinds(task) => self.blind_points = Some(task.points),
            Job::Finish(task) => {
                self.partials = Some(task.partials);
                #[cfg(test)]
                {
                    self.early_rounds += usize::from(self.early_window);
                    self.early_window = false;
                }
                self.transcript = Some(task.transcript);
                self.storage = task.storage;
                if task.result.is_err() || task.round.index == self.end_round {
                    self.result = Some(task.result);
                } else {
                    self.msm.restart();
                    self.next = 0;
                    self.remaining = task.round.chunk_count;
                    self.values_claimed = false;
                    self.blinds_claimed = false;
                    #[cfg(test)]
                    if self.started.is_some() {
                        self.started = Some(std::time::Instant::now());
                    }
                }
                self.round = Some(task.round);
            }
        }
    }
}

#[allow(clippy::too_many_arguments)] // workspaces, generator banks, and round inputs stay separate
pub(super) fn finish(
    workspace: &mut MsmWorkspace,
    ipa_workspace: &mut IpaWorkspace,
    execution: Execution<'_>,
    transcript: &mut Transcript,
    generators: Bases<'_, Vesta>,
    folding_bases: Bases<'_, Vesta>,
    value_base: &FixedGenerator,
    blind_base: &FixedGenerator,
    previous: Buffer<Fp>,
    powers: Buffer<Fp>,
    x_to_half: Fp,
    z: Fp,
    blind: Fp,
    round_blinds: [IpaRoundBlinds; crate::native::randomness::IPA_ROUNDS],
) -> Result<(), Error> {
    let mut round = Round {
        previous,
        powers,
        half: N / 2,
        fold: None,
        pending: None,
        x_to_half,
        scale: <Fp>::ONE,
        evaluation: <Fp>::ZERO,
        z,
        blind,
        index: 0,
        chunk_len: N / PREPARATION_CHUNKS,
        chunk_count: PREPARATION_CHUNKS,
    };
    let mut folded = None;
    #[cfg(test)]
    let mut early_rounds = 0;
    for end_round in crate::tuning::IPA_FOLD_ENDS {
        let original_bank = folded.is_none();
        let bases = folded.as_ref().map_or(generators, Generators::bases);
        let (next, weights, early) = phase(
            workspace,
            ipa_workspace,
            execution,
            transcript,
            bases,
            value_base,
            blind_base,
            round,
            &round_blinds,
            end_round,
        )?;
        round = next;
        #[cfg(test)]
        {
            early_rounds += early;
        }
        #[cfg(not(test))]
        let _ = early;
        if round.half != 0 {
            let started = super::ipa_phase_start();
            folded = Some(generators::materialize(
                &mut ipa_workspace.generators,
                if original_bank { folding_bases } else { bases },
                &weights.values[..weights.len],
                execution,
            )?);
            super::ipa_phase_finish(super::IpaPhase::Generators, started);
            round.pending = None;
        }
    }
    #[cfg(test)]
    crate::native::stage_timing::ipa_early_rounds(early_rounds);
    assert_eq!(round.index, K as usize);
    Ok(())
}

const TENSOR_WEIGHTS: usize = {
    let [a, b, c] = crate::tuning::IPA_FOLD_ENDS;
    assert!(a > 0 && a < b && b < c && c == K as usize);
    let max = if a > b - a { a } else { b - a };
    1 << max
};

struct TensorWeights {
    values: [Fp; TENSOR_WEIGHTS],
    len: usize,
}

#[allow(clippy::too_many_arguments)] // borrowed workspaces and bases accompany the owned round
fn phase(
    workspace: &mut MsmWorkspace,
    ipa_workspace: &mut IpaWorkspace,
    execution: Execution<'_>,
    transcript: &mut Transcript,
    bases: Bases<'_, Vesta>,
    value_base: &FixedGenerator,
    blind_base: &FixedGenerator,
    mut round: Round,
    round_blinds: &[IpaRoundBlinds],
    end_round: usize,
) -> Result<(Round, TensorWeights, usize), Error> {
    let input = ProducedInput::indexed(bases, bases.len() / 2);
    // Keep each first-phase L/R input together at a serial allowance. The
    // phase reuses this plan across rounds; preparation still uses 256-term chunks.
    let source_fragment = if execution.budget.get() == 1 && round.index == 0 {
        input.len()
    } else {
        512
    };
    // Both L/R inputs use halves of the prepared phase bank; a preparation
    // error concerns this internal MSM layout, not the round's random scalars.
    let mut batch = workspace
        .prepare_produced(&[input, input], execution.budget, source_fragment)
        .map_err(|_| Error::InternalInvariant)?;
    let chunk_count = if bases.len() <= 32 {
        LATE_PREPARATION_CHUNKS
    } else {
        PREPARATION_CHUNKS
    };
    let chunk_len = bases.len() / chunk_count;
    let use_static = static_phase_indices(
        bases.len(),
        chunk_count,
        round.half,
        end_round.saturating_sub(round.index),
    );
    round.chunk_len = chunk_len;
    round.chunk_count = chunk_count;
    let round = Arc::new(round);
    let storage = core::array::from_fn(|index| {
        // Inactive slots never publish sources or participate in a fold.
        if index >= chunk_count {
            return None;
        }
        let mut coefficients = execution.buffer(chunk_len, false);
        coefficients.fill(<Fp>::ONE);
        Some(Storage {
            coefficients,
            left: Arc::new(Raw {
                scalars: execution.buffer(chunk_len, false),
                indices: source_indices(&ipa_workspace.indices, index, chunk_len, use_static),
            }),
            right: Arc::new(Raw {
                scalars: execution.buffer(chunk_len, false),
                indices: source_indices(&ipa_workspace.indices, index, chunk_len, use_static),
            }),
            polynomial: execution.buffer(chunk_len, false),
            upper: <Fp>::ZERO,
        })
    });
    let msm = batch.coordinator();
    let partials =
        ipa_workspace
            .partials
            .take(msm.result_count(), VestaProjective::IDENTITY, false);
    let mut ipa = Ipa {
        msm,
        partials: Some(partials),
        round: Some(round),
        storage,
        next: 0,
        remaining: chunk_count,
        values_claimed: false,
        values: None,
        blinds_claimed: false,
        blind_points: None,
        round_blinds,
        end_round,
        value_base,
        blind_base,
        transcript: Some(transcript),
        result: None,
        #[cfg(test)]
        started: super::ipa_phase_start(),
        #[cfg(test)]
        prepare_ns: 0,
        #[cfg(test)]
        batch_ns: 0,
        #[cfg(test)]
        round_prepare_ns: 0,
        #[cfg(test)]
        early_window: false,
        #[cfg(test)]
        early_rounds: 0,
    };
    let started = super::ipa_phase_start();
    run::drive(&mut ipa, execution.budget, &execution);
    super::ipa_phase_finish(super::IpaPhase::Rounds, started);
    #[cfg(test)]
    {
        crate::native::stage_timing::ipa_phase_add(super::IpaPhase::Prepare, ipa.prepare_ns);
        crate::native::stage_timing::ipa_phase_add(super::IpaPhase::Batch, ipa.batch_ns);
    }
    ipa.result.take().unwrap_or(Err(Error::InternalInvariant))?;
    // drive() has completed every claimed task, and Finish returned the round
    // to Ipa. A remaining Arc reader would violate that ownership handoff.
    let round = Arc::try_unwrap(ipa.round.take().unwrap()).map_err(|_| Error::InternalInvariant)?;
    let mut weights = TensorWeights {
        values: [Fp::ZERO; TENSOR_WEIGHTS],
        len: 0,
    };
    if round.half != 0 {
        let (challenge, half) = round.pending.ok_or(Error::InternalInvariant)?;
        // Each block has a single shared coefficient. Preparation has applied
        // all but the last challenge, which was just squeezed at the fence.
        for m in (0..bases.len()).step_by(2 * round.half) {
            let storage = ipa.storage[m / chunk_len].as_ref().unwrap();
            let coefficient = storage.coefficients[m % chunk_len];
            let value = weights
                .values
                .get_mut(weights.len)
                .ok_or(Error::InternalInvariant)?;
            *value = if m & half == 0 {
                coefficient
            } else {
                coefficient.mul(&challenge)
            };
            weights.len += 1;
        }
    }
    #[cfg(test)]
    let early_rounds = ipa.early_rounds;
    #[cfg(not(test))]
    let early_rounds = 0;
    Ok((round, weights, early_rounds))
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{vec, vec::Vec};

    fn words(values: &[Fp]) -> Vec<[u64; 4]> {
        values.iter().map(Fp::montgomery_limbs).collect()
    }

    fn snapshot(storage: &Storage) -> [Vec<[u64; 4]>; 4] {
        [
            words(&storage.coefficients),
            words(&storage.left.scalars),
            words(&storage.right.scalars),
            words(&storage.polynomial),
        ]
    }

    #[test]
    fn static_source_indices_match_owned_preparation() {
        let fields = BufferPool::<Fp>::default();
        let indices = BufferPool::<u32>::default();
        for (bank, chunks, initial_half, rounds, eligible) in [
            (2048, 8, 1024, 3, true),
            (256, 8, 128, 3, true),
            (32, 1, 16, 5, false),
            // A future extra first-phase round would split a 256-entry chunk.
            (2048, 8, 1024, 4, false),
        ] {
            assert_eq!(
                static_phase_indices(bank, chunks, initial_half, rounds),
                eligible
            );
            let chunk_len = bank / chunks;
            for dirty_reuse in [false, true] {
                if dirty_reuse {
                    fields.dirty(Fp::from_u64(91));
                    indices.dirty(u32::MAX);
                }
                for index in 0..rounds {
                    let half = initial_half >> index;
                    let previous_len = if index == 0 { 2 * half } else { 4 * half };
                    let mut previous = fields.take(previous_len, Fp::ZERO, false);
                    for (i, value) in previous.iter_mut().enumerate() {
                        *value = <Fp>::from_u64((i % 23) as u64).neg();
                    }
                    let mut powers = fields.take(half, Fp::ZERO, false);
                    for (i, value) in powers.iter_mut().enumerate() {
                        *value = Fp::from_u64((i % 11) as u64);
                    }
                    let challenge = if dirty_reuse {
                        Fp::ZERO
                    } else {
                        Fp::from_u64(17)
                    };
                    let round = Arc::new(Round {
                        previous,
                        powers,
                        half,
                        fold: (index != 0).then_some(challenge),
                        pending: (index != 0).then_some((challenge, 2 * half)),
                        x_to_half: Fp::ONE,
                        scale: Fp::ONE,
                        evaluation: Fp::ZERO,
                        z: Fp::ONE,
                        blind: Fp::ZERO,
                        index,
                        chunk_len,
                        chunk_count: chunks,
                    });
                    let mut published = [vec![u32::MAX; bank / 2], vec![u32::MAX; bank / 2]];
                    for chunk in 0..chunks {
                        let make_storage = |use_static| {
                            let mut coefficients = fields.take(chunk_len, Fp::ZERO, false);
                            for (i, value) in coefficients.iter_mut().enumerate() {
                                *value = Fp::from_u64(((chunk * chunk_len + i) % 19) as u64);
                            }
                            Storage {
                                coefficients,
                                left: Arc::new(Raw {
                                    scalars: fields.take(chunk_len, Fp::from_u64(91), true),
                                    indices: source_indices(&indices, chunk, chunk_len, use_static),
                                }),
                                right: Arc::new(Raw {
                                    scalars: fields.take(chunk_len, Fp::from_u64(91), true),
                                    indices: source_indices(&indices, chunk, chunk_len, use_static),
                                }),
                                polynomial: fields.take(chunk_len, Fp::from_u64(91), true),
                                upper: Fp::from_u64(91),
                            }
                        };
                        let mut reference = Prepare {
                            round: Arc::clone(&round),
                            chunk,
                            storage: make_storage(false),
                        };
                        let mut candidate = Prepare {
                            round: Arc::clone(&round),
                            chunk,
                            storage: make_storage(eligible),
                        };
                        if eligible && index == 0 && chunk == 0 {
                            // Static bytes do not remove either scalar-owner drain fence.
                            for left in [true, false] {
                                let reader = Arc::clone(if left {
                                    &candidate.storage.left
                                } else {
                                    &candidate.storage.right
                                });
                                let before = snapshot(&candidate.storage);
                                assert!(
                                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                        candidate.execute();
                                    }))
                                    .is_err()
                                );
                                assert_eq!(snapshot(&candidate.storage), before);
                                assert_eq!(
                                    candidate.storage.upper.montgomery_limbs(),
                                    <Fp>::from_u64(91).montgomery_limbs()
                                );
                                drop(reader);
                            }
                        }
                        reference.execute();
                        candidate.execute();
                        assert_eq!(snapshot(&candidate.storage), snapshot(&reference.storage));
                        assert_eq!(
                            candidate.storage.upper.montgomery_limbs(),
                            reference.storage.upper.montgomery_limbs()
                        );
                        for (side, (actual, expected)) in [
                            (&candidate.storage.left, &reference.storage.left),
                            (&candidate.storage.right, &reference.storage.right),
                        ]
                        .into_iter()
                        .enumerate()
                        {
                            assert_eq!(
                                matches!(&actual.indices, SourceIndices::Static(_)),
                                eligible
                            );
                            let range = round.ranges(chunk)[side].clone();
                            assert_eq!(
                                &actual.indices[..range.len()],
                                &expected.indices[..range.len()]
                            );
                            published[side][range.clone()]
                                .copy_from_slice(&actual.indices[..range.len()]);
                        }
                    }
                    for (side, actual) in published.iter().enumerate() {
                        let expected: Vec<_> = (0..bank)
                            .filter(|m| usize::from(m & half != 0) == side)
                            .map(|m| m as u32)
                            .collect();
                        assert_eq!(*actual, expected);
                    }
                }
            }
        }
        for (bank, chunks, half, rounds) in [
            (2048, 0, 1024, 3),
            (2048, 3, 1024, 3),
            (2048, 8, 1024, 0),
            (2048, 8, 1024, usize::MAX),
            (4096, 8, 2048, 3),
            (2048, 8, 512, 3),
        ] {
            assert!(!static_phase_indices(bank, chunks, half, rounds));
        }
    }
}
