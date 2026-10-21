//! Residue producers, folds, class inverses, and commitments on one frontier.

use super::*;
use crate::native::{
    buffer::Buffer,
    commitment::{
        FixedGenerator, MsmWorkspace,
        msm::{self, Raw, SourceIndices},
    },
    curve::{Vesta, VestaProjective},
    field::PallasBase,
    polynomial::FftWorkspace,
    worker::{
        Execution,
        run::{self, Coordinator, Work},
    },
};
use core::num::NonZeroUsize;
use udon::{
    exec::{
        ExecutionOptions,
        execution::{Outcome, ReadView, Task},
    },
    fft::{
        Direction, ElementOrder, ExpansionOrder, ExpansionStorage, InputSupport, InverseScale,
        StorageLayout, TransformRequest,
        execution::{
            self as fft, ExpansionBank, ExpansionPlan, ExpansionRun, FftKernel, FftPlan, FftRun,
            InterpolationPlan, InterpolationRun,
        },
    },
    msm::execution::ProducedInput,
};

const RESIDUES: usize = EXTENDED_N / N;
const WINDOWS: usize = N / FOLD_CHUNK_ROWS;
const EXTENDED_LANE: usize = 0;
const CLASS_4N_LANE: usize = 1;
const LOOKUP_LANE: usize = 4;
/// N-element fragments per scheduler lane. The first four lanes follow
/// [`fold_order::DegreeClass`]: Extended (8N), Class4N, Class2N, then ClassN.
/// The separate lookup lane repeats four residues because its branch is not
/// separately divisible by X^N - 1. Its remainder survives interpolation until
/// [`correct_lookup`] lifts it into the extended lane's coefficient pieces.
const CLASS_RESIDUES: [usize; 5] = [8, 4, 2, 1, 4];
// Keep one producer residue ahead of the oldest fold. Consumers retain their
// complete bundles, so waiting producers cannot consume the fold's capacity.
const RESIDUE_LEAD: usize = 2;

fn fields(values: Buffer<Fp>) -> Arc<Raw<Vesta>> {
    Arc::new(Raw {
        scalars: values,
        indices: SourceIndices::Static(&[]),
    })
}
fn recover(values: Arc<Raw<Vesta>>) -> Buffer<Fp> {
    Arc::try_unwrap(values)
        .unwrap_or_else(|_| panic!("field readers drained"))
        .scalars
}
#[derive(Default)]
struct Read(Option<Arc<Raw<Vesta>>>);
impl ReadView<Fp> for Read {
    fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |v| v.scalars.len())
    }
    fn get(&self, i: usize) -> Option<&Fp> {
        self.0.as_ref()?.scalars.get(i)
    }
    fn contiguous(&self, range: core::ops::Range<usize>) -> Option<&[Fp]> {
        self.0.as_ref()?.scalars.get(range)
    }
}
struct Lease {
    values: Arc<Raw<Vesta>>,
    pair: Option<Arc<Raw<Vesta>>>,
    source: Read,
}
impl fft::Resources<PallasBase> for Lease {
    fn buffers(&mut self) -> fft::Buffers<'_, PallasBase> {
        fft::Buffers {
            values: &mut Arc::get_mut(&mut self.values)
                .expect("exclusive FFT fragment")
                .scalars,
            pair: self.pair.as_mut().map_or(&mut [], |pair| {
                &mut Arc::get_mut(pair).expect("exclusive FFT pair").scalars[..]
            }),
            source: &self.source,
            factor: &[],
        }
    }
}

struct Expansion<'a, 't> {
    column: usize,
    stride: usize,
    run: ExpansionRun<'a, 't, PallasBase, 1>,
    coefficients: Option<Arc<Raw<Vesta>>>,
}
struct Expand<'a, 't> {
    index: usize,
    bank: ExpansionBank,
    task: Task<'a, FftKernel<'t, PallasBase>, Lease>,
}
impl Work for Expand<'_, '_> {
    fn execute(&mut self) {
        self.task.execute().expect("fresh expansion task");
    }
}

enum Application<'t> {
    Instance {
        column: usize,
        input: LagrangeFormInput,
        target: &'t FixedTarget,
        result: Option<Result<ExtendedCoset, Error>>,
    },
    Tables {
        target: &'t FixedTarget,
        theta: Fp,
        result: Option<Result<Vec<Arc<ExtendedCoset>>, Error>>,
    },
}
struct Apply<'t, 'e> {
    job: Application<'t>,
    execution: Execution<'e>,
}
impl Work for Apply<'_, '_> {
    fn execute(&mut self) {
        let execution = self.execution.serial();
        match &mut self.job {
            Application::Instance {
                input,
                target,
                result,
                ..
            } => {
                let LagrangeFormInput::SparseInstance { statements, index } = input else {
                    unreachable!()
                };
                // NativeStatement supplies the fixed prefix width; target
                // preparation supplies its matching support coset and FFT.
                *result = Some(
                    target
                        .prepared_instance()
                        .coset(&*statements[*index], target.fft(), execution)
                        .map_err(|_| Error::InternalInvariant),
                );
            }
            Application::Tables {
                target,
                theta,
                result,
            } => {
                *result = Some(
                    target
                        .lookup_preparation()
                        .compress_cosets(*theta, target, execution)
                        .and_then(|columns| {
                            share_compressed_tables(target.lookup_preparation().sources(), columns)
                        }),
                );
            }
        }
    }
}

struct Build<'t> {
    residue: usize,
    base: Arc<FoldPlan<'t>>,
    columns: Vec<ExtendedCoset>,
    tables: Vec<Arc<ExtendedCoset>>,
    result: Option<Arc<FoldPlan<'t>>>,
}
impl Work for Build<'_> {
    fn execute(&mut self) {
        let count = self.base.action_plans.len();
        let mut columns = core::mem::take(&mut self.columns).into_iter();
        let instance_cosets = columns.by_ref().take(count).collect();
        let advice_cosets = (0..count)
            .map(|_| columns.by_ref().take(ADVICE_COLUMNS).collect())
            .collect();
        let lookup_cosets = (0..count)
            .map(|_| {
                core::array::from_fn(|lookup| LookupCosets {
                    permuted_input: columns.next().expect("completed input residue"),
                    permuted_table: columns.next().expect("completed table residue"),
                    compressed_table: Arc::clone(&self.tables[lookup]),
                })
            })
            .collect();
        let inputs = FoldInputs {
            instance_cosets,
            advice_cosets,
            lookup_cosets,
            common: Arc::clone(&self.base.inputs.common),
        };
        assert!(columns.next().is_none());
        self.result = Some(Arc::new(FoldPlan {
            target: self.base.target,
            inputs,
            constants: Arc::clone(&self.base.constants),
            action_plans: Arc::clone(&self.base.action_plans),
        }));
    }
}
struct Fold<'t, 'e> {
    #[cfg(test)]
    elapsed_ns: u128,
    window: FoldWindow,
    plan: Arc<FoldPlan<'t>>,
    execution: Execution<'e>,
    chunks: [Buffer<Fp>; 5],
    result: Result<(), Error>,
}
impl Work for Fold<'_, '_> {
    fn execute(&mut self) {
        #[cfg(test)]
        let started = std::time::Instant::now();
        self.result = self.plan.fold_rows(
            self.execution,
            self.window,
            self.chunks.each_mut().map(|chunk| &mut chunk[..]),
        );
        #[cfg(test)]
        {
            self.elapsed_ns = started.elapsed().as_nanos();
        }
    }
}
struct Scatter<'e> {
    residue: usize,
    chunks: Vec<[Buffer<Fp>; 5]>,
    execution: Execution<'e>,
    result: [Option<Arc<Raw<Vesta>>>; 5],
}
impl Work for Scatter<'_> {
    fn execute(&mut self) {
        for (class, residues) in CLASS_RESIDUES.into_iter().enumerate() {
            if !self.residue.is_multiple_of(RESIDUES / residues) {
                continue;
            }
            let mut values = self.execution.buffer(N, false);
            for (window, chunks) in self.chunks.iter().enumerate() {
                for (offset, value) in chunks[class].iter().enumerate() {
                    let k = window * FOLD_CHUNK_ROWS + offset;
                    values[k.reverse_bits() >> (usize::BITS - K)] = *value;
                }
            }
            self.result[class] = Some(fields(values));
        }
        self.chunks.clear();
    }
}

struct Interpolate<'a, 't> {
    class: usize,
    first: usize,
    pair: Option<usize>,
    task: Task<'a, FftKernel<'t, PallasBase>, Lease>,
}
impl Work for Interpolate<'_, '_> {
    fn execute(&mut self) {
        self.task.execute().expect("fresh inverse task");
    }
}
struct Add<'a> {
    target: usize,
    class: usize,
    first: usize,
    task: Task<'a, fft::AdditionKernel<PallasBase>, Lease>,
}
impl Work for Add<'_> {
    fn execute(&mut self) {
        self.task.execute().expect("fresh lift task");
    }
}

/// Converts the 4N interpolant of L/(X^N - 1), deg L < 4N, into the
/// blocks of its 8N interpolant. Write L = (X^N - 1)q + r. On an mN
/// coset with shift s, the interpolant is
///
/// q + r/(s^(mN) - 1) * (1 + X^N + ... + X^((m-1)N)).
///
/// Thus the fourth 4N block is u = r/(s^(4N) - 1). With
/// v = u/(s^(4N) + 1), subtract u and add v in the first three blocks,
/// then repeat v in all five remaining 8N blocks. Here s = ZETA and
/// N = 2 mod 3, so 1/(s^(4N) + 1) = -ZETA^2.
fn correct_lookup([a, b, c, remainder]: [&mut [Fp]; 4]) {
    const _: () = assert!(N % 3 == 2);
    let scale = <Fp>::ZETA.square().neg();
    for (((a, b), c), u) in a.iter_mut().zip(b).zip(c).zip(remainder) {
        let v = u.mul(&scale);
        let correction = v.sub(u);
        *a = a.add(&correction);
        *b = b.add(&correction);
        *c = c.add(&correction);
        *u = v;
    }
}

struct CorrectLookup {
    blocks: [Arc<Raw<Vesta>>; 4],
}
impl Work for CorrectLookup {
    fn execute(&mut self) {
        correct_lookup(
            self.blocks
                .each_mut()
                .map(|block| &mut Arc::get_mut(block).expect("exclusive lookup block").scalars[..]),
        );
    }
}
struct AddLookup {
    piece: usize,
    values: Arc<Raw<Vesta>>,
    source: Arc<Raw<Vesta>>,
}
impl Work for AddLookup {
    fn execute(&mut self) {
        let values = &mut Arc::get_mut(&mut self.values)
            .expect("exclusive quotient piece")
            .scalars;
        for (value, source) in values.iter_mut().zip(self.source.scalars.iter()) {
            *value = value.add(source);
        }
    }
}
struct Blind<'t> {
    mask: Option<(&'t [FixedGenerator], [Fp; K as usize])>,
    index: usize,
    base: &'t FixedGenerator,
    scalar: Fp,
    point: VestaProjective,
}
impl Work for Blind<'_> {
    fn execute(&mut self) {
        self.point = if let Some((bases, scalars)) = &self.mask {
            let tables: [&FixedGenerator; K as usize + 1] = core::array::from_fn(|i| {
                if i == K as usize {
                    self.base
                } else {
                    &bases[i]
                }
            });
            let scalars = core::array::from_fn(|i| {
                if i == K as usize {
                    self.scalar
                } else {
                    scalars[i]
                }
            });
            FixedGenerator::sum(tables, &scalars)
        } else {
            self.base.mul(&self.scalar)
        };
    }
}

#[allow(clippy::large_enum_variant)] // Own the admitted lease without a heap allocation for each task.
enum Job<'a, 't, 'b, 'e> {
    Expand(Expand<'a, 't>),
    Apply(Apply<'t, 'e>),
    Build(Build<'t>),
    Fold(Fold<'t, 'e>),
    Scatter(Scatter<'e>),
    Interpolate(Interpolate<'a, 't>),
    Add(Add<'a>),
    CorrectLookup(CorrectLookup),
    AddLookup(AddLookup),
    Msm(msm::MsmTask<'a, 't, 'b, Vesta>),
    Blind(Blind<'t>),
}
impl Work for Job<'_, '_, '_, '_> {
    fn execute(&mut self) {
        match self {
            Self::Expand(t) => t.execute(),
            Self::Apply(t) => t.execute(),
            Self::Build(t) => t.execute(),
            Self::Fold(t) => t.execute(),
            Self::Scatter(t) => t.execute(),
            Self::Interpolate(t) => t.execute(),
            Self::Add(t) => t.execute(),
            Self::CorrectLookup(t) => t.execute(),
            Self::AddLookup(t) => t.execute(),
            Self::Msm(t) => t.execute(),
            Self::Blind(t) => t.execute(),
        }
    }
}

/// State and owned buffers for one quotient window.
///
/// [`Coordinator::claim`] first scans residues for `Build`/`Scatter`, then
/// takes a `Blind`, then rotates among folds, applications/expansions, inverses,
/// additions, and MSMs. Applications precede expansions within their turn.
/// Output expansions stay within `RESIDUE_LEAD` of the first residue whose
/// `scatter_done` is false; the cursor rotates among columns. Each admitted job
/// owns its complete resources and returns them through `complete`.
///
/// The table describes successful execution. Recorded errors stop new claims;
/// [`run::drive`] also calls `complete` after a task panic before propagating it,
/// so completion flags alone do not certify partially executed jobs.
/// Here `r`, `c`, `w`, and `p` denote residue, column/class, fold window, and piece.
/// `classes` holds N-element fragments for the 8N, 4N, 2N, N, and separate 4N
/// lookup banks, with fragment counts given by `CLASS_RESIDUES`.
///
/// | Job/claim | Prerequisites | Claimed resources | Completion updates | Final readers / release |
/// | --- | --- | --- | --- | --- |
/// | `Apply(Instance)` | Queued sparse instance | Instance input and target | Fill every `forms[c][r]`; decrement `forms_left` | `Build` then `Fold`; no retained coefficients |
/// | `Apply(Tables)` | Queued table application | Target and theta | Set `tables` | Shared by builds/folds; coordinator retains tables until it drops |
/// | `Expand(Input)` | Ready expansion request | Take the input/coefficient bank | Restore the transformed bank | Output expansions read its coefficients |
/// | `Expand(Output)` | Ready request; `r * stride < first_unscattered + RESIDUE_LEAD` | New N-element buffer and shared coefficient read | Drop the read; publish `forms[c][r * stride]`; after the column's final residue, move coefficients to `coefficients[c]` and decrement `forms_left` | Residue: `Build`/`Fold`; coefficients: `Output::columns` for opening |
/// | `Build` | Not `built[r]`; tables and all `forms[c][r]` present | Set `built[r]`; take residue forms; share base and tables | Publish the residue plan in `folds[r]` | Fold jobs own the plan through their final read |
/// | `Fold` | Plan present; `next_fold[r] < WINDOWS` | Advance `next_fold[r]`; clone plan; acquire five class chunks (empty off-class) | Store `chunks[r][w]` | `Scatter` consumes chunks; the last plan owner releases residue inputs |
/// | `Scatter` | Not claimed; every chunk window present | Set `scatter_claimed[r]`; take all chunks | Publish bit-reversed class fragments; increment `class_ready[c]` and `scattered`; set `scatter_done[r]` | Inverses consume fragments; scatter drops chunks after copying |
/// | `Interpolate` | `class_ready[c] == CLASS_RESIDUES[c]`; ready FFT task; exclusive fragments | Take the first fragment and optional pair | Restore fragments; set `inverted[c]` when that class inverse completes | Ordinary classes feed `Add`; lookup feeds correction; the extended lane receives additions |
/// | `Add` | Interpolation addition ready (source and extended inverses complete here); exclusive target | Take target fragment; share source fragment | Drop source read; restore target; decrement its `additions[p]`; clear source class on `published.released` | Last addition receipt releases that ordinary class bank |
/// | `CorrectLookup` | Lookup inverted; not `correction_claimed` | Set claim flag; take all four lookup blocks | Restore blocks; set `lookup_corrected` | `AddLookup` reads corrected blocks, repeating block 3 for pieces 3 through 7 |
/// | `AddLookup` | Lookup corrected; extended lane inverted; piece unclaimed and exclusive | Set `lookup_additions[p]`; take piece; share lookup block | Restore piece; decrement `additions[p]`; increment `lookup_added`; clear lookup bank after all pieces | Last job's source drops on completion, releasing the lookup bank |
/// | `publish_pieces` (inline) | No error; extended lane inverted; `additions[p] == 0`; not `pieces[p]` | Share final piece with MSM when `commit` | Set `pieces[p]` | Immutable MSM reads, then `Output::pieces`; publication can precede other pieces' additions |
/// | `Msm` | MSM frontier ready and required sources/resources available | Delegate complete lease to MSM coordinator | Delegate receipt; release task source reads | [`execute`] combines results with `blind_points` |
/// | `Blind` | Next blind exists (`commit` only) | Scalar, fixed base, and optional fixed mask bases/scalars | Store `blind_points[index]` | [`execute`] combines with MSM result, including the mask |
///
/// Claim flags and counts are distinct from completion: `built` and
/// `scatter_claimed` prevent duplicate claims, and `next_fold` counts admitted
/// windows. `class_ready` counts published scatter fragments, not currently
/// available leases; a taken class slot is `None` until its task returns it.
/// Mutable class claims require exclusive ownership. `additions[p]` initially
/// counts one lookup addition plus each ordinary smaller class covering `p`.
/// `forms_done` records `forms_left == 0` with tables present;
/// `interpolation_done` records the ordinary interpolation's completion plus
/// `lookup_added == RESIDUES`. Neither flag is a barrier for early consumers.
/// Dense4N columns prefill unused odd residues with pending forms; only even
/// residues read those columns.
///
/// The last `Build` claim drops the coordinator's `base`; the last `Fold`
/// claim for a residue drops its `folds[r]`. Admitted jobs retain their own
/// references, so residue inputs and shared product cosets survive their final
/// fold readers. Compressed tables additionally remain owned by `tables`.
/// After the driver drains and results are checked, [`execute`] clears MSM
/// sources before unwrapping the extended lane into `Output::pieces`; dense input
/// coefficients move into `Output::columns`. These returned buffers survive for
/// window combination and opening. Dropped pooled buffers return on their last
/// owner; returning a coefficient buffer here transfers it, without recycling it.
/// With `commit == false`, pieces are still marked ready, but no MSM source is
/// published and no MSM or blind job is admitted.
struct Quotient<'a, 't, 'b, 'e> {
    execution: Execution<'e>,
    application_execution: Execution<'e>,
    expansions: Vec<Expansion<'a, 't>>,
    cursor: usize,
    applications: std::vec::IntoIter<Application<'t>>,
    base: Option<Arc<FoldPlan<'t>>>,
    tables: Option<Vec<Arc<ExtendedCoset>>>,
    forms: Vec<[Option<ExtendedCoset>; RESIDUES]>,
    coefficients: Vec<Option<SharedPoly>>,
    built: [bool; RESIDUES],
    folds: [Option<Arc<FoldPlan<'t>>>; RESIDUES],
    next_fold: [usize; RESIDUES],
    chunks: [Vec<Option<[Buffer<Fp>; 5]>>; RESIDUES],
    scatter_claimed: [bool; RESIDUES],
    scatter_done: [bool; RESIDUES],
    scattered: usize,
    interpolation: InterpolationRun<'a, 't, PallasBase, 4>,
    lookup_inverse: FftRun<'a, 't, PallasBase>,
    classes: [Vec<Option<Arc<Raw<Vesta>>>>; 5],
    class_ready: [usize; 5],
    inverted: [bool; 5],
    correction_claimed: bool,
    lookup_corrected: bool,
    lookup_additions: [bool; RESIDUES],
    lookup_added: usize,
    interpolation_done: bool,
    additions: [usize; RESIDUES],
    pieces: [bool; RESIDUES],
    commit: bool,
    msm: msm::Coordinator<'a, 't, 'b, Vesta>,
    blinds: core::iter::Take<core::array::IntoIter<(usize, Fp), { RESIDUES + 1 }>>,
    blind_base: &'t FixedGenerator,
    mask: Option<(&'t [FixedGenerator], [Fp; K as usize])>,
    blind_points: [Option<VestaProjective>; RESIDUES + 1],
    next_kind: usize,
    error: bool,
    forms_left: usize,
    forms_done: bool,
    #[cfg(test)]
    timing: &'e mut crate::native::stage_timing::QuotientRecorder,
}
impl<'a, 't, 'b, 'e> Quotient<'a, 't, 'b, 'e> {
    fn claim_expansion(&mut self) -> Option<Job<'a, 't, 'b, 'e>> {
        if let Some(job) = self.applications.next() {
            return Some(Job::Apply(Apply {
                job,
                execution: self.application_execution,
            }));
        }
        let first_unscattered = self.scatter_done.iter().take_while(|&&done| done).count();
        for offset in 0..self.expansions.len() {
            let index = (self.cursor + offset) % self.expansions.len();
            let expansion = &mut self.expansions[index];
            let mut ready = [None];
            if expansion.run.ready_slot_from(0, 0, &mut ready) == 0 {
                continue;
            }
            let request = ready[0].take().unwrap();
            assert_eq!(request.task.write.1, 0..N);
            assert!(request.task.pair.is_none());
            let bank = request.values;
            if matches!(bank, ExpansionBank::Output(residue) if residue * expansion.stride >= first_unscattered + RESIDUE_LEAD)
            {
                continue;
            }
            let (values, source) = match bank {
                ExpansionBank::Input => (expansion.coefficients.take().unwrap(), Read::default()),
                ExpansionBank::Output(_) => (
                    fields(self.execution.buffer(N, false)),
                    Read(Some(Arc::clone(expansion.coefficients.as_ref().unwrap()))),
                ),
                ExpansionBank::Coefficients => unreachable!(),
            };
            let task = expansion
                .run
                .try_claim(request, || {
                    Some(Lease {
                        values,
                        pair: None,
                        source,
                    })
                })
                .expect("current expansion")
                .unwrap();
            self.cursor = (index + 1) % self.expansions.len();
            return Some(Job::Expand(Expand { index, bank, task }));
        }
        None
    }
    fn claim_fold(&mut self) -> Option<Job<'a, 't, 'b, 'e>> {
        for residue in 0..RESIDUES {
            let Some(plan) = &self.folds[residue] else {
                continue;
            };
            let window = self.next_fold[residue];
            if window == WINDOWS {
                continue;
            }
            self.next_fold[residue] += 1;
            let job = Fold {
                #[cfg(test)]
                elapsed_ns: 0,
                window: FoldWindow {
                    residue,
                    k_offset: window * FOLD_CHUNK_ROWS,
                },
                plan: Arc::clone(plan),
                execution: self.execution,
                chunks: core::array::from_fn(|class| {
                    self.execution.buffer(
                        if residue.is_multiple_of(RESIDUES / CLASS_RESIDUES[class]) {
                            FOLD_CHUNK_ROWS
                        } else {
                            0
                        },
                        false,
                    )
                }),
                result: Ok(()),
            };
            if window + 1 == WINDOWS {
                self.folds[residue] = None;
            }
            #[cfg(test)]
            if !self.forms_done {
                self.timing.early_consumers[0] += 1;
            }
            return Some(Job::Fold(job));
        }
        None
    }
    fn claim_inverse(&mut self) -> Option<Job<'a, 't, 'b, 'e>> {
        for class in (0..CLASS_RESIDUES.len()).rev() {
            if self.class_ready[class] != CLASS_RESIDUES[class] {
                continue;
            }
            let mut ready = [None];
            let mut cursor = 0;
            while (if class == LOOKUP_LANE {
                self.lookup_inverse.ready_from(cursor, &mut ready)
            } else {
                self.interpolation
                    .ready_transform_from(class, cursor, &mut ready)
            }) != 0
            {
                let request = ready[0].take().unwrap();
                cursor = request.key.index() + 1;
                assert_eq!(request.write.0, fft::Bank::Values);
                assert!(request.read.is_none());
                let first = request.write.1.start / N;
                let pair = request.pair.as_ref().map(|r| r.start / N);
                let row = &mut self.classes[class];
                if !exclusive(&row[first]) || pair.is_some_and(|i| !exclusive(&row[i])) {
                    continue;
                }
                let lease = Lease {
                    values: row[first].take().unwrap(),
                    pair: pair.map(|i| row[i].take().unwrap()),
                    source: Read::default(),
                };
                let task = (if class == LOOKUP_LANE {
                    self.lookup_inverse.try_claim(request, || Some(lease))
                } else {
                    self.interpolation
                        .try_claim_transform(class, request, || Some(lease))
                })
                .expect("current class transform")
                .unwrap();
                #[cfg(test)]
                if self.scattered < RESIDUES {
                    self.timing.early_consumers[1] += 1;
                }
                return Some(Job::Interpolate(Interpolate {
                    class,
                    first,
                    pair,
                    task,
                }));
            }
        }
        None
    }
    fn claim_addition(&mut self) -> Option<Job<'a, 't, 'b, 'e>> {
        if self.inverted[LOOKUP_LANE] && !self.correction_claimed {
            self.correction_claimed = true;
            return Some(Job::CorrectLookup(CorrectLookup {
                blocks: core::array::from_fn(|block| {
                    self.classes[LOOKUP_LANE][block].take().unwrap()
                }),
            }));
        }
        if self.lookup_corrected && self.inverted[EXTENDED_LANE] {
            for piece in 0..RESIDUES {
                if !self.lookup_additions[piece] && exclusive(&self.classes[EXTENDED_LANE][piece]) {
                    self.lookup_additions[piece] = true;
                    return Some(Job::AddLookup(AddLookup {
                        piece,
                        values: self.classes[EXTENDED_LANE][piece].take().unwrap(),
                        source: Arc::clone(
                            self.classes[LOOKUP_LANE][piece.min(3)].as_ref().unwrap(),
                        ),
                    }));
                }
            }
        }
        for class in CLASS_4N_LANE..LOOKUP_LANE {
            let mut ready = [None];
            let mut cursor = 0;
            while self
                .interpolation
                .ready_addition_from(class, cursor, &mut ready)
                != 0
            {
                let request = ready[0].take().unwrap();
                cursor = request.key.index() + 1;
                let target = request.target;
                let first = request.write.start / N;
                if !exclusive(&self.classes[target][first]) {
                    continue;
                }
                let source = Read(Some(Arc::clone(
                    self.classes[class][first].as_ref().unwrap(),
                )));
                let values = self.classes[target][first].take().unwrap();
                let task = self
                    .interpolation
                    .try_claim_addition(class, request, || {
                        Some(Lease {
                            values,
                            pair: None,
                            source,
                        })
                    })
                    .expect("current lift")
                    .unwrap();
                return Some(Job::Add(Add {
                    class,
                    target,
                    first,
                    task,
                }));
            }
        }
        None
    }
    fn publish_pieces(&mut self) {
        if self.error || !self.inverted[EXTENDED_LANE] {
            return;
        }
        for piece in 0..RESIDUES {
            if !self.pieces[piece] && self.additions[piece] == 0 {
                let values = self.classes[EXTENDED_LANE][piece]
                    .as_ref()
                    .expect("final coefficient fragment");
                if self.commit {
                    self.msm.sources[piece].publish(0..N, Arc::clone(values));
                }
                self.pieces[piece] = true;
            }
        }
    }
    fn mark_forms(&mut self) {
        if !self.forms_done && self.forms_left == 0 && self.tables.is_some() {
            self.forms_done = true;
            #[cfg(test)]
            {
                self.timing
                    .mark(crate::native::stage_timing::QuotientStage::Forms);
                self.timing
                    .mark(crate::native::stage_timing::QuotientStage::LookupForms);
            }
        }
    }
    fn mark_interpolation(&mut self) {
        if !self.interpolation_done
            && self.interpolation.is_complete()
            && self.lookup_added == RESIDUES
        {
            self.interpolation_done = true;
            #[cfg(test)]
            self.timing
                .mark(crate::native::stage_timing::QuotientStage::Interpolation);
        }
    }
}
fn exclusive(values: &Option<Arc<Raw<Vesta>>>) -> bool {
    values.as_ref().is_some_and(|v| Arc::strong_count(v) == 1)
}
impl<'a, 't, 'b, 'e> Coordinator for Quotient<'a, 't, 'b, 'e> {
    type Task = Job<'a, 't, 'b, 'e>;
    fn claim(&mut self) -> Option<Self::Task> {
        if self.error
            || self.msm.failed()
            || self.interpolation.is_failed()
            || self.lookup_inverse.is_failed()
        {
            return None;
        }
        for residue in 0..RESIDUES {
            if !self.built[residue]
                && let Some(tables) = self.tables.as_ref()
                && self.forms.iter().all(|column| column[residue].is_some())
            {
                self.built[residue] = true;
                let job = Build {
                    residue,
                    base: Arc::clone(self.base.as_ref().unwrap()),
                    columns: self
                        .forms
                        .iter_mut()
                        .map(|column| column[residue].take().unwrap())
                        .collect(),
                    tables: tables.clone(),
                    result: None,
                };
                if self.built.iter().all(|built| *built) {
                    self.base = None;
                }
                return Some(Job::Build(job));
            }
            if !self.scatter_claimed[residue] && self.chunks[residue].iter().all(Option::is_some) {
                self.scatter_claimed[residue] = true;
                return Some(Job::Scatter(Scatter {
                    residue,
                    chunks: self.chunks[residue]
                        .iter_mut()
                        .map(|chunk| chunk.take().unwrap())
                        .collect(),
                    execution: self.execution,
                    result: core::array::from_fn(|_| None),
                }));
            }
        }
        if let Some((index, scalar)) = self.blinds.next() {
            return Some(Job::Blind(Blind {
                index,
                mask: if index == RESIDUES { self.mask } else { None },
                base: self.blind_base,
                scalar,
                point: VestaProjective::IDENTITY,
            }));
        }
        for _ in 0..5 {
            let kind = self.next_kind;
            self.next_kind = (kind + 1) % 5;
            let task = match kind {
                0 => self.claim_fold(),
                1 => self.claim_expansion(),
                2 => self.claim_inverse(),
                3 => self.claim_addition(),
                _ => self.msm.claim().map(|task| {
                    #[cfg(test)]
                    if self.msm.input_of(&task) < RESIDUES && !self.interpolation_done {
                        self.timing.early_consumers[2] += 1;
                    }
                    Job::Msm(task)
                }),
            };
            if task.is_some() {
                return task;
            }
        }
        None
    }
    fn complete(&mut self, job: Self::Task) {
        match job {
            Job::Expand(job) => {
                let expansion = &mut self.expansions[job.index];
                let published = expansion
                    .run
                    .complete(0, job.task.finish())
                    .expect("matching expansion receipt");
                let Lease { values, source, .. } = published.task.resources;
                drop(source);
                self.error |=
                    published.task.error.is_some() || published.task.outcome != Outcome::Success;
                match job.bank {
                    ExpansionBank::Input => expansion.coefficients = Some(values),
                    ExpansionBank::Output(residue) => {
                        if !self.error {
                            assert_eq!(published.residue, Some(residue));
                            let residue = residue * expansion.stride;
                            self.forms[expansion.column][residue] = Some(
                                ExtendedCoset::from_residue(residue, Arc::new(recover(values)))
                                    .unwrap(),
                            );
                        }
                    }
                    ExpansionBank::Coefficients => unreachable!(),
                }
                if published.complete {
                    self.coefficients[expansion.column] = Some(SharedPoly::new(recover(
                        expansion.coefficients.take().unwrap(),
                    )));
                    self.forms_left -= 1;
                }
            }
            Job::Apply(job) => match job.job {
                Application::Instance { column, result, .. } => {
                    match result.unwrap_or(Err(Error::InternalInvariant)) {
                        Ok(coset) => {
                            self.forms[column] = core::array::from_fn(|_| Some(coset.clone()));
                            self.forms_left -= 1;
                        }
                        Err(_) => self.error = true,
                    }
                }
                Application::Tables { result, .. } => {
                    match result.unwrap_or(Err(Error::InternalInvariant)) {
                        Ok(tables) => self.tables = Some(tables),
                        Err(_) => self.error = true,
                    }
                }
            },
            Job::Build(job) => {
                self.folds[job.residue] = job.result;
            }
            Job::Fold(job) => {
                #[cfg(test)]
                {
                    self.timing.fold_work_ns += job.elapsed_ns;
                }
                self.error |= job.result.is_err();
                self.chunks[job.window.residue][job.window.k_offset / FOLD_CHUNK_ROWS] =
                    Some(job.chunks);
            }
            Job::Scatter(job) => {
                self.scatter_done[job.residue] = true;
                for (class, values) in job.result.into_iter().enumerate() {
                    if let Some(values) = values {
                        let bits = CLASS_RESIDUES[class].ilog2();
                        let fragment = if bits == 0 {
                            0
                        } else {
                            (job.residue / (RESIDUES / CLASS_RESIDUES[class])).reverse_bits()
                                >> (usize::BITS - bits)
                        };
                        assert!(self.classes[class][fragment].replace(values).is_none());
                        self.class_ready[class] += 1;
                    }
                }
                self.scattered += 1;
                #[cfg(test)]
                if self.scattered == RESIDUES {
                    self.timing
                        .mark(crate::native::stage_timing::QuotientStage::ConstraintFold);
                }
            }
            Job::Interpolate(job) => {
                let (resources, error, outcome) = if job.class == LOOKUP_LANE {
                    let published = self
                        .lookup_inverse
                        .complete(job.task.finish())
                        .expect("matching lookup inverse receipt");
                    self.inverted[LOOKUP_LANE] = published.complete;
                    (published.resources, published.error, published.outcome)
                } else {
                    let published = self
                        .interpolation
                        .complete_transform(job.class, job.task.finish())
                        .expect("matching inverse receipt");
                    if let Some(class) = published.coefficients {
                        self.inverted[class] = true;
                    }
                    (published.resources, published.error, published.outcome)
                };
                let Lease {
                    values,
                    pair,
                    source,
                } = resources;
                drop(source);
                self.classes[job.class][job.first] = Some(values);
                if let Some(index) = job.pair {
                    self.classes[job.class][index] = pair;
                }
                self.error |= error.is_some() || outcome != Outcome::Success;
                self.publish_pieces();
            }
            Job::Add(job) => {
                let published = self
                    .interpolation
                    .complete_addition(job.class, job.task.finish())
                    .expect("matching addition receipt");
                let Lease { values, source, .. } = published.resources;
                drop(source);
                self.classes[job.target][job.first] = Some(values);
                self.error |= published.error.is_some() || published.outcome != Outcome::Success;
                if job.target == EXTENDED_LANE {
                    self.additions[job.first] -= 1;
                }
                if let Some(class) = published.released {
                    self.classes[class].clear();
                }
                self.publish_pieces();
            }
            Job::CorrectLookup(job) => {
                for (slot, block) in self.classes[LOOKUP_LANE].iter_mut().zip(job.blocks) {
                    *slot = Some(block);
                }
                self.lookup_corrected = true;
            }
            Job::AddLookup(job) => {
                self.classes[EXTENDED_LANE][job.piece] = Some(job.values);
                self.additions[job.piece] -= 1;
                self.lookup_added += 1;
                if self.lookup_added == RESIDUES {
                    self.classes[LOOKUP_LANE].clear();
                }
                self.publish_pieces();
            }
            Job::Msm(job) => self.msm.complete(job),
            Job::Blind(job) => self.blind_points[job.index] = Some(job.point),
        }
        self.mark_forms();
        self.mark_interpolation();
    }
}

pub(super) struct Output {
    /// Dense expansion inputs in order; sparse instances retain no coefficients.
    pub(super) columns: Vec<SharedPoly>,
    pub(super) pieces: Vec<Buffer<Fp>>,
    pub(super) commitments: Vec<VestaProjective>,
    pub(super) mask: VestaProjective,
}

/// Runs one quotient window and optionally overlaps commitments with interpolation.
///
/// With `commit == false`, returns unblinded coefficient pieces, empty
/// commitments, and an identity mask; no MSM sources or blinding jobs are
/// admitted. The caller must combine all window contributions before committing.
#[allow(clippy::too_many_arguments)] // workspaces, window inputs, and sampled blinds stay separate
pub(super) fn execute<'t>(
    target: &'t FixedTarget,
    workspace: &mut MsmWorkspace,
    fft: &mut FftWorkspace,
    execution: Execution<'_>,
    inputs: Vec<LagrangeFormInput>,
    base: FoldPlan<'t>,
    theta: Fp,
    commit: bool,
    piece_blinds: &[Fp],
    mask: &IpaMaskRandomness,
    #[cfg(test)] timing: &mut crate::native::stage_timing::QuotientRecorder,
) -> Result<Output, Error> {
    let layout = StorageLayout::Fragments {
        length: NonZeroUsize::new(N).unwrap(),
        whole_bank: false,
    };
    // The provider owns disjoint N-element fragments and no snapshot or panel bank.
    let options = ExecutionOptions::default()
        .with_task_budget(execution.budget)
        .with_memory_limit(0);
    // All four plans below combine prepared domains with this fixed fragment
    // layout. Construction errors describe internal plan incompatibilities;
    // no witness values or transcript challenges enter plan construction.
    let expansion_plan = ExpansionPlan::new(
        target.fft().expansion(RESIDUES).unwrap(),
        ExpansionStorage::DisposableInput {
            scale: InverseScale::Normalized,
        },
        ExpansionOrder::Residues,
        InputSupport::Full,
        ElementOrder::Natural,
        layout,
        options,
    )
    .map_err(|_| Error::InternalInvariant)?;
    let lookup_expansion_plan = ExpansionPlan::new(
        target.fft().expansion(4).unwrap(),
        ExpansionStorage::DisposableInput {
            scale: InverseScale::Normalized,
        },
        ExpansionOrder::Residues,
        InputSupport::Full,
        ElementOrder::Natural,
        layout,
        options,
    )
    .map_err(|_| Error::InternalInvariant)?;
    let transforms = core::array::from_fn(|class| {
        (
            target.fft().class_plan(3 - class),
            ElementOrder::BitReversed,
        )
    });
    let interpolation_plan = InterpolationPlan::new(transforms, true, layout, options)
        .map_err(|_| Error::InternalInvariant)?;
    let lookup_inverse_plan = FftPlan::new(
        target.fft().class_plan(2),
        TransformRequest {
            input_order: ElementOrder::BitReversed,
            ..TransformRequest::new(Direction::Inverse)
        },
        layout,
        options,
    )
    .map_err(|_| Error::InternalInvariant)?;
    assert_eq!(expansion_plan.snapshot_fields(), 0);
    assert_eq!(lookup_expansion_plan.snapshot_fields(), 0);
    assert_eq!(lookup_inverse_plan.retained_fields(), 0);
    for class in EXTENDED_LANE..LOOKUP_LANE {
        assert_eq!(interpolation_plan.snapshot_fields(class), Some(0));
    }
    let column_count = inputs.len();
    let dense_count = inputs
        .iter()
        .filter(|input| {
            matches!(
                input,
                LagrangeFormInput::Dense(_) | LagrangeFormInput::Dense4N(_)
            )
        })
        .count();
    let live_residues: usize = inputs
        .iter()
        .map(|input| match input {
            LagrangeFormInput::Dense(_) => RESIDUE_LEAD,
            LagrangeFormInput::Dense4N(_) => RESIDUE_LEAD.div_ceil(2),
            LagrangeFormInput::SparseInstance { .. } => 0,
        })
        .sum();
    fft.provision(dense_count);
    // Two live residues per 8N column and one per 4N column, all four
    // degree-class banks, and the separate 4N lookup bank. An adjacent
    // pair of residues needs at most six classes of fold chunks.
    // Provision counts only idle buffers: live opening polynomials cannot
    // satisfy this reserve. Returned banks can serve later polynomial stages.
    fft.buffers.provision(N, live_residues + 19, <Fp>::ZERO);
    fft.buffers
        .provision(FOLD_CHUNK_ROWS, 6 * WINDOWS, <Fp>::ZERO);
    let application_execution = execution;
    let execution = execution.with_buffers(&fft.buffers);
    let mut metadata = fft.expansion_ids.iter_mut().zip(&mut fft.expansion_storage);
    let mut applications = vec![Application::Tables {
        target,
        theta,
        result: None,
    }];
    let mut expansions = Vec::with_capacity(dense_count);
    let mut forms: Vec<[Option<ExtendedCoset>; RESIDUES]> = (0..column_count)
        .map(|_| core::array::from_fn(|_| None))
        .collect();
    for (column, input) in inputs.into_iter().enumerate() {
        let stride = if matches!(input, LagrangeFormInput::Dense4N(_)) {
            2
        } else {
            1
        };
        match input {
            LagrangeFormInput::Dense(values) | LagrangeFormInput::Dense4N(values) => {
                let (identity, storage) = metadata.next().unwrap();
                let plan = if stride == 2 {
                    // Odd residues never read the permuted columns.
                    for residue in (1..RESIDUES).step_by(2) {
                        forms[column][residue] = Some(ExtendedCoset::pending());
                    }
                    lookup_expansion_plan
                } else {
                    expansion_plan
                };
                expansions.push(Expansion {
                    column,
                    stride,
                    run: ExpansionRun::new(plan, false, identity, storage).unwrap(),
                    coefficients: Some(fields(values)),
                });
            }
            input => applications.push(Application::Instance {
                column,
                input,
                target,
                result: None,
            }),
        }
    }
    let interpolation = InterpolationRun::new(
        interpolation_plan,
        &mut fft.class_ids,
        &mut fft.class_storage,
    );
    let lookup_inverse = FftRun::new(
        lookup_inverse_plan,
        false,
        &mut fft.lookup_id,
        &mut fft.lookup_storage,
    );
    let fixed_mask = target
        .parameters()
        .prepared_mask_generators()
        .map(|bases| (bases, mask.alphas));
    let bases = target.parameters().quotient_coefficient_bases();
    let msm_inputs: [_; RESIDUES + 1] = core::array::from_fn(|index| {
        if index < RESIDUES {
            ProducedInput::dense(bases)
        } else {
            ProducedInput::indexed(
                target.parameters().coefficient_bases(),
                if fixed_mask.is_some() { 0 } else { K as usize },
            )
        }
    });
    // Produced inputs use the prepared coefficient banks and fixed piece/mask
    // dimensions; an MSM planning failure is an internal layout mismatch.
    let mut batch = workspace
        .prepare_produced(if commit { &msm_inputs } else { &[] }, execution.budget, N)
        .map_err(|_| Error::InternalInvariant)?;
    let mut msm = batch.coordinator();
    if commit && fixed_mask.is_none() {
        msm.sources[RESIDUES].publish(
            0..K as usize,
            Arc::new(Raw {
                scalars: application_execution.copy(&mask.alphas),
                indices: SourceIndices::Static(&IPA_MASK_GENERATOR_INDICES),
            }),
        );
    }
    let mut quotient = Quotient {
        mask: fixed_mask,
        execution,
        application_execution,
        expansions,
        cursor: 0,
        applications: applications.into_iter(),
        base: Some(Arc::new(base)),
        tables: None,
        forms,
        coefficients: (0..column_count).map(|_| None).collect(),
        built: [false; RESIDUES],
        folds: core::array::from_fn(|_| None),
        next_fold: [0; RESIDUES],
        chunks: core::array::from_fn(|_| (0..WINDOWS).map(|_| None).collect()),
        scatter_claimed: [false; RESIDUES],
        scatter_done: [false; RESIDUES],
        scattered: 0,
        interpolation,
        lookup_inverse,
        classes: core::array::from_fn(|class| (0..CLASS_RESIDUES[class]).map(|_| None).collect()),
        class_ready: [0; 5],
        inverted: [false; 5],
        correction_claimed: false,
        lookup_corrected: false,
        lookup_additions: [false; RESIDUES],
        lookup_added: 0,
        interpolation_done: false,
        additions: core::array::from_fn(|piece| {
            1 + (CLASS_4N_LANE..LOOKUP_LANE)
                .filter(|class| piece < RESIDUES >> class)
                .count()
        }),
        pieces: [false; RESIDUES],
        commit,
        msm,
        blinds: core::array::from_fn(|index| {
            (
                index,
                if index < RESIDUES {
                    piece_blinds[index]
                } else {
                    mask.blind
                },
            )
        })
        .into_iter()
        .take(if commit { RESIDUES + 1 } else { 0 }),
        blind_base: target.parameters().prepared_blind_generator(),
        blind_points: [None; RESIDUES + 1],
        next_kind: 1,
        error: false,
        forms_left: column_count,
        forms_done: false,
        #[cfg(test)]
        timing,
    };
    run::drive(&mut quotient, execution.budget, &execution);
    if quotient.error || quotient.msm.failed() || !quotient.interpolation_done {
        return Err(Error::InternalInvariant);
    }
    let points = quotient.msm.results().ok_or(Error::InternalInvariant)?;
    if points.len() != if commit { RESIDUES + 1 } else { 0 } {
        return Err(Error::InternalInvariant);
    }
    let mut commitments = points
        .zip(quotient.blind_points)
        .map(|(point, blind)| blind.map(|blind| point.add(&blind)))
        .collect::<Option<Vec<_>>>()
        .ok_or(Error::InternalInvariant)?;
    let mask = commitments.pop().unwrap_or(VestaProjective::IDENTITY);
    for source in &mut quotient.msm.sources {
        source.clear();
    }
    let pieces = core::mem::take(&mut quotient.classes[EXTENDED_LANE])
        .into_iter()
        .map(|piece| piece.map(recover))
        .collect::<Option<Vec<_>>>()
        .ok_or(Error::InternalInvariant)?;
    let columns = quotient
        .expansions
        .iter()
        .map(|expansion| quotient.coefficients[expansion.column].take())
        .collect::<Option<Vec<_>>>()
        .ok_or(Error::InternalInvariant)?;
    Ok(Output {
        columns,
        pieces,
        commitments,
        mask,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::polynomial::{coset_fft, coset_ifft};
    use udon::fft::Domain;

    /// Independent evaluation-domain division, including numerators that
    /// do not vanish on the base subgroup. The production lift must keep
    /// their remainder's contribution to all eight coefficient blocks.
    #[test]
    fn lookup_remainder_lift_matches_dense_division() {
        fn divided_interpolant(numerator: &[Fp], blocks: usize) -> Vec<Fp> {
            let mut values = numerator.to_vec();
            values.resize(blocks * N, <Fp>::ZERO);
            assert!(coset_fft(&mut values));
            let domain = Domain::<Fp>::for_size(values.len()).unwrap();
            let step = domain.root().pow_u64(N as u64);
            let mut xn = <Fp>::ZETA.pow_u64(N as u64);
            let scales: Vec<_> = (0..blocks)
                .map(|_| {
                    let inverse = xn.sub(&<Fp>::ONE).invert().unwrap();
                    xn = xn.mul(&step);
                    inverse
                })
                .collect();
            for (row, value) in values.iter_mut().enumerate() {
                *value = value.mul(&scales[row % blocks]);
            }
            assert!(coset_ifft(&mut values));
            values
        }

        let dense: Vec<_> = (0..4 * N)
            .map(|i| <Fp>::from_u64((i * i + 17 * i + 23) as u64))
            .collect();
        let mut monomial = vec![<Fp>::ZERO; 4 * N];
        monomial[4 * N - 1] = <Fp>::ONE;
        let mut divisible = vec![<Fp>::ZERO; 4 * N];
        for (i, value) in dense[..3 * N].iter().enumerate() {
            divisible[i] = divisible[i].sub(value);
            divisible[i + N] = divisible[i + N].add(value);
        }
        for (numerator, has_remainder) in [
            (vec![<Fp>::ZERO; 4 * N], false),
            (vec![<Fp>::ONE], true),
            (monomial, true),
            (dense, true),
            (divisible, false),
        ] {
            let expected = divided_interpolant(&numerator, 8);
            let mut small = divided_interpolant(&numerator, 4);
            assert_eq!(small[3 * N..].iter().any(|x| !x.is_zero()), has_remainder);
            let chunks: Vec<_> = small.chunks_exact_mut(N).collect();
            correct_lookup(chunks.try_into().unwrap());
            let actual: Vec<_> = (0..8)
                .flat_map(|piece| small[piece.min(3) * N..(piece.min(3) + 1) * N].iter())
                .map(|value| value.to_bytes())
                .collect();
            assert_eq!(
                actual,
                expected
                    .iter()
                    .map(|value| value.to_bytes())
                    .collect::<Vec<_>>()
            );
        }
    }
}
