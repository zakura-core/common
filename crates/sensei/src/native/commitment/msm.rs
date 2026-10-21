//! Workspace banks and task leases for the shared MSM scheduler.
//!
//! [`MsmWorkspace`] owns the retained banks, frontier metadata, and scratch
//! [`Work`] bundles. [`Batch`] borrows these and copies input descriptors, not
//! their backing scalars or bases. [`Batch::coordinator`] reborrows the banks
//! and metadata; its runs retain the input borrows. Produced inputs additionally
//! use coordinator-owned [`SourceRow`] registrations for published [`Raw`] data.
//!
//! Each claim detaches a complete [`SourcedLease`] in an [`MsmTask`]:
//!
//! | Resource | Claim and task access | Return or release |
//! | --- | --- | --- |
//! | Scratch [`Work`] | Move one exclusive borrow from the coordinator's `free` stack into the lease. | `Coordinator::complete` returns the borrow to `free` after releasing its readers and copying any successful partial output. |
//! | Preparation [`Records`] | Take the slot's `Arc`, leaving `None`, for an exclusive preparation writer. Later window tasks clone published records into their scratch bundle's [`ReadBank`]. | Completion restores the writer's `Arc` to its slot; each reader completion clears its `ReadBank`. |
//! | Streaming buckets | Take a window's `Vec` from its slot, leaving `None`; successive chunks and the final collapse reuse that window's buckets. | Completion restores the same `Vec` before another task can claim it. |
//! | Produced source fragments | [`SourceRow::acquire`] clones the registered `Arc<Raw>` fragments needed by the request into [`SourceReads`]. | Completion drops these task readers. Registrations remain until explicit clearing, coordinator restart, or row drop. |
//!
//! [`Task::finish`] moves the lease into a noncloneable completion receipt.
//! `Coordinator::complete` routes it to the originating [`MsmRun::complete`],
//! which validates the frontier identity and returns the lease even for an
//! unsuccessful task. Only successful, error-free partial outputs are copied
//! into the retained bank. A reduction receives a scratch copy of those partials.
//! The scheduler serializes claim and completion callbacks: although publishing
//! a receipt may ready a successor, its lease is restored before the next claim.
//!
//! Preparation records start with one owner. Returning a writer's record makes
//! it available to readers, but exclusive reuse also requires every window
//! reader to complete and clear its `ReadBank`. `MsmRun` advances past a phase
//! only after all its receipts arrive; this fences the next preparation chunk.
//! Draining the previous batch establishes the same condition when
//! [`MsmWorkspace::prepare`] grows or reuses the banks. These completion paths
//! establish the `Arc::get_mut` and returned-slot assumptions below.
//! [`Batch::execute_with`] checks that every scratch borrow returned after
//! driving the scheduler; direct coordinator users must also drain every claim.
//!
//! Source ownership is separate: releasing task readers leaves the row's
//! registrations and any producer-held Arcs alive. Clearing registrations
//! after readers drain permits a producer to regain exclusive access if it
//! holds the only remaining Arc. Dropping the last Arc destroys [`Raw`] and
//! returns its pool-backed [`Buffer`] leases; static index slices are borrowed.
//!
//! These are explicit completion obligations, not a drop-based return protocol.
//! [`run::drive`] retains a task across caught kernel unwinding, completes its
//! failed receipt, drains dispatched tasks, and resumes the panic. Returning
//! those leases does not publish a successful result. Normal arithmetic errors
//! likewise return leases while stopping new MSM claims. Dropping an unfinished
//! task, or a panic during claim or completion itself, does not guarantee that
//! all slots and reader banks are restored for workspace reuse.

use super::super::worker::run::{self, Coordinator as Scheduler, Work as Job};
use crate::native::buffer::Buffer;
use alloc::{sync::Arc, vec::Vec};
use core::{num::NonZeroUsize, ops::Range};
use udon::{
    curve::{AffinePoint, CurveError, PastaCurve, ProjectivePoint},
    exec::{
        ExecutionOptions, Executor, TaskBudget,
        execution::{Identity, Outcome, ReadView, Task, TaskStorage},
    },
    field::PastaField,
    msm::{
        Input, ScalarStorage, Scratch,
        execution::{
            Buffers, MsmKernel, MsmPlan, MsmRun, ProducedInput, Request, Resources, SourceBuffers,
        },
    },
};

const FRONTIER: usize = 32;

#[cfg(all(test, feature = "prover"))]
mod tests;

struct Values<T>(Vec<T>);
impl<T> ReadView<T> for Values<T> {
    fn len(&self) -> usize {
        self.0.len()
    }
    fn get(&self, index: usize) -> Option<&T> {
        self.0.get(index)
    }
    fn contiguous(&self, range: Range<usize>) -> Option<&[T]> {
        self.0.get(range)
    }
}

struct Records<C: PastaCurve> {
    scalars: Values<ScalarStorage<C>>,
    digits: Values<u8>,
}
struct Retained<C: PastaCurve> {
    records: Vec<Option<Arc<Records<C>>>>,
    scalar_grain: usize,
    digit_grain: usize,
    partials: Vec<ProjectivePoint<C>>,
    buckets: Vec<Option<Vec<ProjectivePoint<C>>>>,
    bucket_grain: usize,
}
impl<C: PastaCurve> Retained<C> {
    fn new() -> Self {
        Self {
            records: Vec::new(),
            scalar_grain: 1,
            digit_grain: 0,
            partials: Vec::new(),
            buckets: Vec::new(),
            bucket_grain: 0,
        }
    }
}

struct Metadata {
    identity: Identity,
    frontier: [TaskStorage; FRONTIER],
}
impl Metadata {
    fn new() -> Self {
        Self {
            identity: Identity::new(),
            frontier: [TaskStorage::EMPTY; FRONTIER],
        }
    }
}

struct Work<C: PastaCurve> {
    reads: ReadBank<C>,
    affine: Vec<AffinePoint<C>>,
    projective: Vec<ProjectivePoint<C>>,
    field: Vec<PastaField<C::Base>>,
    indices: Vec<usize>,
    partials: Values<ProjectivePoint<C>>,
    output: [ProjectivePoint<C>; 1],
}
impl<C: PastaCurve> Work<C> {
    fn new() -> Self {
        Self {
            reads: ReadBank {
                records: Vec::new(),
                scalar_grain: 1,
                digit_grain: 1,
                scalars: 0,
                digits: 0,
            },
            affine: Vec::new(),
            projective: Vec::new(),
            field: Vec::new(),
            indices: Vec::new(),
            partials: Values(Vec::new()),
            output: [ProjectivePoint::IDENTITY],
        }
    }
    fn grow(&mut self, sizes: [usize; 5], fragments: usize) {
        if self.reads.records.capacity() < fragments {
            self.reads.records.reserve(fragments);
        }
        let [
            affine_len,
            projective_len,
            field_len,
            index_len,
            partial_result_len,
        ] = sizes;
        grow(&mut self.affine, affine_len, AffinePoint::GENERATOR);
        grow(
            &mut self.projective,
            projective_len,
            ProjectivePoint::IDENTITY,
        );
        grow(&mut self.field, field_len, PastaField::ZERO);
        grow(&mut self.indices, index_len, 0);
        grow(
            &mut self.partials.0,
            partial_result_len,
            ProjectivePoint::IDENTITY,
        );
    }
}
fn grow<T: Clone>(values: &mut Vec<T>, len: usize, value: T) {
    values.resize(values.len().max(len), value);
}

pub(crate) struct MsmWorkspace<C: PastaCurve = udon::curve::Vesta> {
    retained: Vec<Retained<C>>,
    metadata: Vec<Metadata>,
    plans: Vec<MsmPlan<C>>,
    groups: Vec<Range<usize>>,
    work: Vec<Work<C>>,
}
impl<C: PastaCurve> MsmWorkspace<C> {
    pub(crate) fn new() -> Self {
        Self {
            retained: Vec::new(),
            metadata: Vec::new(),
            plans: Vec::new(),
            groups: Vec::new(),
            work: Vec::new(),
        }
    }

    /// Provisions all retained banks and complete scratch bundles before dispatch.
    pub(crate) fn prepare<'a, 'i>(
        &'a mut self,
        inputs: &[Input<'i, C>],
        budget: TaskBudget,
    ) -> Result<Batch<'a, 'i, C>, CurveError> {
        self.prepare_bindings(inputs.iter().copied().map(Binding::Borrowed), budget, None)
    }

    #[cfg(feature = "prover")]
    pub(crate) fn prepare_produced<'a, 'i>(
        &'a mut self,
        inputs: &[ProducedInput<'i, C>],
        budget: TaskBudget,
        source_fragment: usize,
    ) -> Result<Batch<'a, 'i, C>, CurveError> {
        self.prepare_bindings(
            inputs.iter().copied().map(Binding::Produced),
            budget,
            NonZeroUsize::new(source_fragment.max(1)),
        )
    }

    fn prepare_bindings<'a, 'i>(
        &'a mut self,
        inputs: impl ExactSizeIterator<Item = Binding<'i, C>>,
        budget: TaskBudget,
        source_fragment: Option<NonZeroUsize>,
    ) -> Result<Batch<'a, 'i, C>, CurveError> {
        self.plans.clear();
        let options = ExecutionOptions::default()
            .with_task_budget(TaskBudget::new(budget.get().min(FRONTIER)).unwrap());
        let mut bindings = Vec::new();
        self.groups.clear();
        self.groups.reserve(inputs.len());
        for (source, input) in inputs.enumerate() {
            let plan = match input {
                Binding::Borrowed(input) => MsmPlan::for_input(&input, options),
                Binding::Produced(input) => MsmPlan::for_produced(
                    input,
                    source_fragment.expect("producer fragment length"),
                    options,
                ),
            }?;
            let start = bindings.len();
            for partition in 0..input.len().div_ceil(plan.grain().max(1)).max(1) {
                let first = partition * plan.grain();
                bindings.push((
                    input,
                    first..(first + plan.grain()).min(input.len()),
                    source,
                ));
                self.plans.push(plan);
            }
            self.groups.push(start..bindings.len());
        }
        self.retained
            .resize_with(self.retained.len().max(bindings.len()), Retained::new);
        self.metadata
            .resize_with(self.metadata.len().max(bindings.len()), Metadata::new);
        let mut sizes = [0; 5];
        let mut fragments = 0;
        let mut parallelism = 0usize;
        for (plan, retained) in self.plans.iter().zip(&mut self.retained) {
            let r = plan.retained();

            grow(
                &mut retained.partials,
                plan.output_slots(),
                ProjectivePoint::IDENTITY,
            );
            let bucket_fields = r.projective() - plan.output_slots();
            retained.bucket_grain = bucket_fields / plan.output_slots().max(1);
            let bucket_slots = if bucket_fields == 0 {
                0
            } else {
                plan.output_slots()
            };
            retained
                .buckets
                .resize_with(
                    retained.buckets.len().max(bucket_slots),
                    || Some(Vec::new()),
                );
            for buckets in &mut retained.buckets[..bucket_slots] {
                // New slots are populated; reused slots were restored by
                // Coordinator::complete for every preceding bucket task.
                grow(
                    buckets.as_mut().expect("returned bucket lease"),
                    retained.bucket_grain,
                    ProjectivePoint::IDENTITY,
                );
            }

            let scalar_grain = plan.preparation_terms().max(1);
            let digit_grain = r.digits() / plan.grain().max(1) * scalar_grain;
            let count = plan.grain().div_ceil(scalar_grain);
            fragments = fragments.max(count);
            retained.scalar_grain = scalar_grain;
            retained.digit_grain = digit_grain;
            retained
                .records
                .resize_with(retained.records.len().max(count), || {
                    Some(Arc::new(Records {
                        scalars: Values(Vec::new()),
                        digits: Values(Vec::new()),
                    }))
                });
            for record in &mut retained.records[..count] {
                // Completion restored preparation slots and cleared all old
                // window ReadBanks; a fresh record also has only this owner.
                let record = Arc::get_mut(record.as_mut().expect("returned preparation lease"))
                    .expect("previous readers drained");
                grow(
                    &mut record.scalars.0,
                    r.scalars().min(scalar_grain),
                    ScalarStorage::ZERO,
                );
                grow(&mut record.digits.0, digit_grain, 0);
            }
            parallelism = parallelism.saturating_add(plan.output_slots().max(count));
            let t = plan.temporary();
            let affine_len = t.affine();
            let projective_len = t.projective();
            let field_len = t.field();
            let index_len = t.indices();
            let partial_result_len = plan.output_slots();
            for (max, n) in sizes.iter_mut().zip([
                affine_len,
                projective_len,
                field_len,
                index_len,
                partial_result_len,
            ]) {
                *max = (*max).max(n);
            }
        }
        let workers = budget.get().min(FRONTIER).min(parallelism.max(1));
        self.work
            .resize_with(self.work.len().max(workers), Work::new);
        for work in &mut self.work[..workers] {
            work.grow(sizes, fragments);
        }
        Ok(Batch {
            bindings,
            groups: &self.groups,
            plans: &self.plans,
            retained: &mut self.retained[..self.plans.len()],
            metadata: &mut self.metadata[..self.plans.len()],
            work: &mut self.work[..workers],
        })
    }

    #[cfg(all(test, feature = "prover"))]
    pub(crate) fn capacities(&self) -> Vec<usize> {
        // Like prepare, inspect only after every claimed lease has passed
        // through Coordinator::complete and repopulated its retained slot.
        let mut result = alloc::vec![
            self.retained.capacity(),
            self.metadata.capacity(),
            self.plans.capacity(),
            self.groups.capacity(),
            self.work.capacity(),
        ];
        for retained in &self.retained {
            result.extend([
                retained.records.capacity(),
                retained.partials.capacity(),
                retained.buckets.capacity(),
            ]);
            for buckets in &retained.buckets {
                result.push(buckets.as_ref().expect("returned lease").capacity());
            }
            for records in &retained.records {
                let records = records.as_ref().expect("returned lease");
                result.extend([records.scalars.0.capacity(), records.digits.0.capacity()]);
            }
        }
        for work in &self.work {
            result.extend([
                work.reads.records.capacity(),
                work.affine.capacity(),
                work.projective.capacity(),
                work.field.capacity(),
                work.indices.capacity(),
                work.partials.0.capacity(),
            ]);
        }
        result
    }

    #[cfg(all(test, feature = "prover", feature = "verifier"))]
    pub(crate) fn retained_bytes(&self) -> usize {
        // The returned-slot requirement is the same as for capacities.
        let mut bytes = self.retained.capacity() * size_of::<Retained<C>>()
            + self.metadata.capacity() * size_of::<Metadata>()
            + self.plans.capacity() * size_of::<MsmPlan<C>>()
            + self.groups.capacity() * size_of::<Range<usize>>()
            + self.work.capacity() * size_of::<Work<C>>();
        for retained in &self.retained {
            bytes += retained.records.capacity() * size_of::<Option<Arc<Records<C>>>>()
                + retained.partials.capacity() * size_of::<ProjectivePoint<C>>()
                + retained.buckets.capacity() * size_of::<Option<Vec<ProjectivePoint<C>>>>();
            for buckets in &retained.buckets {
                bytes += buckets.as_ref().expect("returned lease").capacity()
                    * size_of::<ProjectivePoint<C>>();
            }
            for records in &retained.records {
                let records = records.as_ref().expect("returned lease");
                bytes += size_of::<Records<C>>()
                    + 2 * size_of::<usize>()
                    + records.scalars.0.capacity() * size_of::<ScalarStorage<C>>()
                    + records.digits.0.capacity();
            }
        }
        for work in &self.work {
            bytes += work.reads.records.capacity() * size_of::<Arc<Records<C>>>()
                + work.affine.capacity() * size_of::<AffinePoint<C>>()
                + work.projective.capacity() * size_of::<ProjectivePoint<C>>()
                + work.field.capacity() * size_of::<PastaField<C::Base>>()
                + work.indices.capacity() * size_of::<usize>()
                + work.partials.0.capacity() * size_of::<ProjectivePoint<C>>();
        }
        bytes
    }
}

struct ReadBank<C: PastaCurve> {
    records: Vec<Arc<Records<C>>>,
    scalar_grain: usize,
    digit_grain: usize,
    scalars: usize,
    digits: usize,
}
macro_rules! read_bank {
    ($type:ty, $grain:ident, $len:ident) => {
        impl<C: PastaCurve> ReadView<$type> for ReadBank<C> {
            fn len(&self) -> usize {
                self.$len
            }
            fn get(&self, index: usize) -> Option<&$type> {
                if index >= self.$len {
                    return None;
                }
                self.records
                    .get(index / self.$grain)?
                    .$len
                    .0
                    .get(index % self.$grain)
            }
            fn contiguous(&self, range: Range<usize>) -> Option<&[$type]> {
                let prefix = self.contiguous_prefix(range.clone())?;
                (prefix.len() == range.len()).then_some(prefix)
            }
            fn contiguous_prefix(&self, range: Range<usize>) -> Option<&[$type]> {
                if range.end > self.$len || range.start > range.end {
                    return None;
                }
                if range.is_empty() {
                    return Some(&[]);
                }
                self.records.get(range.start / self.$grain)?.$len.0.get(
                    range.start % self.$grain
                        ..range.end.min((range.start / self.$grain + 1) * self.$grain)
                            - range.start / self.$grain * self.$grain,
                )
            }
        }
    };
}
read_bank!(ScalarStorage<C>, scalar_grain, scalars);
read_bank!(u8, digit_grain, digits);

struct Lease<'a, C: PastaCurve> {
    work: &'a mut Work<C>,
    prepare: Option<Arc<Records<C>>>,
    buckets: Option<Vec<ProjectivePoint<C>>>,
}
impl<C: PastaCurve> Resources<C> for Lease<'_, C> {
    fn buffers(&mut self) -> Buffers<'_, C> {
        let (scalars, digits) = match self.prepare.as_mut() {
            Some(records) => {
                // Claim took this writer's slot before readers are admitted;
                // prior window completions cleared their ReadBanks before
                // MsmRun readied this preparation phase (see module lifecycle).
                let records = Arc::get_mut(records).expect("exclusive preparation lease");
                (
                    records.scalars.0.as_mut_slice(),
                    records.digits.0.as_mut_slice(),
                )
            }
            None => (&mut [][..], &mut [][..]),
        };
        Buffers {
            records: &self.work.reads,
            digits: &self.work.reads,
            scratch: Scratch::new(
                scalars,
                digits,
                &mut self.work.affine,
                &mut self.work.projective,
                &mut self.work.field,
                &mut self.work.indices,
            ),
            buckets: self.buckets.as_deref_mut().unwrap_or(&mut []),
            output: &mut self.work.output,
            partials: &self.work.partials,
        }
    }
}

#[derive(Clone, Copy)]
enum Binding<'i, C: PastaCurve> {
    Borrowed(Input<'i, C>),
    #[cfg_attr(
        not(feature = "prover"),
        expect(
            dead_code,
            reason = "Shared MSM bindings; only prover pipelines publish source rows."
        )
    )]
    Produced(ProducedInput<'i, C>),
}
impl<C: PastaCurve> Binding<'_, C> {
    fn len(&self) -> usize {
        match self {
            Self::Borrowed(i) => i.len(),
            Self::Produced(i) => i.len(),
        }
    }
}

/// A prepared borrow of workspace storage; lease ownership follows the module
/// lifecycle when a coordinator is created from it.
pub(crate) struct Batch<'a, 'i, C: PastaCurve> {
    bindings: Vec<(Binding<'i, C>, Range<usize>, usize)>,
    groups: &'a [Range<usize>],
    plans: &'a [MsmPlan<C>],
    retained: &'a mut [Retained<C>],
    metadata: &'a mut [Metadata],
    work: &'a mut [Work<C>],
}

pub(crate) struct Coordinator<'a, 'i, 'b, C: PastaCurve> {
    runs: Vec<MsmRun<'a, 'i, C>>,
    bindings: &'b [(Binding<'i, C>, Range<usize>, usize)],
    #[cfg_attr(
        not(feature = "prover"),
        expect(
            dead_code,
            reason = "Shared MSM bindings; only prover pipelines publish source rows."
        )
    )]
    plans: &'b [MsmPlan<C>],
    pub(crate) sources: Vec<SourceRow<C>>,
    retained: &'b mut [Retained<C>],
    free: [Option<&'b mut Work<C>>; FRONTIER],
    free_len: usize,
    cursor: usize,
    error: Option<CurveError>,
}
pub(crate) struct MsmTask<'a, 'i, 'b, C: PastaCurve> {
    index: usize,
    request: Request<'a>,
    task: Task<'a, MsmKernel<'i, C>, SourcedLease<'b, C>>,
}
#[cfg(all(test, feature = "prover"))]
impl<C: PastaCurve> MsmTask<'_, '_, '_, C> {
    pub(crate) fn writes_partial(&self) -> bool {
        self.request.output_slot.is_some()
    }
}
impl<C: PastaCurve> Job for MsmTask<'_, '_, '_, C> {
    fn execute(&mut self) {
        self.task.execute().expect("fresh task");
    }
}
impl<'a, 'i, 'b, C: PastaCurve> Scheduler for Coordinator<'a, 'i, 'b, C> {
    type Task = MsmTask<'a, 'i, 'b, C>;
    fn claim(&mut self) -> Option<Self::Task> {
        if self.error.is_some() || self.free_len == 0 {
            return None;
        }
        for offset in 0..self.runs.len() {
            let index = (self.cursor + offset) % self.runs.len();
            let mut ready = [None];
            if self.runs[index].ready(&mut ready) == 0 {
                continue;
            }
            let mut request = ready[0].unwrap();
            let source = if matches!(self.bindings[index].0, Binding::Produced(_)) {
                let row = &self.sources[self.bindings[index].2];
                loop {
                    if let Some(source) = row.acquire(request) {
                        break source;
                    }
                    if self.runs[index].ready_from(request.key.index() + 1, &mut ready) == 0 {
                        break SourceReads::unavailable();
                    }
                    request = ready[0].unwrap();
                }
            } else {
                SourceReads::empty()
            };
            if source.unavailable {
                continue;
            }
            self.free_len -= 1;
            let work = self.free[self.free_len].take().unwrap();
            let retained = &mut self.retained[index];
            let prepare = if request.scratch.scalars() != 0 || request.scratch.digits() != 0 {
                Some(
                    retained.records[request.scalar_start / retained.scalar_grain]
                        .take()
                        .expect("exclusive preparation fragment"),
                )
            } else {
                None
            };
            let buckets = if request.buckets == 0 {
                None
            } else {
                Some(
                    retained.buckets[request.bucket_start / retained.bucket_grain]
                        .take()
                        .expect("exclusive bucket fragment"),
                )
            };
            if request.read_scalars != 0 || request.read_digits != 0 {
                work.reads.records.extend(
                    retained
                        .records
                        .iter()
                        .take(request.terms.div_ceil(retained.scalar_grain))
                        .map(|r| Arc::clone(r.as_ref().expect("published preparation"))),
                );
            }
            if request.read_partials != 0 {
                work.partials.0[..request.read_partials]
                    .copy_from_slice(&retained.partials[..request.read_partials]);
            }
            work.reads.scalar_grain = retained.scalar_grain;
            work.reads.digit_grain = retained.digit_grain;
            work.reads.scalars = request.read_scalars;
            work.reads.digits = request.read_digits;
            let task = self.runs[index]
                .try_claim(request, || {
                    Some(SourcedLease {
                        lease: Lease {
                            work,
                            prepare,
                            buckets,
                        },
                        source,
                    })
                })
                .expect("current request")
                .expect("complete lease");
            self.cursor = (index + 1) % self.runs.len();
            return Some(MsmTask {
                index,
                request,
                task,
            });
        }
        None
    }
    fn complete(&mut self, job: Self::Task) {
        // The task and its noncloneable receipt carry the original run's key;
        // route by the index saved at claim, including for failed execution.
        let published = self.runs[job.index]
            .complete(job.task.finish())
            .expect("matching receipt");
        let SourcedLease {
            lease:
                Lease {
                    work,
                    prepare,
                    buckets,
                },
            source,
        } = published.resources;
        // Release only this task's readers. SourceRow keeps registrations;
        // the last window completion restores preparation-record exclusivity.
        drop(source);
        work.reads.records.clear();
        let retained = &mut self.retained[job.index];
        if let Some(records) = prepare {
            let slot = &mut retained.records[job.request.scalar_start / retained.scalar_grain];
            assert!(slot.replace(records).is_none());
        }
        if let Some(buckets) = buckets {
            let slot = &mut retained.buckets[job.request.bucket_start / retained.bucket_grain];
            assert!(slot.replace(buckets).is_none());
        }
        if published.outcome == Outcome::Success
            && published.error.is_none()
            && let Some(slot) = job.request.output_slot
        {
            retained.partials[slot] = work.output[0];
        }
        self.error = self.error.or(published.error);
        assert!(self.free[self.free_len].replace(work).is_none());
        self.free_len += 1;
    }
}

impl<C: PastaCurve> Batch<'_, '_, C> {
    pub(crate) fn execute<E: Executor>(
        &mut self,
        output: &mut [ProjectivePoint<C>],
        executor: &E,
    ) -> Result<(), CurveError> {
        self.execute_with(
            output,
            executor,
            TaskBudget::new(self.work.len()).unwrap(),
            &mut (),
        )
    }

    pub(crate) fn execute_with<E: Executor, S: Scheduler>(
        &mut self,
        output: &mut [ProjectivePoint<C>],
        executor: &E,
        budget: TaskBudget,
        sides: &mut S,
    ) -> Result<(), CurveError> {
        assert_eq!(output.len(), self.groups.len(), "commitment output length");
        let workers = self.work.len();
        let groups = self.groups;
        let mut coordinator = self.coordinator();
        run::drive(
            &mut run::Pair::new(&mut coordinator, sides),
            budget,
            executor,
        );
        assert_eq!(coordinator.free_len, workers, "all receipts drained");
        if let Some(error) = coordinator.error {
            return Err(error);
        }
        for (output, group) in output.iter_mut().zip(groups) {
            *output = coordinator.runs[group.clone()]
                .iter()
                .fold(ProjectivePoint::IDENTITY, |sum, run| {
                    sum.add(&run.result().expect("all runs completed"))
                });
        }
        Ok(())
    }
}

impl<'a, 'i, C: PastaCurve> Batch<'a, 'i, C> {
    pub(crate) fn coordinator(&mut self) -> Coordinator<'_, 'i, '_, C> {
        let runs = self
            .bindings
            .iter()
            .zip(self.plans)
            .zip(self.metadata.iter_mut())
            .map(|(((input, range, _), plan), metadata)| match input {
                Binding::Borrowed(input) => MsmRun::new_partition(
                    *plan,
                    *input,
                    range.clone(),
                    &mut metadata.identity,
                    &mut metadata.frontier,
                ),
                Binding::Produced(input) => MsmRun::new_produced_partition(
                    *plan,
                    *input,
                    range.clone(),
                    &mut metadata.identity,
                    &mut metadata.frontier,
                ),
            })
            .collect();
        Coordinator {
            runs,
            bindings: &self.bindings,
            plans: self.plans,
            sources: if matches!(self.bindings.first(), Some((Binding::Produced(_), _, _))) {
                (0..self.groups.len())
                    .map(|_| SourceRow {
                        fragments: Fragments::new(),
                    })
                    .collect()
            } else {
                Vec::new()
            },
            retained: &mut *self.retained,
            free_len: self.work.len(),
            free: {
                let mut work = self.work.iter_mut();
                core::array::from_fn(|_| work.next())
            },
            cursor: 0,
            error: None,
        }
    }
}
impl<C: PastaCurve> Coordinator<'_, '_, '_, C> {
    #[cfg(all(test, feature = "prover"))]
    pub(crate) fn input_of(&self, task: &MsmTask<'_, '_, '_, C>) -> usize {
        self.bindings[task.index].2
    }

    #[cfg(feature = "prover")]
    pub(crate) fn result_count(&self) -> usize {
        self.runs.len()
    }
    #[cfg(feature = "prover")]
    pub(crate) fn results(&self) -> Option<impl ExactSizeIterator<Item = ProjectivePoint<C>> + '_> {
        if self.runs.iter().any(|run| run.result().is_none()) {
            return None;
        }
        Some(
            self.runs
                .iter()
                .map(|run| run.result().expect("ready result")),
        )
    }
    #[cfg(feature = "prover")]
    pub(crate) fn failed(&self) -> bool {
        self.error.is_some()
    }
    #[cfg(feature = "prover")]
    /// Rebinds successfully completed runs and drops their source registrations.
    /// Every task receipt has already released its source and record readers in
    /// `complete`; removing the registrations permits producer-held Arcs to
    /// become exclusive for the next round.
    pub(crate) fn restart(&mut self) {
        assert!(self.error.is_none());
        for ((run, (input, range, _)), plan) in
            self.runs.iter_mut().zip(self.bindings).zip(self.plans)
        {
            let Binding::Produced(input) = input else {
                panic!("only produced rows are rebound");
            };
            run.rebind_produced_partition(*plan, *input, range.clone())
                .expect("drained round");
        }
        for source in &mut self.sources {
            source.fragments.clear();
        }
        self.cursor = 0;
    }
}

/// Produced data shared by producer owners, row registrations, and task readers.
/// See the module lifecycle for when mutation and pool return become possible.
pub(crate) struct Raw<C: PastaCurve> {
    pub(crate) scalars: crate::native::buffer::Buffer<PastaField<C::Scalar>>,
    pub(crate) indices: SourceIndices,
}
/// Static schedules need no owned index allocation; IPA indices follow a pool lease.
pub(crate) enum SourceIndices {
    #[cfg_attr(
        not(feature = "prover"),
        expect(
            dead_code,
            reason = "Shared MSM bindings; only prover pipelines publish source rows."
        )
    )]
    Static(&'static [u32]),
    #[cfg_attr(
        not(feature = "prover"),
        expect(
            dead_code,
            reason = "Shared MSM bindings; only prover pipelines publish source rows."
        )
    )]
    Owned(Buffer<u32>),
}
impl core::ops::Deref for SourceIndices {
    type Target = [u32];
    fn deref(&self) -> &[u32] {
        match self {
            Self::Static(values) => values,
            Self::Owned(values) => values,
        }
    }
}
impl SourceIndices {
    #[cfg(feature = "prover")]
    pub(crate) fn owned_mut(&mut self) -> &mut [u32] {
        match self {
            Self::Owned(values) => values,
            Self::Static(_) => panic!("static source indices are immutable"),
        }
    }
}

/// The usual eight producer chunks stay inline. Unusually fragmented inputs spill.
struct Fragments<T> {
    inline: [Option<T>; 8],
    len: usize,
    spill: Vec<T>,
}
impl<T> Fragments<T> {
    fn new() -> Self {
        Self {
            inline: core::array::from_fn(|_| None),
            len: 0,
            spill: Vec::new(),
        }
    }
    fn push(&mut self, value: T) {
        if self.len < self.inline.len() {
            self.inline[self.len] = Some(value);
        } else {
            self.spill.push(value);
        }
        self.len += 1;
    }
    fn iter(&self) -> impl Iterator<Item = &T> {
        self.inline[..self.len.min(8)]
            .iter()
            .flatten()
            .chain(&self.spill)
    }
    #[cfg(feature = "prover")]
    fn clear(&mut self) {
        for value in &mut self.inline {
            *value = None;
        }
        self.spill.clear();
        self.len = 0;
    }
}
/// Registrations retained independently of the readers acquired by each task.
pub(crate) struct SourceRow<C: PastaCurve> {
    fragments: Fragments<(Range<usize>, Arc<Raw<C>>)>,
}
impl<C: PastaCurve> SourceRow<C> {
    #[cfg(feature = "prover")]
    /// Drops registrations without invalidating already-acquired task readers.
    /// Producers must also wait for those readers before reclaiming exclusivity.
    pub(crate) fn clear(&mut self) {
        self.fragments.clear();
    }
    #[cfg(feature = "prover")]
    /// Retains the supplied Arc for a nonempty range; callers may keep an owner.
    pub(crate) fn publish(&mut self, range: Range<usize>, values: Arc<Raw<C>>) {
        if !range.is_empty() {
            self.fragments.push((range, values));
        }
    }
    /// Acquires all requested source fragments before a task is claimed.
    /// Missing coverage drops any clones acquired so far and leaves the task ready.
    fn acquire(&self, request: Request<'_>) -> Option<SourceReads<C>> {
        let len = request.source_scalars.max(request.source_indices);
        if len == 0 {
            return Some(SourceReads::empty());
        }
        let mut reads = SourceReads::empty();
        let end = request.offset + len;
        let mut first = request.offset;
        while first < end {
            let (range, values) = self
                .fragments
                .iter()
                .find(|(range, _)| range.contains(&first))?;
            let len = end.min(range.end) - first;
            reads.fragments.push(SourceFragment {
                range: first - request.offset..first - request.offset + len,
                offset: first - range.start,
                values: Arc::clone(values),
            });
            first += len;
        }
        reads.len = len;
        Some(reads)
    }
}
struct SourceFragment<C: PastaCurve> {
    range: Range<usize>,
    offset: usize,
    values: Arc<Raw<C>>,
}
struct SourceReads<C: PastaCurve> {
    fragments: Fragments<SourceFragment<C>>,
    len: usize,
    unavailable: bool,
}
impl<C: PastaCurve> SourceReads<C> {
    fn empty() -> Self {
        Self {
            fragments: Fragments::new(),
            len: 0,
            unavailable: false,
        }
    }
    fn unavailable() -> Self {
        Self {
            unavailable: true,
            ..Self::empty()
        }
    }
}
macro_rules! source_reads {
    ($type:ty, $field:ident) => {
        impl<C: PastaCurve> ReadView<$type> for SourceReads<C> {
            fn len(&self) -> usize {
                self.len
            }
            fn get(&self, index: usize) -> Option<&$type> {
                let SourceFragment {
                    range,
                    offset,
                    values,
                } = self
                    .fragments
                    .iter()
                    .find(|fragment| fragment.range.contains(&index))?;
                values.$field.get(offset + index - range.start)
            }
            fn contiguous(&self, range: Range<usize>) -> Option<&[$type]> {
                let prefix = self.contiguous_prefix(range.clone())?;
                (prefix.len() == range.len()).then_some(prefix)
            }
            fn contiguous_prefix(&self, range: Range<usize>) -> Option<&[$type]> {
                if range.start > range.end || range.end > self.len {
                    return None;
                }
                if range.is_empty() {
                    return Some(&[]);
                }
                let SourceFragment {
                    range: r,
                    offset,
                    values,
                } = self
                    .fragments
                    .iter()
                    .find(|fragment| fragment.range.contains(&range.start))?;
                values
                    .$field
                    .get(offset + range.start - r.start..offset + range.end.min(r.end) - r.start)
            }
        }
    };
}
source_reads!(PastaField<C::Scalar>, scalars);
source_reads!(u32, indices);
struct SourcedLease<'a, C: PastaCurve> {
    lease: Lease<'a, C>,
    source: SourceReads<C>,
}
impl<C: PastaCurve> Resources<C> for SourcedLease<'_, C> {
    fn buffers(&mut self) -> Buffers<'_, C> {
        self.lease.buffers()
    }
    fn with_source<O>(
        &mut self,
        use_buffers: impl FnOnce(Buffers<'_, C>, SourceBuffers<'_, C>) -> O,
    ) -> O {
        use_buffers(
            self.lease.buffers(),
            SourceBuffers {
                scalars: &self.source,
                indices: &self.source,
            },
        )
    }
}
