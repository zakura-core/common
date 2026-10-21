//! Completion-driven admission of owned tasks on the selected pool.

use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
#[cfg(feature = "multicore")]
use std::{any::Any, sync::Mutex};
use udon::exec::{Executor, TaskBudget};

/// An owned task carrying the input handles and leases acquired by a coordinator.
///
/// The driver retains ownership while [`Self::execute`] mutably borrows the task,
/// then transfers it to [`Coordinator::complete`]. Execution runs outside the
/// coordinator lock; it must leave the task consumable even if it unwinds.
pub(crate) trait Work: Send {
    fn execute(&mut self);
}

/// Owns readiness and unclaimed resources for completion-driven admission.
///
/// [`Self::claim`] transfers a complete lease into an owned task; arithmetic
/// belongs in [`Work::execute`]. [`Self::complete`] consumes the task to return
/// leases and publish results before successors can claim them. Neither callback
/// may wait for another task. The [MSM lease lifecycle](crate::native::commitment::msm)
/// describes a concrete resource and receipt protocol.
///
/// In the parallel path, claim, completion, active-task accounting, and panic
/// recording all hold the same coordinator mutex. Execution and task spawning
/// happen outside it. A caught unwind from claim, execution, or completion stops
/// further admission once its payload is recorded under that mutex. Other tasks
/// may already have been claimed, including before an execution panic reaches
/// the mutex: they still execute and attempt completion. The scope drains every
/// claimed task through its completion attempt before [`drive`] resumes the
/// first recorded panic, which need not be the earliest panic in time.
///
/// Completion is attempted even after execution unwinds, so it must accept a
/// partially executed task. This is not a guarantee of successful publication
/// or of restored coordinator state if claim or completion itself panics. These
/// obligations concern caught unwinding; an abort does not run this drain path.
///
/// The serial path uses no mutex and holds at most one task. It is selected
/// without `multicore`, for a serial task budget, or when the executor's closure
/// runs outside Rayon. A claim panic propagates directly. Execution and completion
/// unwinds are caught separately, and completion is still attempted; an execution
/// panic takes precedence over a completion panic. The selected panic resumes
/// before another claim. [`Pair`] applies this same protocol to both coordinators.
pub(crate) trait Coordinator: Send {
    type Task: Work;
    /// Detach a ready task with all its leases, or return `None` if none is ready.
    fn claim(&mut self) -> Option<Self::Task>;
    /// Consume the returned task, including any partially executed state.
    fn complete(&mut self, task: Self::Task);
}

pub(crate) enum Never {}
impl Work for Never {
    fn execute(&mut self) {
        match *self {}
    }
}
impl Coordinator for () {
    type Task = Never;
    fn claim(&mut self) -> Option<Self::Task> {
        None
    }
    fn complete(&mut self, task: Self::Task) {
        match task {}
    }
}

impl<C: Coordinator> Coordinator for &mut C {
    type Task = C::Task;
    fn claim(&mut self) -> Option<Self::Task> {
        (**self).claim()
    }
    fn complete(&mut self, task: Self::Task) {
        (**self).complete(task);
    }
}

pub(crate) enum Either<A, B> {
    Left(A),
    Right(B),
}
impl<A: Work, B: Work> Work for Either<A, B> {
    fn execute(&mut self) {
        match self {
            Self::Left(a) => a.execute(),
            Self::Right(b) => b.execute(),
        }
    }
}

/// Alternates admission preference across two coordinators sharing one task limit.
///
/// Each claim flips the preferred side (left first), falling back to the other
/// only if the preferred side returns `None`. [`Either`] retains the originating
/// side so execution and completion route to the matching task and coordinator.
/// The pair is one coordinator to [`drive`]: its task budget and recorded panic
/// cover both sides, with no separate per-side capacity or completion ordering.
pub(crate) struct Pair<A, B> {
    pub(crate) left: A,
    pub(crate) right: B,
    next_right: bool,
}
impl<A, B> Pair<A, B> {
    pub(crate) fn new(left: A, right: B) -> Self {
        Self {
            left,
            right,
            next_right: true,
        }
    }
}
impl<A: Coordinator, B: Coordinator> Coordinator for Pair<A, B> {
    type Task = Either<A::Task, B::Task>;
    fn claim(&mut self) -> Option<Self::Task> {
        self.next_right = !self.next_right;
        if self.next_right {
            self.right
                .claim()
                .map(Either::Right)
                .or_else(|| self.left.claim().map(Either::Left))
        } else {
            self.left
                .claim()
                .map(Either::Left)
                .or_else(|| self.right.claim().map(Either::Right))
        }
    }
    fn complete(&mut self, task: Self::Task) {
        match task {
            Either::Left(a) => self.left.complete(a),
            Either::Right(b) => self.right.complete(b),
        }
    }
}

pub(crate) struct Map<'a, I, R, F> {
    items: I,
    results: Vec<Option<R>>,
    job: &'a F,
    next: usize,
}
impl<'a, I: ExactSizeIterator, R, F> Map<'a, I, R, F> {
    pub(crate) fn new(items: I, job: &'a F) -> Self {
        let results = (0..items.len()).map(|_| None).collect();
        Self {
            items,
            results,
            job,
            next: 0,
        }
    }
    pub(crate) fn results(self) -> Vec<R> {
        self.results
            .into_iter()
            .map(|r| r.expect("completed application task"))
            .collect()
    }
}
pub(crate) struct MapTask<'a, T, R, F> {
    index: usize,
    input: Option<T>,
    output: Option<R>,
    job: &'a F,
}
impl<T: Send, R: Send, F: Fn(T) -> R + Sync> Work for MapTask<'_, T, R, F> {
    fn execute(&mut self) {
        self.output = Some((self.job)(self.input.take().unwrap()));
    }
}
impl<'a, I, R, F> Coordinator for Map<'a, I, R, F>
where
    I: Iterator + Send,
    I::Item: Send,
    R: Send,
    F: Fn(I::Item) -> R + Sync,
{
    type Task = MapTask<'a, I::Item, R, F>;
    fn claim(&mut self) -> Option<Self::Task> {
        let input = self.items.next()?;
        let index = self.next;
        self.next += 1;
        Some(MapTask {
            index,
            input: Some(input),
            output: None,
            job: self.job,
        })
    }
    fn complete(&mut self, task: Self::Task) {
        self.results[task.index] = task.output;
    }
}

#[cfg(feature = "multicore")]
struct State<'a, C> {
    coordinator: &'a mut C,
    active: usize,
    limit: usize,
    panic: Option<Box<dyn Any + Send>>,
}
#[cfg(feature = "multicore")]
impl<C: Coordinator> State<'_, C> {
    fn claim(&mut self) -> Option<C::Task> {
        if self.panic.is_some() || self.active == self.limit {
            return None;
        }
        let task = match catch_unwind(AssertUnwindSafe(|| self.coordinator.claim())) {
            Ok(task) => task?,
            Err(panic) => {
                self.panic = Some(panic);
                return None;
            }
        };
        self.active += 1;
        Some(task)
    }
}

#[cfg(feature = "multicore")]
fn dispatch<'scope, C: Coordinator + 'scope>(
    scope: &rayon::ScopeFifo<'scope>,
    shared: &'scope Mutex<State<'_, C>>,
) {
    loop {
        let Some(mut task) = shared.lock().unwrap().claim() else {
            return;
        };
        scope.spawn_fifo(move |scope| {
            loop {
                let panic = catch_unwind(AssertUnwindSafe(|| task.execute())).err();
                let (next, fill) = {
                    let mut state = shared.lock().unwrap();
                    state.panic = state.panic.take().or(panic);
                    let publication =
                        catch_unwind(AssertUnwindSafe(|| state.coordinator.complete(task))).err();
                    state.panic = state.panic.take().or(publication);
                    state.active -= 1;
                    let next = state.claim();
                    let fill = state.panic.is_none() && state.active < state.limit;
                    (next, fill)
                };
                // A completion may release a whole frontier. Fill vacant
                // leases, then keep one successor on this worker's stack.
                if fill {
                    dispatch(scope, shared);
                }
                match next {
                    Some(next) => task = next,
                    None => return,
                }
            }
        });
    }
}

/// Idle drainers return to Rayon, whose workers can serve other operations or
/// park. Only a publication starts more drainers; there is no readiness poll.
pub(crate) fn drive<C: Coordinator, E: Executor>(
    coordinator: &mut C,
    budget: TaskBudget,
    executor: &E,
) {
    #[cfg(not(feature = "multicore"))]
    let _ = executor;
    if !cfg!(feature = "multicore") || budget == TaskBudget::SERIAL {
        serial(coordinator);
        #[cfg(feature = "multicore")]
        return;
    }
    #[cfg(feature = "multicore")]
    executor.join(
        || {
            if rayon::current_thread_index().is_none() {
                serial(coordinator);
                return;
            }
            let shared = Mutex::new(State {
                coordinator,
                active: 0,
                limit: budget.get(),
                panic: None,
            });
            rayon::scope_fifo(|scope| dispatch(scope, &shared));
            let state = shared.into_inner().unwrap();
            assert_eq!(state.active, 0, "the scope drains all owned leases");
            if let Some(panic) = state.panic {
                resume_unwind(panic);
            }
        },
        || (),
    );
}

fn serial<C: Coordinator>(coordinator: &mut C) {
    while let Some(mut task) = coordinator.claim() {
        let panic = catch_unwind(AssertUnwindSafe(|| task.execute())).err();
        let publication = catch_unwind(AssertUnwindSafe(|| coordinator.complete(task))).err();
        if let Some(panic) = panic.or(publication) {
            resume_unwind(panic);
        }
    }
}

#[cfg(all(test, feature = "multicore"))]
mod tests;
