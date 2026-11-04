use super::*;
use std::{
    sync::{
        Arc, Barrier,
        atomic::{AtomicBool, AtomicUsize, Ordering},
        mpsc,
    },
    time::Duration,
};

struct Pool(rayon::ThreadPool);
impl Pool {
    fn new(workers: usize) -> Self {
        Self(
            rayon::ThreadPoolBuilder::new()
                .num_threads(workers)
                .build()
                .unwrap(),
        )
    }
}
impl Executor for Pool {
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

struct TaskJob(Box<dyn FnMut() + Send>);
impl Work for TaskJob {
    fn execute(&mut self) {
        self.0();
    }
}

/// The consumer must release the other producer. A wave barrier here would
/// time out, even though a second worker is available to run the consumer.
#[test]
fn publishes_consumers_before_the_producer_tail() {
    struct Graph {
        producers: std::vec::IntoIter<TaskJob>,
        consumer: Option<TaskJob>,
        published: Arc<AtomicUsize>,
        completed: usize,
    }
    impl Coordinator for Graph {
        type Task = TaskJob;
        fn claim(&mut self) -> Option<TaskJob> {
            self.producers.next().or_else(|| {
                (self.published.load(Ordering::Acquire) != 0)
                    .then(|| self.consumer.take())
                    .flatten()
            })
        }
        fn complete(&mut self, _: TaskJob) {
            self.completed += 1;
            self.published.store(self.completed, Ordering::Release);
        }
    }
    let (send, receive) = mpsc::channel();
    let published = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&published);
    let mut graph = Graph {
        producers: vec![
            TaskJob(Box::new(|| {})),
            TaskJob(Box::new(move || {
                receive.recv_timeout(Duration::from_secs(5)).unwrap();
            })),
        ]
        .into_iter(),
        consumer: Some(TaskJob(Box::new(move || {
            assert_eq!(observed.load(Ordering::Acquire), 1);
            send.send(()).unwrap();
        }))),
        published,
        completed: 0,
    };
    drive(&mut graph, TaskBudget::new(2).unwrap(), &Pool::new(2));
    assert_eq!(graph.completed, 3);
}

#[test]
fn one_worker_and_serial_executor_preserve_results() {
    for workers in [1, 2, 4] {
        let job = |n: usize| n * n;
        let mut map = Map::new(0..71, &job);
        drive(
            &mut map,
            TaskBudget::new(workers).unwrap(),
            &Pool::new(workers),
        );
        assert_eq!(map.results(), (0..71).map(job).collect::<Vec<_>>());
    }
    let job = |n: usize| n + 1;
    let mut map = Map::new(0..19, &job);
    drive(
        &mut map,
        TaskBudget::new(4).unwrap(),
        &udon::exec::SerialExecutor,
    );
    assert_eq!(map.results(), (1..20).collect::<Vec<_>>());
}

#[test]
fn panic_stops_admission_and_drains_leases() {
    for publication_panics in [false, true] {
        struct Graph {
            jobs: std::vec::IntoIter<TaskJob>,
            claimed: usize,
            returned: usize,
            send: mpsc::Sender<()>,
            publication_panics: bool,
        }
        impl Coordinator for Graph {
            type Task = TaskJob;
            fn claim(&mut self) -> Option<TaskJob> {
                let job = self.jobs.next()?;
                self.claimed += 1;
                Some(job)
            }
            fn complete(&mut self, _: TaskJob) {
                self.returned += 1;
                if self.returned == 1 {
                    self.send.send(()).unwrap();
                    assert!(!self.publication_panics, "publication failure");
                }
            }
        }
        let barrier = Arc::new(Barrier::new(2));
        let first = Arc::clone(&barrier);
        let drained = Arc::new(AtomicBool::new(false));
        let returned = Arc::clone(&drained);
        let (send, receive) = mpsc::channel();
        let mut graph = Graph {
            jobs: vec![
                TaskJob(Box::new(move || {
                    first.wait();
                    assert!(publication_panics, "kernel failure");
                })),
                TaskJob(Box::new(move || {
                    barrier.wait();
                    receive.recv_timeout(Duration::from_secs(5)).unwrap();
                    returned.store(true, Ordering::Release);
                })),
                TaskJob(Box::new(|| panic!("must not admit a successor"))),
            ]
            .into_iter(),
            claimed: 0,
            returned: 0,
            send,
            publication_panics,
        };
        assert!(
            catch_unwind(AssertUnwindSafe(|| {
                drive(&mut graph, TaskBudget::new(2).unwrap(), &Pool::new(2));
            }))
            .is_err()
        );
        assert_eq!(graph.claimed, 2);
        assert_eq!(graph.returned, 2);
        assert!(drained.load(Ordering::Acquire));
    }
}

#[test]
fn execution_maps_exact_iterators_in_order_and_keeps_error_values() {
    use crate::native::worker::Execution;
    for workers in [1, 4] {
        let pool = Pool::new(workers);
        let execution = Execution::new(&pool, TaskBudget::new(workers).unwrap());
        assert!(execution.map(0..0, |i, _| i).is_empty());
        assert_eq!(execution.map([3, 1, 2], |i, _| i), [3, 1, 2]);
        let mut values = [0; 19];
        let results = execution.map(values.iter_mut().zip(0..19), |(value, i), _| {
            *value = i;
            if i % 3 == 0 { Err(i) } else { Ok(i) }
        });
        assert_eq!(values, core::array::from_fn(|i| i));
        assert_eq!(
            results,
            (0..19)
                .map(|i| if i % 3 == 0 { Err(i) } else { Ok(i) })
                .collect::<Vec<_>>()
        );
        let drops = AtomicUsize::new(0);
        struct Lease<'a>(&'a AtomicUsize);
        impl Drop for Lease<'_> {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::Relaxed);
            }
        }
        let leases = (0..19).map(|_| Lease(&drops)).collect::<Vec<_>>();
        assert!(
            catch_unwind(AssertUnwindSafe(|| {
                execution.map(leases.into_iter().enumerate(), |(i, lease), _| {
                    assert_ne!(i, 0, "mapped task failure");
                    lease
                })
            }))
            .is_err()
        );
        assert_eq!(drops.load(Ordering::Relaxed), 19);
    }
}
