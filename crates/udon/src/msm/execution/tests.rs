mod suffix;

use super::{
    BatchPlan, Buffers, JobStorage, MsmPlan, MsmRun, ParallelMsmRun, ProducedInput, Resources,
    SourceBuffers, WorkKind, WorkerStorage,
};
use crate::{
    curve::{
        AffinePoint, CurveError, EisensteinTableBatch, Pallas, PastaCurve, Point,
        PreparedAffinePoint, ProjectivePoint, Vesta,
    },
    exec::execution::test_pool as run_pool,
    exec::{
        SerialExecutor, TaskBudget,
        execution::{Identity, Outcome, ReadView, TaskError, TaskStorage},
    },
    field::{CanonicalUint, PastaField},
    msm::execution::test_buffers::{Arena, Lease, Work},
    msm::{
        Accumulation, Algorithm, ArithmeticOptions, Bases, BatchOptions, Input, PreparedScalars,
        Requirements, ScalarStorage, Scratch, Selection, policy::InvalidWindow,
    },
};
use spin::RwLock;
use std::num::NonZeroUsize;
use std::{string::ToString, vec, vec::Vec};

struct Fragments<'a, T>(&'a [T]);

#[test]
fn produced_alpha_falls_back_under_a_small_workspace() {
    use crate::{
        exec::ExecutionOptions,
        msm::{AlphaCodebook, AlphaCoefficient, AlphaDescription, AlphaTable},
    };
    fn check<C: PastaCurve>() {
        let d = AlphaDescription::new(7).unwrap();
        let mut codes = vec![0; d.codes()];
        let mut coefficients = vec![AlphaCoefficient::ZERO; d.layers()];
        let book = AlphaCodebook::prepare(
            d,
            &mut codes,
            &mut coefficients,
            &mut vec![0; d.codebook_scratch()],
        );
        let g = AffinePoint::<C>::GENERATOR;
        let mut entries = vec![g; d.layers()];
        let table = AlphaTable::prepare(
            book,
            &[g],
            &mut entries,
            &mut [ProjectivePoint::IDENTITY],
            &mut [PastaField::ZERO],
            TaskBudget::SERIAL,
            &SerialExecutor,
        );
        let input = ProducedInput::dense(Bases::Alpha(table));
        let options = ExecutionOptions::DEFAULT.with_memory_limit(4096);
        let plan = MsmPlan::for_produced(input, NonZeroUsize::new(1).unwrap(), options).unwrap();
        assert!(!matches!(plan.job.geometry, super::Geometry::Alpha(_)));
        let scalars = [PastaField::<C::Scalar>::from_u64(7).invert().unwrap()];
        let expected = g.mul_projective(&scalars[0]);
        let arena = Arena::new(plan);
        let work = [RwLock::new(Work::new(core::iter::once(plan.temporary())))];
        let mut identity = Identity::new();
        let mut slots = [TaskStorage::EMPTY];
        let mut run = MsmRun::new_produced_partition(plan, input, 0..1, &mut identity, &mut slots);
        while run.result().is_none() {
            let mut ready = [None];
            assert_eq!(run.ready(&mut ready), 1);
            let request = ready[0].unwrap();
            let mut task = run
                .try_claim(request, || {
                    Some(ProducedLease {
                        arithmetic: arena.acquire(request, &work)?,
                        scalars: Fragments(&scalars),
                        indices: Fragments(&[]),
                    })
                })
                .unwrap()
                .unwrap();
            task.execute().unwrap();
            assert_eq!(run.complete(task.finish()).unwrap().error, None);
        }
        assert_eq!(run.result(), Some(expected));

        // A tiny row uses originals even without a ceiling. A substantial row
        // selects alpha so binding must reject a bank without expanded layers.
        let scalars = [scalars[0]; 128];
        let indices = [0; 128];
        let mut records = [ScalarStorage::ZERO; 128];
        let prepared =
            PreparedScalars::prepare(&scalars, &mut records, TaskBudget::SERIAL, &SerialExecutor);
        let alpha = MsmPlan::for_input(
            &Input::indexed_prepared(Bases::Alpha(table), &indices, prepared).unwrap(),
            ExecutionOptions::DEFAULT,
        )
        .unwrap();
        assert!(matches!(alpha.job.geometry, super::Geometry::Alpha(7)));
        assert!(
            !alpha
                .accepts(Input::indexed_prepared(Bases::Affine(&[g]), &indices, prepared).unwrap())
        );
        let streaming = MsmPlan::new_with(
            1,
            ArithmeticOptions::DEFAULT
                .with_algorithm(Algorithm::StreamingBooth { width: None })
                .unwrap(),
            NonZeroUsize::new(1).unwrap(),
        )
        .unwrap();
        assert_eq!(prepared.alpha_cache_len(&streaming), 0);
        let mut storage = [0xa5; 8];
        let unchanged = prepared.cache_alpha(
            &streaming,
            book,
            &mut storage,
            TaskBudget::SERIAL,
            &SerialExecutor,
        );
        assert_eq!(unchanged.retained_bytes(), prepared.retained_bytes());
        assert_eq!(storage, [0xa5; 8]);
    }
    check::<Pallas>();
    check::<Vesta>();
}

impl<T> ReadView<T> for Fragments<'_, T> {
    fn len(&self) -> usize {
        self.0.len()
    }
    fn get(&self, index: usize) -> Option<&T> {
        self.0.get(index)
    }
    fn contiguous_prefix(&self, range: core::ops::Range<usize>) -> Option<&[T]> {
        // Producer fragments deliberately straddle recoder boundaries.
        if range.end > self.len() || range.start > range.end {
            return None;
        }
        self.0
            .get(range.start..range.end.min((range.start / 13 + 1) * 13))
    }
}
struct ProducedLease<'a, C: PastaCurve, I = Fragments<'a, u32>> {
    arithmetic: Lease<'a, C>,
    scalars: Fragments<'a, PastaField<C::Scalar>>,
    indices: I,
}
impl<C: PastaCurve, I: ReadView<u32>> Resources<C> for ProducedLease<'_, C, I> {
    fn buffers(&mut self) -> Buffers<'_, C> {
        self.arithmetic.buffers()
    }
    fn with_source<O>(
        &mut self,
        use_buffers: impl FnOnce(Buffers<'_, C>, SourceBuffers<'_, C>) -> O,
    ) -> O {
        use_buffers(
            self.arithmetic.buffers(),
            SourceBuffers {
                scalars: &self.scalars,
                indices: &self.indices,
            },
        )
    }
}

fn produced<C: PastaCurve>() {
    const TERMS: usize = 701;
    let bases: Vec<_> = (1..=TERMS)
        .map(|i| {
            *ladder::<C>(PastaField::from_u64(i as u64))
                .to_point()
                .as_affine()
                .unwrap()
        })
        .collect();
    let scalars: Vec<_> = (0..TERMS)
        .map(|i| {
            PastaField::<C::Scalar>::from_u64(i as u64 + 7)
                .invert()
                .unwrap()
        })
        .collect();
    let indices: Vec<_> = (0..TERMS).map(|i| (i * 11 % TERMS) as u32).collect();
    let description = super::super::AlphaDescription::new(7).unwrap();
    let mut codes = vec![0; description.codes()];
    let mut coefficients = vec![super::super::AlphaCoefficient::ZERO; description.layers()];
    let book = super::super::AlphaCodebook::prepare(
        description,
        &mut codes,
        &mut coefficients,
        &mut vec![0; description.codebook_scratch()],
    );
    let mut entries = vec![AffinePoint::<C>::GENERATOR; TERMS * description.layers()];
    let table = super::super::AlphaTable::prepare(
        book,
        &bases,
        &mut entries,
        &mut vec![ProjectivePoint::IDENTITY; TERMS],
        &mut vec![PastaField::ZERO; TERMS],
        TaskBudget::SERIAL,
        &SerialExecutor,
    );
    for bank in [Bases::Affine(&bases), Bases::Alpha(table)] {
        for indexed in [false, true] {
            for streaming in [false, true] {
                let options = if streaming {
                    ArithmeticOptions::DEFAULT
                        .with_algorithm(Algorithm::StreamingBooth { width: None })
                        .unwrap()
                        .with_chunk_size(NonZeroUsize::new(512).unwrap())
                } else {
                    ArithmeticOptions::DEFAULT
                };
                let input = if indexed {
                    ProducedInput::indexed(bank, TERMS)
                } else {
                    ProducedInput::dense(bank)
                };
                let original = if streaming {
                    MsmPlan::<C>::new_with(TERMS, options, NonZeroUsize::new(TERMS).unwrap())
                        .unwrap()
                } else {
                    MsmPlan::<C>::for_produced(
                        input,
                        NonZeroUsize::new(TERMS).unwrap(),
                        crate::exec::ExecutionOptions::default(),
                    )
                    .unwrap()
                };
                let plan = original
                    .with_grain(NonZeroUsize::new(512).unwrap())
                    .unwrap();
                assert_eq!(plan.output_slots(), original.output_slots());
                assert_eq!(plan.preparation_terms(), 256);
                let range = 17..619;
                let expected = ladder::<C>(range.clone().fold(PastaField::ZERO, |sum, i| {
                    sum.add(&scalars[i].mul(&PastaField::<_>::from_u64(if indexed {
                        indices[i] as u64 + 1
                    } else {
                        i as u64 + 1
                    })))
                }));
                let arena = Arena::new(plan);
                let work = [RwLock::new(Work::new(core::iter::once(plan.temporary())))];
                let mut identity = Identity::new();
                let mut slots = [const { TaskStorage::EMPTY }; 3];
                let mut run = MsmRun::new_produced_partition(
                    plan,
                    input,
                    range.clone(),
                    &mut identity,
                    &mut slots,
                );
                let mut ready = [None; 3];
                run.ready(&mut ready);
                let old_request = ready[0].unwrap();
                for repetition in 0..2 {
                    if repetition != 0 {
                        run.rebind_produced_partition(plan, input, range.clone())
                            .unwrap();
                        assert!(matches!(
                            run.try_claim(old_request, || None::<ProducedLease<'_, C>>),
                            Err(TaskError::Stale)
                        ));
                    }
                    let mut first_ready = false;
                    let mut completed_later_preparation = false;
                    while run.result().is_none() {
                        let count = run.ready(&mut ready);
                        let mut progress = false;
                        for request in ready[..count].iter().flatten().rev() {
                            if request.kind == WorkKind::Prepare
                                && request.offset == range.start
                                && !first_ready
                            {
                                assert!(
                                    run.try_claim(*request, || None::<ProducedLease<'_, C>>)
                                        .unwrap()
                                        .is_none()
                                );
                                continue;
                            }
                            let source_range = request.offset..request.offset + request.terms;
                            let mut task = run
                                .try_claim(*request, || {
                                    Some(ProducedLease {
                                        arithmetic: arena.acquire(*request, &work)?,
                                        scalars: Fragments(&scalars[source_range.clone()]),
                                        indices: Fragments(if indexed {
                                            &indices[source_range]
                                        } else {
                                            &[]
                                        }),
                                    })
                                })
                                .unwrap()
                                .unwrap();
                            task.execute().unwrap();
                            let published = run.complete(task.finish()).unwrap();
                            assert_eq!(published.error, None);
                            if request.kind == WorkKind::Prepare && !first_ready {
                                completed_later_preparation = true;
                            }
                            progress = true;
                        }
                        if !first_ready {
                            first_ready = true;
                        } else {
                            assert!(progress);
                        }
                    }
                    assert!(
                        completed_later_preparation,
                        "indexed={indexed} streaming={streaming} repetition={repetition} grain={}",
                        plan.grain()
                    );
                    assert_eq!(run.result(), Some(expected));
                    assert!(!run.is_failed());
                    assert_eq!(run.inflight(), 0);
                }
            }
        }
    }
}

#[test]
fn produced_fragments_wait_for_sources_and_rebind_partition_epochs() {
    produced::<Pallas>();
    produced::<Vesta>();
}

#[test]
fn preparation_checks_all_capacities_before_writing() {
    let bases = [AffinePoint::<Pallas>::GENERATOR; 513];
    let scalars = [PastaField::from_u64(7); 513];
    let input = Input::new(Bases::Affine(&bases), &scalars);
    let plan = MsmPlan::new(513, Default::default()).unwrap();
    for short_digits in [false, true] {
        let mut identity = Identity::new();
        let mut slots = [TaskStorage::EMPTY];
        let mut run = MsmRun::new(plan, input, &mut identity, &mut slots);
        let mut ready = [None];
        assert_eq!(run.ready(&mut ready), 1);
        let request = ready[0].unwrap();
        assert_eq!(request.kind, WorkKind::Prepare);
        assert!(request.scratch.scalars() > 0 && request.scratch.digits() > 0);
        let mut records = vec![ScalarStorage::ZERO; request.scratch.scalars()];
        let mut digits = vec![0xa5; request.scratch.digits()];
        let scalar_len = records.len() - usize::from(!short_digits);
        let digit_len = digits.len() - usize::from(short_digits);
        let mut task = run
            .try_claim(request, || {
                Some(Buffers {
                    records: &[],
                    digits: &[],
                    scratch: Scratch::new(
                        &mut records[..scalar_len],
                        &mut digits[..digit_len],
                        &mut [],
                        &mut [],
                        &mut [],
                        &mut [],
                    ),
                    buckets: &mut [],
                    output: &mut [],
                    partials: &[],
                })
            })
            .unwrap()
            .unwrap();
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                task.execute().unwrap();
            }))
            .is_err()
        );
        let published = run.complete(task.finish()).unwrap();
        assert_eq!(published.outcome, Outcome::Failed);
        assert_eq!(published.error, None);
        assert!(records.iter().all(|record| *record == ScalarStorage::ZERO));
        assert!(digits.iter().all(|digit| *digit == 0xa5));
        assert!(run.is_failed());
        assert_eq!(run.inflight(), 0);
    }
}

#[test]
fn invalid_produced_sources_preserve_destinations_and_drain_admitted_tasks() {
    let bases = [AffinePoint::<Pallas>::GENERATOR; 513];
    let scalars = [PastaField::from_u64(7); 256];
    let indices = [0; 256];
    let mut invalid_indices = indices;
    invalid_indices[19] = bases.len() as u32;
    let plan = MsmPlan::new_with(
        513,
        ArithmeticOptions::DEFAULT,
        NonZeroUsize::new(513).unwrap(),
    )
    .unwrap();
    for invalid in 0..3 {
        let arena = Arena::new(plan);
        let work = [RwLock::new(Work::new(core::iter::once(plan.temporary())))];
        let mut identity = Identity::new();
        let mut slots = [const { TaskStorage::EMPTY }; 2];
        let mut run = MsmRun::new_produced_partition(
            plan,
            ProducedInput::indexed(Bases::Affine(&bases), 513),
            1..513,
            &mut identity,
            &mut slots,
        );
        let mut ready = [None; 2];
        assert_eq!(run.ready(&mut ready), 2);
        let first = ready[0].unwrap();
        let second = ready[1].unwrap();
        let mut pending = run
            .try_claim(first, || {
                Some(ProducedLease {
                    arithmetic: arena.acquire(first, &work)?,
                    scalars: Fragments(&scalars),
                    indices: Fragments(&indices),
                })
            })
            .unwrap()
            .unwrap();
        let mut bad = run
            .try_claim(second, || {
                Some(ProducedLease {
                    arithmetic: arena.acquire(second, &work)?,
                    scalars: Fragments(if invalid == 0 {
                        &scalars[..255]
                    } else {
                        &scalars
                    }),
                    indices: Fragments(match invalid {
                        1 => &indices[..255],
                        2 => &invalid_indices,
                        _ => &indices,
                    }),
                })
            })
            .unwrap()
            .unwrap();
        let outcome = if invalid < 2 {
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| bad.execute())).is_err()
            );
            Outcome::Failed
        } else {
            bad.execute().unwrap();
            Outcome::Success
        };
        let completion = bad.finish();
        assert_eq!(completion.outcome(), outcome);
        let published = run.complete(completion).unwrap();
        assert_eq!(published.outcome, outcome);
        match invalid {
            0 | 1 => assert!(published.error.is_none()),
            _ => assert_eq!(
                published.error,
                Some(CurveError::BaseIndexOutOfBounds {
                    position: second.offset + 19,
                    index: bases.len() as u32,
                    bases: bases.len(),
                })
            ),
        }
        let (records, digits) = published.resources.arithmetic.preparation();
        assert!(records.iter().all(|v| *v == ScalarStorage::ZERO));
        assert!(digits.iter().all(|v| *v == 0));
        drop(published);
        assert!(run.is_failed());
        assert_eq!(run.ready(&mut ready), 0);
        assert_eq!(run.inflight(), 1);
        pending.execute().unwrap();
        drop(run.complete(pending.finish()).unwrap());
        assert_eq!(run.inflight(), 0);
        assert_eq!(run.result(), None);
        assert_eq!(
            run.rebind_produced(plan, ProducedInput::indexed(Bases::Affine(&bases), 513)),
            Err(TaskError::Failed)
        );
        assert!(arena.acquire(first, &work).is_some());
        assert!(arena.acquire(second, &work).is_some());
    }
}

#[test]
fn produced_index_prefixes_preserve_validation_before_writes() {
    struct Indices<'a> {
        values: &'a [u32],
        prefix: Option<usize>,
        missing: Option<usize>,
    }
    impl ReadView<u32> for Indices<'_> {
        fn len(&self) -> usize {
            self.values.len()
        }
        fn get(&self, index: usize) -> Option<&u32> {
            self.values
                .get(index)
                .filter(|_| self.missing != Some(index))
        }
        fn contiguous_prefix(&self, range: core::ops::Range<usize>) -> Option<&[u32]> {
            let width = self.prefix?;
            if width == 0 {
                return Some(&[]);
            }
            if range.end > self.len() || range.start > range.end {
                return None;
            }
            self.values
                .get(range.start..range.end.min((range.start / width + 1) * width))
        }
    }
    fn projective_words<C: PastaCurve>(points: &[ProjectivePoint<C>]) -> Vec<[[u64; 4]; 3]> {
        points
            .iter()
            .map(|point| {
                let (x, y, z) = point.coordinates();
                [
                    x.montgomery_limbs(),
                    y.montgomery_limbs(),
                    z.montgomery_limbs(),
                ]
            })
            .collect()
    }
    macro_rules! destinations {
        ($buffers:expr) => {{
            let buffers = $buffers;
            (
                buffers.scratch.scalars.to_vec(),
                buffers.scratch.digits.to_vec(),
                buffers.scratch.affine.to_vec(),
                projective_words(buffers.scratch.projective),
                buffers
                    .scratch
                    .field
                    .iter()
                    .map(PastaField::montgomery_limbs)
                    .collect::<Vec<_>>(),
                buffers.scratch.indices.to_vec(),
                projective_words(buffers.buckets),
                projective_words(buffers.output),
            )
        }};
    }
    fn check<C: PastaCurve>() {
        let bases = [AffinePoint::<C>::GENERATOR; 65];
        let scalars = [PastaField::<C::Scalar>::from_u64(7); 64];
        let valid = [0; 64];
        for streaming in [false, true] {
            let options = if streaming {
                ArithmeticOptions::DEFAULT
                    .with_algorithm(Algorithm::StreamingBooth { width: None })
                    .unwrap()
            } else {
                ArithmeticOptions::DEFAULT
            };
            let plan = MsmPlan::new_with(65, options, NonZeroUsize::new(65).unwrap()).unwrap();
            for prefix in [Some(64), Some(13), None, Some(0)] {
                for fail_kind in [WorkKind::Prepare, WorkKind::Window] {
                    // Cover both sides of prefix boundaries and a final short prefix.
                    // Two invalid values ensure the first error keeps its absolute offset.
                    for (invalid_at, missing) in [
                        (Some(0), false),
                        (Some(12), false),
                        (Some(13), false),
                        (Some(25), false),
                        (Some(26), false),
                        (Some(63), false),
                        (None, false),
                        (Some(13), true),
                    ] {
                        if missing && prefix.is_some_and(|width| width != 0) {
                            continue;
                        }
                        let mut invalid = valid;
                        if let Some(position) = invalid_at {
                            invalid[position] = bases.len() as u32;
                            invalid[63] = u32::MAX;
                        }
                        let arena = Arena::new(plan);
                        let work = [RwLock::new(Work::new(core::iter::once(plan.temporary())))];
                        let mut identity = Identity::new();
                        let mut slots = [TaskStorage::EMPTY];
                        let mut run = MsmRun::new_produced_partition(
                            plan,
                            ProducedInput::indexed(Bases::Affine(&bases), 65),
                            1..65,
                            &mut identity,
                            &mut slots,
                        );
                        loop {
                            let mut ready = [None];
                            assert_eq!(run.ready(&mut ready), 1);
                            let request = ready[0].unwrap();
                            let failing = request.kind == fail_kind && invalid_at.is_some();
                            // Window failures receive a fresh malformed view only after a
                            // successful Prepare: validation cannot be cached across leases.
                            let mut resources = ProducedLease {
                                arithmetic: arena.acquire(request, &work).unwrap(),
                                scalars: Fragments(&scalars),
                                indices: Indices {
                                    values: if failing { &invalid } else { &valid },
                                    prefix,
                                    missing: if failing && missing { invalid_at } else { None },
                                },
                            };
                            let before = failing.then(|| {
                                let buffers = resources.buffers();
                                buffers.scratch.digits.fill(0xa5);
                                buffers.scratch.projective.fill(ProjectivePoint::GENERATOR);
                                buffers.scratch.field.fill(PastaField::ONE);
                                buffers.scratch.indices.fill(usize::MAX);
                                buffers.buckets.fill(ProjectivePoint::GENERATOR);
                                buffers.output.fill(ProjectivePoint::GENERATOR);
                                destinations!(buffers)
                            });
                            let mut task =
                                run.try_claim(request, || Some(resources)).unwrap().unwrap();
                            if failing && missing {
                                assert!(
                                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                        task.execute()
                                    }))
                                    .is_err()
                                );
                            } else {
                                task.execute().unwrap();
                            }
                            let mut published = run.complete(task.finish()).unwrap();
                            if let Some(before) = before {
                                let position = invalid_at.unwrap();
                                if missing {
                                    assert_eq!(published.outcome, Outcome::Failed);
                                    assert_eq!(published.error, None);
                                } else {
                                    assert_eq!(
                                        published.error,
                                        Some(CurveError::BaseIndexOutOfBounds {
                                            position: request.offset + position,
                                            index: invalid[position],
                                            bases: bases.len(),
                                        })
                                    );
                                }
                                assert!(destinations!(published.resources.buffers()) == before);
                                drop(published);
                                assert!(run.is_failed());
                                assert_eq!(run.inflight(), 0);
                                assert_eq!(run.result(), None);
                                break;
                            }
                            assert_eq!(published.error, None);
                            drop(published);
                            if let Some(result) = run.result() {
                                assert!(invalid_at.is_none());
                                assert_eq!(result, ladder::<C>(PastaField::from_u64(7 * 64)));
                                break;
                            }
                        }
                    }
                }
            }
        }
    }
    check::<Pallas>();
    check::<Vesta>();
}

#[test]
fn cached_borrowed_partitions_preserve_global_scalar_and_index_offsets() {
    let bases: Vec<_> = (1..=701)
        .map(|i| {
            *ladder::<Vesta>(PastaField::from_u64(i))
                .to_point()
                .as_affine()
                .unwrap()
        })
        .collect();
    let scalars: Vec<_> = (0..bases.len())
        .map(|i| PastaField::<_>::from_u64(i as u64 + 3).invert().unwrap())
        .collect();
    let indices: Vec<_> = (0..bases.len())
        .map(|i| (i * 11 % bases.len()) as u32)
        .collect();
    let mut records = vec![ScalarStorage::ZERO; scalars.len()];
    let prepared =
        PreparedScalars::prepare(&scalars, &mut records, TaskBudget::SERIAL, &SerialExecutor);
    let mut digits = vec![0; prepared.cache_len_with(ArithmeticOptions::DEFAULT).unwrap()];
    let cached = prepared
        .cache_with(ArithmeticOptions::DEFAULT, &mut digits)
        .unwrap();
    let input = Selection::indexed(Bases::Affine(&bases), &indices)
        .unwrap()
        .with_prepared_scalars(cached);
    let original = MsmPlan::new_with(
        input.len(),
        ArithmeticOptions::DEFAULT,
        NonZeroUsize::new(input.len()).unwrap(),
    )
    .unwrap();
    for plan in [
        original,
        original
            .with_grain(NonZeroUsize::new(256).unwrap())
            .unwrap(),
    ] {
        for range in [0..0, 17..619, 619..701] {
            let expected = ladder::<Vesta>(range.clone().fold(PastaField::ZERO, |sum, i| {
                sum.add(&scalars[i].mul(&PastaField::<_>::from_u64(indices[i] as u64 + 1)))
            }));
            let arena = Arena::new(plan);
            let work = [RwLock::new(Work::new(core::iter::once(plan.temporary())))];
            let mut identity = Identity::new();
            let mut slots = [const { TaskStorage::EMPTY }; 3];
            let mut run = MsmRun::new_partition(plan, input, range, &mut identity, &mut slots);
            while run.result().is_none() {
                let mut ready = [None; 3];
                let count = run.ready(&mut ready);
                assert_ne!(count, 0);
                for request in ready[..count].iter().flatten().rev() {
                    let mut task = run
                        .try_claim(*request, || arena.acquire(*request, &work))
                        .unwrap()
                        .unwrap();
                    task.execute().unwrap();
                    let published = run.complete(task.finish()).unwrap();
                    assert_eq!(published.error, None);
                }
            }
            assert_eq!(run.result(), Some(expected));
        }
    }
}

fn check<C: PastaCurve>() {
    const TERMS: usize = 385;
    let bases = vec![AffinePoint::<C>::GENERATOR; TERMS];
    let scalars: Vec<_> = (0..TERMS)
        .map(|i| {
            PastaField::<C::Scalar>::from_canonical_uint(CanonicalUint::from_limbs([
                i as u64 * 17 + 3,
                0xabcd,
                i as u64 * 11,
                0x1234_5678,
            ]))
            .unwrap()
        })
        .collect();
    let mut expected = ProjectivePoint::<C>::IDENTITY;
    let scalar = scalars.iter().fold(PastaField::ZERO, |sum, s| sum.add(s));
    for byte in scalar.to_bytes().iter().rev() {
        for bit in (0..8).rev() {
            expected = expected.double();
            if byte & (1 << bit) != 0 {
                expected = expected.add(&ProjectivePoint::GENERATOR);
            }
        }
    }
    let options = [
        ArithmeticOptions::DEFAULT,
        ArithmeticOptions::DEFAULT
            .with_algorithm(Algorithm::Joint)
            .unwrap(),
        ArithmeticOptions::DEFAULT
            .with_algorithm(Algorithm::Booth {
                width: Some(11),
                accumulation: Accumulation::Projective,
            })
            .unwrap(),
        ArithmeticOptions::DEFAULT
            .with_algorithm(Algorithm::Booth {
                width: Some(7),
                accumulation: Accumulation::Hybrid,
            })
            .unwrap(),
        ArithmeticOptions::DEFAULT
            .with_algorithm(Algorithm::StreamingBooth { width: None })
            .unwrap(),
    ];
    for options in options {
        let plan = MsmPlan::<C>::new_with(TERMS, options, NonZeroUsize::new(256).unwrap()).unwrap();
        let retained = counts(plan.retained());
        let temporary = counts(plan.temporary());
        for slots in [1, 3] {
            assert_eq!(
                counts(
                    plan.retained_for_slots(NonZeroUsize::new(slots).unwrap())
                        .unwrap()
                ),
                retained.map(|count| count * slots),
            );
        }
        assert_eq!(
            plan.retained_for_slots(NonZeroUsize::MAX),
            Err(CurveError::SizeOverflow)
        );
        for workers in [1, 3, 4] {
            let arena = Arena::new(plan);
            let work = [RwLock::new(Work::new(core::iter::once(plan.temporary())))];
            let mut identity = Identity::new();
            let mut slots = [const { TaskStorage::EMPTY }; 3];
            let mut run = MsmRun::new(
                plan,
                Input::new(Bases::Affine(&bases), &scalars),
                &mut identity,
                &mut slots,
            );
            assert!(arena.bytes() + work[0].read().bytes() < 4 * 1024 * 1024);
            run_pool::scoped(workers, 3, |pool| {
                let mut ready = [None; 3];
                while run.result().is_none() {
                    let count = run.ready(&mut ready);
                    for request in ready[..count].iter().flatten() {
                        if !pool.available() {
                            break;
                        }
                        if let Some(task) = run
                            .try_claim(*request, || arena.acquire(*request, &work))
                            .unwrap()
                        {
                            assert!(pool.submit(task).is_ok());
                        }
                    }
                    let completed = run
                        .complete(pool.receive().expect("admitted MSM must make progress"))
                        .unwrap();
                    assert_eq!(completed.error, None);
                    assert!(!run.is_failed());
                    drop(completed);
                }
            });
            assert_eq!(run.result(), Some(expected));
            let leases = NonZeroUsize::new(workers).unwrap();
            let required = plan.requirements_with(leases);
            let executing = workers.min(plan.output_slots()).min(32);
            assert_eq!(
                counts(required),
                core::array::from_fn(|i| retained[i] + executing * temporary[i]),
            );
            assert_eq!(plan.grain(), 256);
            let result = plan.execute_with(
                Input::new(Bases::Affine(&bases), &scalars),
                leases,
                &SerialExecutor,
                Scratch::new(
                    &mut vec![ScalarStorage::ZERO; required.scalars()],
                    &mut vec![0; required.digits()],
                    &mut vec![AffinePoint::GENERATOR; required.affine()],
                    &mut vec![ProjectivePoint::IDENTITY; required.projective()],
                    &mut vec![PastaField::ZERO; required.field()],
                    &mut vec![0; required.indices()],
                ),
            );
            assert_eq!(result, expected);
        }
    }
}

#[test]
fn bounded_windows_streaming_and_partial_reductions_match_ladder() {
    check::<Pallas>();
    check::<Vesta>();
}

fn ladder<C: PastaCurve>(scalar: PastaField<C::Scalar>) -> ProjectivePoint<C> {
    let mut result = ProjectivePoint::IDENTITY;
    for byte in scalar.to_bytes().iter().rev() {
        for bit in (0..8).rev() {
            result = result.double();
            if byte & (1 << bit) != 0 {
                result = result.add(&ProjectivePoint::GENERATOR);
            }
        }
    }
    result
}

fn counts(required: Requirements) -> [usize; 6] {
    [
        required.scalars(),
        required.digits(),
        required.affine(),
        required.projective(),
        required.field(),
        required.indices(),
    ]
}

fn batch_limits<C: PastaCurve>() {
    let bases = [AffinePoint::<C>::GENERATOR; 257];
    let scalars: Vec<_> = (2..259)
        .map(|i| PastaField::<C::Scalar>::from_u64(i).invert().unwrap())
        .collect();
    let expected = ladder::<C>(scalars.iter().fold(PastaField::ZERO, |sum, s| sum.add(s)));
    let input = Input::new(Bases::Affine(&bases), &scalars);
    let empty = Input::new(Bases::Affine(&[]), &[]);
    let inputs = [input, empty, empty];
    for width in [None, Some(4), Some(7)] {
        for accumulation in [
            Accumulation::Projective,
            Accumulation::Affine,
            Accumulation::Hybrid,
        ] {
            let arithmetic = ArithmeticOptions::DEFAULT
                .with_algorithm(Algorithm::Booth {
                    width,
                    accumulation,
                })
                .unwrap()
                .with_max_terms_per_pass(NonZeroUsize::new(17));
            // One term and one task leave no smaller layout for these explicit
            // compatible choices. Compare adaptation with that forced plan.
            let floor = {
                let mut jobs = [JobStorage::EMPTY; 3];
                let mut workers = [WorkerStorage::EMPTY; 1];
                BatchPlan::new_with(
                    &inputs,
                    BatchOptions::new(
                        arithmetic
                            .with_algorithm(Algorithm::Booth {
                                width: Some(width.unwrap_or(4)),
                                accumulation,
                            })
                            .unwrap()
                            .with_chunk_size(NonZeroUsize::MIN),
                    ),
                    &mut jobs,
                    &mut workers,
                )
                .unwrap()
                .requirements()
            };
            let options =
                BatchOptions::new(arithmetic).with_task_budget(TaskBudget::new(3).unwrap());
            assert_eq!(options.arithmetic(), arithmetic);
            assert_eq!(options.task_budget().get(), 3);
            assert_eq!(options.memory_limit(), None);
            let (j, w) = BatchPlan::<C>::storage_len_with(inputs.len(), options).unwrap();
            assert_eq!((j, w), (3, 3));
            let minimum = floor.bytes::<C>().unwrap();
            let mut jobs = vec![JobStorage::EMPTY; j + 1];
            let mut workers = vec![WorkerStorage::EMPTY; w + 1];
            assert_eq!(
                BatchPlan::new_with(
                    &inputs,
                    options.with_memory_limit(minimum - 1),
                    &mut jobs,
                    &mut workers,
                )
                .err(),
                Some(CurveError::MemoryLimit {
                    limit: minimum - 1,
                    required: minimum
                }),
            );
            assert!(jobs.iter().all(|j| *j == JobStorage::EMPTY));
            assert!(workers.iter().all(|w| *w == WorkerStorage::EMPTY));
            {
                let plan = BatchPlan::new_with(
                    &inputs,
                    options.with_memory_limit(minimum),
                    &mut jobs,
                    &mut workers,
                )
                .unwrap();
                assert_eq!(plan.requirements(), floor);
                // Metadata capacity is separate from arithmetic workspace.
                assert_eq!(plan.worker_ranges(), 1);
                assert_eq!(plan.temporary_bytes(), minimum);
                let r = plan.requirements();
                let mut records = vec![ScalarStorage::ZERO; r.scalars() + 1];
                let mut digits = vec![u8::MAX; r.digits() + 1];
                let mut affine = vec![AffinePoint::GENERATOR; r.affine() + 1];
                let mut projective = vec![ProjectivePoint::GENERATOR; r.projective() + 1];
                let mut field = vec![PastaField::ONE; r.field() + 1];
                let mut indices = vec![usize::MAX; r.indices() + 1];
                let mut output = [ProjectivePoint::GENERATOR; 3];
                plan.execute(
                    &mut output,
                    &SerialExecutor,
                    Scratch::new(
                        &mut records,
                        &mut digits,
                        &mut affine,
                        &mut projective,
                        &mut field,
                        &mut indices,
                    ),
                );
                assert_eq!(
                    output,
                    [
                        expected,
                        ProjectivePoint::IDENTITY,
                        ProjectivePoint::IDENTITY
                    ]
                );
                assert!(records[r.scalars()] == ScalarStorage::ZERO);
                assert_eq!(digits[r.digits()], u8::MAX);
                assert_eq!(affine[r.affine()], AffinePoint::GENERATOR);
                assert_eq!(projective[r.projective()], ProjectivePoint::GENERATOR);
                assert_eq!((field[r.field()]).reduce(), (PastaField::<_>::ONE).reduce());
                assert_eq!(indices[r.indices()], usize::MAX);
            }
            assert_eq!(jobs[j], JobStorage::EMPTY);
            assert_eq!(workers[w], WorkerStorage::EMPTY);
        }
    }

    // Retained preparation and digit caches belong to their owner, outside the
    // batch ceiling, even when they are larger than the execution provision.
    let arithmetic = ArithmeticOptions::DEFAULT
        .with_algorithm(Algorithm::Booth {
            width: Some(7),
            accumulation: Accumulation::Projective,
        })
        .unwrap();
    let mut records = vec![ScalarStorage::ZERO; scalars.len()];
    let prepared =
        PreparedScalars::prepare(&scalars, &mut records, TaskBudget::SERIAL, &SerialExecutor);
    let mut digits = vec![0; prepared.cache_len_with(arithmetic).unwrap()];
    let cached = prepared.cache_with(arithmetic, &mut digits).unwrap();
    let inputs = [Selection::new(Bases::Affine(&bases)).with_prepared_scalars(cached)];
    let mut jobs = [JobStorage::EMPTY];
    let mut workers = [WorkerStorage::EMPTY];
    let options = BatchOptions::new(arithmetic);
    let bytes = BatchPlan::new_with(&inputs, options, &mut jobs, &mut workers)
        .unwrap()
        .temporary_bytes();
    assert!(cached.retained_bytes() > bytes);
    let plan = BatchPlan::new_with(
        &inputs,
        options.with_memory_limit(bytes),
        &mut jobs,
        &mut workers,
    )
    .unwrap();
    let r = plan.requirements();
    assert_eq!((r.scalars(), r.digits()), (0, 0));
    assert_eq!(bytes, r.bytes::<C>().unwrap());
    let mut output = [ProjectivePoint::IDENTITY];
    plan.execute(
        &mut output,
        &SerialExecutor,
        Scratch::new(
            &mut [],
            &mut [],
            &mut vec![AffinePoint::GENERATOR; r.affine()],
            &mut vec![ProjectivePoint::IDENTITY; r.projective()],
            &mut vec![PastaField::ZERO; r.field()],
            &mut vec![0; r.indices()],
        ),
    );
    assert_eq!(output, [expected]);
}

#[test]
fn batch_limits_exclude_metadata_and_preserve_private_booth_choices() {
    batch_limits::<Pallas>();
    batch_limits::<Vesta>();
    let plan = BatchPlan::<Pallas>::new_with(
        &[],
        BatchOptions::default().with_memory_limit(0),
        &mut [],
        &mut [],
    )
    .unwrap();
    assert_eq!(plan.requirements(), Requirements::default());
    assert_eq!(plan.temporary_bytes(), 0);
}

#[test]
fn run_binding_enforces_plan_and_storage_contracts() {
    let bases = [AffinePoint::<Pallas>::GENERATOR; 2];
    let scalars = [PastaField::ONE; 2];
    let input = Input::new(Bases::Affine(&bases), &scalars);
    let short = Input::new(Bases::Affine(&bases[..1]), &scalars[..1]);
    let produced = ProducedInput::dense(Bases::Affine(&bases));
    let short_produced = ProducedInput::dense(Bases::Affine(&bases[..1]));
    let plan = MsmPlan::new_with(2, ArithmeticOptions::DEFAULT, NonZeroUsize::MIN).unwrap();
    let mut identity = Identity::new();
    let mut storage = [const { TaskStorage::EMPTY }; 1];
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = MsmRun::new(plan, short, &mut identity, &mut storage);
        }))
        .is_err()
    );
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = MsmRun::new_produced(plan, short_produced, &mut identity, &mut storage);
        }))
        .is_err()
    );
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = MsmRun::new_partition(plan, short, 0..1, &mut identity, &mut storage);
        }))
        .is_err()
    );
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = MsmRun::new_produced_partition(
                plan,
                short_produced,
                0..1,
                &mut identity,
                &mut storage,
            );
        }))
        .is_err()
    );
    for (start, end) in [(2, 1), (0, 3)] {
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _ = MsmRun::new_partition(plan, input, start..end, &mut identity, &mut storage);
            }))
            .is_err()
        );
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _ = MsmRun::new_produced_partition(
                    plan,
                    produced,
                    start..end,
                    &mut identity,
                    &mut storage,
                );
            }))
            .is_err()
        );
    }
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = MsmRun::new(plan, input, &mut identity, &mut []);
        }))
        .is_err()
    );
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = MsmRun::new_produced_partition(plan, produced, 0..1, &mut identity, &mut []);
        }))
        .is_err()
    );
    let mut run = MsmRun::new_partition(plan, input, 0..0, &mut identity, &mut storage);
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = run.rebind(plan, short);
        }))
        .is_err()
    );
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = run.rebind_produced(plan, short_produced);
        }))
        .is_err()
    );
    for (start, end) in [(2, 1), (0, 3)] {
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _ = run.rebind_produced_partition(plan, produced, start..end);
            }))
            .is_err()
        );
    }
    assert_eq!(run.result(), Some(ProjectivePoint::IDENTITY));
    run.rebind(plan, input).unwrap();
    assert_eq!(run.rebind(plan, input), Err(TaskError::Busy));

    let mut identities = [Identity::new()];
    let mut storage = [[const { TaskStorage::EMPTY }; 1]];
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = ParallelMsmRun::new(plan, short, &mut identities, &mut storage);
        }))
        .is_err()
    );
    let streaming = MsmPlan::new_with(
        2,
        ArithmeticOptions::DEFAULT
            .with_algorithm(Algorithm::StreamingBooth { width: None })
            .unwrap(),
        NonZeroUsize::MIN,
    )
    .unwrap();
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = ParallelMsmRun::new(streaming, input, &mut identities, &mut storage);
        }))
        .is_err()
    );
    let empty = Input::new(Bases::Affine(&[]), &[]);
    let empty_plan = MsmPlan::new_with(0, ArithmeticOptions::DEFAULT, NonZeroUsize::MIN).unwrap();
    let mut run = ParallelMsmRun::new(empty_plan, empty, &mut identities, &mut storage).unwrap();
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = run.rebind(plan, short);
        }))
        .is_err()
    );
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = run.rebind(streaming, input);
        }))
        .is_err()
    );
    assert_eq!(run.result(), Some(ProjectivePoint::IDENTITY));
    run.rebind(plan, input).unwrap();
    assert_eq!(run.rebind(plan, input), Err(TaskError::Busy));

    let error: &dyn core::error::Error = &TaskError::Storage;
    assert!(error.to_string().contains("workspace ceiling"));
    assert!(error.source().is_none());
}

fn chunks<C: PastaCurve>(
    input: Input<'_, C>,
    expected: ProjectivePoint<C>,
    options: ArithmeticOptions,
    grain: usize,
    prepared: bool,
    cached: bool,
    skew: bool,
) {
    let plan = MsmPlan::new_with(input.len(), options, NonZeroUsize::new(grain).unwrap()).unwrap();
    let arenas: [_; 3] = core::array::from_fn(|_| Arena::new(plan));
    let work = [RwLock::new(Work::new(core::iter::once(plan.temporary())))];
    let mut identities = core::array::from_fn(|_| Identity::new());
    let mut slots = [const { [const { TaskStorage::EMPTY }; 3] }; 3];
    let mut run = ParallelMsmRun::new(plan, input, &mut identities, &mut slots).unwrap();
    run_pool::scoped(4, 3, |pool| {
        for repetition in 0..2 {
            if repetition > 0 {
                run.rebind(plan, input).unwrap();
            }
            let mut ready = [None; 32];
            let mut held = None;
            let mut delayed = false;
            while run.result().is_none() {
                let count = run.ready(&mut ready);
                for request in ready[..count].iter().flatten() {
                    if !pool.available() {
                        break;
                    }
                    if prepared {
                        assert_eq!(
                            request.task.scratch.scalars() + request.task.read_scalars,
                            0
                        );
                    }
                    if cached {
                        assert_eq!(request.task.scratch.digits() + request.task.read_digits, 0);
                    }
                    if let Some(task) = run
                        .try_claim(*request, || {
                            arenas[request.slot].acquire(request.task, &work)
                        })
                        .unwrap()
                    {
                        if skew
                            && !delayed
                            && request.slot == 0
                            && request.task.kind == WorkKind::Prepare
                        {
                            held = Some(task);
                            delayed = true;
                        } else {
                            assert!(pool.submit((request.slot, task)).is_ok());
                        }
                    }
                }
                if let Some((slot, receipt)) = pool.receive() {
                    let completed = run.complete(slot, receipt).unwrap();
                    assert_eq!(completed.error, None);
                    drop(completed);
                } else {
                    // All later chunks finished while the first preparation
                    // was suspended. Their retained results cannot consume its
                    // reserved slot or trigger unbounded successor production.
                    let mut task = held.take().expect("admitted chunks must make progress");
                    assert_eq!(run.inflight(), 1);
                    assert_eq!(run.ready(&mut ready), 0);
                    task.execute().unwrap();
                    drop(run.complete(0, task.finish()).unwrap());
                }
                assert!(!run.is_failed());
            }
            assert_eq!(run.result(), Some(expected));
            assert_eq!(run.inflight(), 0);
        }
    });
}

fn representations<C: PastaCurve>() {
    let bases: Vec<_> = (1..=19)
        .map(|i| {
            *ladder::<C>(PastaField::from_u64(i))
                .to_point()
                .as_affine()
                .unwrap()
        })
        .collect();
    let prepared_bases: Vec<_> = bases.iter().map(PreparedAffinePoint::from_affine).collect();
    let points: Vec<_> = bases
        .iter()
        .enumerate()
        .map(|(i, p)| {
            if i % 7 == 0 {
                Point::IDENTITY
            } else {
                p.to_projective().to_point()
            }
        })
        .collect();
    let r = EisensteinTableBatch::<C>::requirements(bases.len()).unwrap();
    let mut entries = vec![AffinePoint::GENERATOR; r.table_entries];
    let mut cached_entries =
        vec![PreparedAffinePoint::from_affine(&AffinePoint::GENERATOR); r.table_entries];
    let compact = EisensteinTableBatch::prepare(
        &bases,
        &mut entries,
        &mut vec![ProjectivePoint::IDENTITY; r.projective_scratch],
        &mut vec![PastaField::ZERO; r.field_scratch],
        TaskBudget::SERIAL,
        &SerialExecutor,
    );
    let compact_cached = EisensteinTableBatch::prepare(
        &bases,
        &mut cached_entries,
        &mut vec![ProjectivePoint::IDENTITY; r.projective_scratch],
        &mut vec![PastaField::ZERO; r.field_scratch],
        TaskBudget::SERIAL,
        &SerialExecutor,
    );
    let indices: Vec<_> = (0..59).map(|i| (i * 7 % bases.len()) as u32).collect();
    for source in [
        Bases::Affine(&bases),
        Bases::Prepared(&prepared_bases),
        Bases::Points(&points),
        Bases::Compact(compact),
        Bases::CompactPrepared(compact_cached),
    ] {
        for indexed in [false, true] {
            let selection = if indexed {
                Selection::indexed(source, &indices).unwrap()
            } else {
                Selection::new(source)
            };
            let scalars: Vec<_> = (0..selection.len())
                .map(|i| {
                    PastaField::<C::Scalar>::from_u64(i as u64 + 2)
                        .invert()
                        .unwrap()
                })
                .collect();
            let unsigned: Vec<_> = (0..selection.len())
                .map(|i| [0, 1, u128::MAX, 1 << 127, i as u128][i % 5])
                .collect();
            let signed: Vec<_> = (0..selection.len())
                .map(|i| [0, -1, i128::MIN, i128::MAX, i as i128][i % 5])
                .collect();
            let uint: Vec<_> = unsigned
                .iter()
                .map(|&i| CanonicalUint::from_limbs([i as u64, (i >> 64) as u64, 0, 0]))
                .collect();
            let unsigned_fields: Vec<_> = uint
                .iter()
                .map(|&i| PastaField::<C::Scalar>::from_canonical_uint(i).unwrap())
                .collect();
            let signed_fields: Vec<_> =
                signed
                    .iter()
                    .map(|i| {
                        let i_abs = i.unsigned_abs();
                        let f = PastaField::<C::Scalar>::from_canonical_uint(
                            CanonicalUint::from_limbs([i_abs as u64, (i_abs >> 64) as u64, 0, 0]),
                        )
                        .unwrap();
                        if *i < 0 { f.neg() } else { f }
                    })
                    .collect();
            let expected = |scalars: &[PastaField<C::Scalar>]| {
                ladder::<C>(scalars.iter().enumerate().fold(
                    PastaField::ZERO,
                    |sum, (i, scalar)| {
                        let index = if indexed { indices[i] as usize } else { i };
                        let weight = if matches!(source, Bases::Points(_)) && index % 7 == 0 {
                            0
                        } else {
                            index + 1
                        };
                        sum.add(&scalar.mul(&PastaField::<_>::from_u64(weight as u64)))
                    },
                ))
            };
            let mut records = vec![ScalarStorage::ZERO; selection.len()];
            let prepared = PreparedScalars::prepare(
                &scalars,
                &mut records,
                TaskBudget::SERIAL,
                &SerialExecutor,
            );
            let mut digits = vec![0; prepared.cache_len_with(ArithmeticOptions::DEFAULT).unwrap()];
            let cached = prepared
                .cache_with(ArithmeticOptions::DEFAULT, &mut digits)
                .unwrap();
            for (input, answer, retained) in [
                (selection.with_scalars(&scalars), expected(&scalars), false),
                (
                    selection.with_unsigned(&unsigned),
                    expected(&unsigned_fields),
                    false,
                ),
                (
                    selection.with_signed(&signed),
                    expected(&signed_fields),
                    false,
                ),
                (
                    selection.with_canonical(&uint, 128).unwrap(),
                    expected(&unsigned_fields),
                    false,
                ),
                (
                    selection.with_prepared_scalars(prepared),
                    expected(&scalars),
                    true,
                ),
                (
                    selection.with_prepared_scalars(cached),
                    expected(&scalars),
                    true,
                ),
            ] {
                chunks(
                    input,
                    answer,
                    ArithmeticOptions::DEFAULT,
                    8,
                    retained,
                    false,
                    true,
                );
            }
            chunks(
                selection.with_prepared_scalars(cached),
                expected(&scalars),
                ArithmeticOptions::DEFAULT,
                64,
                true,
                true,
                false,
            );
        }
    }
}

#[test]
fn independent_chunks_reuse_all_scalar_and_base_representations() {
    representations::<Pallas>();
    representations::<Vesta>();
}

#[test]
fn independent_booth_chunks_and_empty_runs() {
    let bases = [AffinePoint::<Pallas>::GENERATOR; 385];
    let scalars: Vec<_> = (0..bases.len())
        .map(|i| PastaField::<_>::from_u64(i as u64 + 2).invert().unwrap())
        .collect();
    let expected = ladder::<Pallas>(scalars.iter().fold(PastaField::ZERO, |sum, s| sum.add(s)));
    for width in 4..=12 {
        let options = ArithmeticOptions::DEFAULT
            .with_algorithm(Algorithm::Booth {
                width: Some(width),
                accumulation: Accumulation::Auto,
            })
            .unwrap();
        chunks(
            Input::new(Bases::Affine(&bases), &scalars),
            expected,
            options,
            128,
            false,
            false,
            true,
        );
        let empty = Input::new(Bases::Affine(&bases[..0]), &scalars[..0]);
        let plan =
            MsmPlan::<Pallas>::new_with(0, options, NonZeroUsize::new(128).unwrap()).unwrap();
        assert_eq!(plan.retained().bytes::<Pallas>().unwrap(), 0);
        assert_eq!(plan.temporary().bytes::<Pallas>().unwrap(), 0);
        assert_eq!(
            plan.retained_for_slots(NonZeroUsize::MAX).unwrap(),
            Requirements::default()
        );
        assert_eq!(
            plan.requirements_with(NonZeroUsize::MAX),
            Requirements::default()
        );
        chunks(
            empty,
            ProjectivePoint::IDENTITY,
            options,
            128,
            false,
            false,
            false,
        );
    }
    assert!(matches!(
        MsmPlan::<Pallas>::new_with(usize::MAX, ArithmeticOptions::DEFAULT, NonZeroUsize::MAX),
        Err(CurveError::SizeOverflow)
    ));
}

#[test]
fn kernel_selection_validates_widths_and_replaces_all_preferences() {
    const JOINT: ArithmeticOptions =
        match ArithmeticOptions::DEFAULT.with_algorithm(Algorithm::Joint) {
            Ok(options) => options,
            Err(_) => panic!("valid kernel"),
        };
    for width in [0, 3, 13, u32::MAX] {
        for kernel in [
            Algorithm::Booth {
                width: Some(width),
                accumulation: Accumulation::Auto,
            },
            Algorithm::StreamingBooth { width: Some(width) },
        ] {
            assert_eq!(
                JOINT.with_algorithm(kernel),
                Err(InvalidWindow { bits: width })
            );
        }
    }
    for width in 4..=12 {
        let booth = JOINT
            .with_algorithm(Algorithm::Booth {
                width: Some(width),
                accumulation: Accumulation::Hybrid,
            })
            .unwrap();
        let streaming = booth
            .with_algorithm(Algorithm::StreamingBooth { width: Some(width) })
            .unwrap();
        assert_eq!(streaming.with_algorithm(Algorithm::Joint).unwrap(), JOINT);
        assert_eq!(
            streaming.with_algorithm(Algorithm::Auto).unwrap(),
            ArithmeticOptions::DEFAULT
        );
        let empty = MsmPlan::<Pallas>::new_with(0, streaming, NonZeroUsize::MIN).unwrap();
        let mut identity = Identity::new();
        let mut slots = [const { TaskStorage::EMPTY }; 1];
        let run = MsmRun::new(
            empty,
            Input::new(Bases::Affine(&[]), &[]),
            &mut identity,
            &mut slots,
        );
        assert_eq!(run.result(), Some(ProjectivePoint::IDENTITY));
    }
}

fn small_kernel_dispatch<C: PastaCurve>() {
    let bases = [AffinePoint::<C>::GENERATOR; 3];
    let scalars = [PastaField::ONE; 3];
    let expected = ladder::<C>(PastaField::from_u64(3));
    let selection = Selection::new(Bases::Affine(&bases));
    let mut records = [ScalarStorage::ZERO; 3];
    let prepared =
        PreparedScalars::prepare(&scalars, &mut records, TaskBudget::SERIAL, &SerialExecutor);
    for kernel in [
        Algorithm::Auto,
        Algorithm::Joint,
        Algorithm::Booth {
            width: None,
            accumulation: Accumulation::Affine,
        },
        Algorithm::Booth {
            width: Some(4),
            accumulation: Accumulation::Projective,
        },
        Algorithm::Booth {
            width: Some(7),
            accumulation: Accumulation::Hybrid,
        },
        Algorithm::StreamingBooth { width: None },
        Algorithm::StreamingBooth { width: Some(4) },
    ] {
        let options = ArithmeticOptions::DEFAULT.with_algorithm(kernel).unwrap();
        let original = MsmPlan::<C>::new_with(3, options, NonZeroUsize::new(7).unwrap()).unwrap();
        let plan = original.with_grain(NonZeroUsize::MIN).unwrap();
        assert_eq!(plan.output_slots(), original.output_slots());
        assert!(
            counts(plan.temporary())
                .iter()
                .zip(counts(original.temporary()))
                .all(|(a, b)| *a <= b)
        );
        let mut digits = vec![0; prepared.cache_len_with(options).unwrap()];
        let cached = prepared.cache_with(options, &mut digits).unwrap();
        let arena = Arena::new(plan);
        let work = [RwLock::new(Work::new(core::iter::once(plan.temporary())))];
        let mut identity = Identity::new();
        let mut slots = [const { TaskStorage::EMPTY }; 3];
        let raw = selection.with_scalars(&scalars);
        let mut run = MsmRun::new(plan, raw, &mut identity, &mut slots);
        for (source, input) in [
            raw,
            selection.with_prepared_scalars(prepared),
            selection.with_prepared_scalars(cached),
        ]
        .into_iter()
        .enumerate()
        {
            // Rebinding keeps the same requirements even when scalar shape and
            // cache availability become known at different times.
            if run.result().is_some() {
                run.rebind(plan, input).unwrap();
            }
            let mut windows = 0;
            let mut collapses = 0;
            while run.result().is_none() {
                let mut ready = [None; 3];
                let count = run.ready(&mut ready);
                assert!(count > 0);
                for request in ready[..count].iter().flatten() {
                    if request.kind == WorkKind::Window {
                        windows += 1;
                        match kernel {
                            Algorithm::Booth {
                                accumulation: Accumulation::Projective,
                                ..
                            } => {
                                assert_eq!(request.scratch.affine(), 0);
                                assert_eq!(request.scratch.field(), 0);
                                assert!(request.scratch.projective() >= 8);
                            }
                            Algorithm::Booth {
                                accumulation: Accumulation::Affine | Accumulation::Hybrid,
                                ..
                            } => {
                                assert!(request.scratch.affine() > 0);
                                assert!(request.scratch.field() > 0);
                            }
                            Algorithm::StreamingBooth { .. } => assert!(request.buckets > 0),
                            _ => {}
                        }
                    }
                    collapses += usize::from(request.kind == WorkKind::Collapse);
                    let mut task = run
                        .try_claim(*request, || arena.acquire(*request, &work))
                        .unwrap()
                        .unwrap();
                    task.execute().unwrap();
                    assert_eq!(run.complete(task.finish()).unwrap().error, None);
                }
            }
            assert_eq!(run.result(), Some(expected));
            assert_eq!(
                windows,
                3 * if kernel == Algorithm::Auto {
                    1
                } else {
                    plan.output_slots()
                }
            );
            assert_eq!(
                collapses,
                if matches!(kernel, Algorithm::StreamingBooth { .. }) {
                    plan.output_slots()
                } else {
                    0
                }
            );
            // Batch dispatch on the same short prepared input must retain the
            // requested family too: Booth needs digits, Joint does not.
            let inputs = [input];
            let mut jobs = [JobStorage::EMPTY];
            let mut workers = [WorkerStorage::EMPTY];
            let batch =
                BatchPlan::new_with(&inputs, BatchOptions::new(options), &mut jobs, &mut workers)
                    .unwrap();
            let r = batch.requirements();
            if matches!(
                kernel,
                Algorithm::Booth { .. } | Algorithm::StreamingBooth { .. }
            ) {
                assert!(r.projective() > 0);
                if source == 0 {
                    assert!(r.digits() > 0);
                }
            }
            let mut output = [ProjectivePoint::IDENTITY];
            batch.execute(
                &mut output,
                &SerialExecutor,
                Scratch::new(
                    &mut vec![ScalarStorage::ZERO; r.scalars()],
                    &mut vec![0; r.digits()],
                    &mut vec![AffinePoint::GENERATOR; r.affine()],
                    &mut vec![ProjectivePoint::IDENTITY; r.projective()],
                    &mut vec![PastaField::ZERO; r.field()],
                    &mut vec![0; r.indices()],
                ),
            );
            assert_eq!(output, [expected]);
        }
    }
}

#[test]
fn explicit_kernels_dispatch_on_short_raw_prepared_and_cached_inputs() {
    small_kernel_dispatch::<Pallas>();
    small_kernel_dispatch::<Vesta>();
}
