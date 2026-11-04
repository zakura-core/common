use super::*;
use crate::native::commitment::CompactGenerators;
use crate::resource_tests::PoolExecutor;
use udon::{
    curve::{PreparedAffinePoint, Vesta, VestaAffine, VestaProjective},
    exec::SerialExecutor,
    field::{Fp, Fq},
    msm::{Bases, PreparedScalars},
};

fn coefficients(len: usize) -> Vec<Fp> {
    let mut next = <Fp>::from_u64(17).invert().unwrap();
    (0..len)
        .map(|i| {
            next = next.square().add(&<Fp>::from_u64(i as u64));
            match i % 7 {
                0 => <Fp>::ZERO,
                1 => <Fp>::ONE,
                2 => <Fp>::from_u64(i as u64).neg(),
                _ => next,
            }
        })
        .collect()
}

#[test]
fn mixed_inputs_reuse_scratch_across_pools_and_chunks() {
    let len = 8192 + 13;
    let scalars = coefficients(len);
    let generators = [VestaAffine::GENERATOR, VestaAffine::GENERATOR.neg()];
    let prepared_bases = generators.map(|p| PreparedAffinePoint::from_affine(&p));
    let compact = CompactGenerators::new(&prepared_bases);
    let indices = (0..len)
        .map(|i| ((i * 13 + i / 3) % 2) as u32)
        .collect::<Vec<_>>();
    let dense = indices
        .iter()
        .map(|&i| generators[i as usize])
        .collect::<Vec<_>>();
    let mut records = vec![ScalarStorage::<Vesta>::ZERO; len];
    let prepared =
        PreparedScalars::prepare(&scalars, &mut records, TaskBudget::SERIAL, &SerialExecutor);
    let mut cache_records = vec![ScalarStorage::<Vesta>::ZERO; 4096];
    let cache_prepared = PreparedScalars::prepare(
        &scalars[..4096],
        &mut cache_records,
        TaskBudget::SERIAL,
        &SerialExecutor,
    );
    let cache_input = Input::new_prepared(Bases::Affine(&dense[..4096]), cache_prepared);
    let cache_plan = MsmPlan::for_input(
        &cache_input,
        ExecutionOptions::default().with_task_budget(TaskBudget::new(16).unwrap()),
    )
    .unwrap();
    let mut digits = vec![0; cache_prepared.cache_len(&cache_plan)];
    assert!(!digits.is_empty());
    let cached = cache_prepared.cache(
        &cache_plan,
        &mut digits,
        TaskBudget::SERIAL,
        &SerialExecutor,
    );
    let inputs = [
        Input::new(Bases::Affine(&dense[..0]), &scalars[..0]),
        Input::new(Bases::Affine(&dense[..1]), &scalars[..1]),
        Input::new(Bases::Affine(&dense[..31]), &scalars[..31]),
        Input::indexed(
            Bases::Prepared(&prepared_bases),
            &indices[..128],
            &scalars[..128],
        )
        .unwrap(),
        Input::indexed(Bases::Affine(&generators), &indices[..257], &scalars[..257]).unwrap(),
        Input::new(Bases::Affine(&dense[..1024]), &scalars[..1024]),
        Input::new(Bases::Affine(&dense[..2049]), &scalars[..2049]),
        Input::new(Bases::Affine(&dense), &scalars),
        Input::new_prepared(Bases::Affine(&dense), prepared),
        Input::new_prepared(Bases::Affine(&dense[..4096]), cached),
        Input::indexed(compact.bases(), &indices[..128], &scalars[..128]).unwrap(),
    ];
    let expected = inputs.map(|input| {
        let sum = scalars
            .iter()
            .zip(&indices)
            .take(input.len())
            .fold(<Fp>::ZERO, |sum, (&scalar, &index)| {
                sum.add(&if index == 0 { scalar } else { scalar.neg() })
            });
        VestaAffine::GENERATOR.mul_projective(&sum)
    });
    let mut workspace = MsmWorkspace::new();
    for workers in [1, 2, 4] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .build()
            .unwrap();
        let executor = PoolExecutor(&pool);
        // The provision is deliberately independent of the number of threads.
        // Nested execution on a one-thread pool must still drain every run.
        let budget = TaskBudget::new(if workers == 4 { usize::MAX } else { 16 }).unwrap();
        for iteration in 0..3 {
            let before = workspace.capacities();
            for retained in &mut workspace.retained {
                for record in &mut retained.records {
                    let records = Arc::get_mut(record.as_mut().unwrap()).unwrap();
                    records.scalars.0.fill(ScalarStorage::ZERO);
                    records.digits.0.fill(255);
                }
                retained
                    .partials
                    .fill(VestaAffine::GENERATOR.to_projective());
            }
            for work in &mut workspace.work {
                work.affine.fill(generators[1]);
                work.projective.fill(generators[1].to_projective());
                work.field.fill(<Fq>::ONE);
                work.indices.fill(usize::MAX);
            }
            let mut output = [VestaProjective::IDENTITY; 11];
            pool.install(|| {
                workspace
                    .prepare(&inputs, budget)
                    .unwrap()
                    .execute(&mut output, &executor)
            })
            .unwrap();
            assert_eq!(output, expected);
            if iteration > 0 {
                assert_eq!(workspace.capacities(), before);
            }
        }
    }
}

#[test]
fn produced_fragments_preserve_retained_buckets_across_pool_tasks_and_reuse() {
    let scalars = coefficients(4096);
    let generators = [VestaAffine::GENERATOR, VestaAffine::GENERATOR.neg()];
    let indices = (0..scalars.len())
        .map(|i| (i % 2) as u32)
        .collect::<Vec<_>>();
    let dense = indices
        .iter()
        .map(|&i| generators[i as usize])
        .collect::<Vec<_>>();
    let compact = CompactGenerators::new(
        &dense
            .iter()
            .map(PreparedAffinePoint::from_affine)
            .collect::<Vec<_>>(),
    );
    let compact_indexed =
        CompactGenerators::new(&generators.map(|p| PreparedAffinePoint::from_affine(&p)));
    let inputs = [
        ProducedInput::dense(Bases::Affine(&dense)),
        ProducedInput::indexed(Bases::Affine(&generators), scalars.len()),
        ProducedInput::dense(compact.bases()),
        ProducedInput::indexed(compact_indexed.bases(), scalars.len()),
    ];
    let expected = VestaAffine::GENERATOR.mul_projective(
        &scalars
            .iter()
            .zip(&indices)
            .fold(<Fp>::ZERO, |sum, (&scalar, &index)| {
                sum.add(&if index == 0 { scalar } else { scalar.neg() })
            }),
    );
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap();
    let executor = PoolExecutor(&pool);
    let budget = TaskBudget::new(8).unwrap();
    let mut workspace = MsmWorkspace::new();
    for _ in 0..2 {
        for retained in &mut workspace.retained {
            for buckets in &mut retained.buckets {
                buckets
                    .as_mut()
                    .unwrap()
                    .fill(VestaAffine::GENERATOR.to_projective());
            }
        }
        let mut batch = workspace.prepare_produced(&inputs, budget, 512).unwrap();
        let groups = batch.groups.to_vec();
        let mut coordinator = batch.coordinator();
        assert!(coordinator.claim().is_none());
        for first in (0..scalars.len()).step_by(512) {
            let range = first..first + 512;
            let values = Arc::new(Raw {
                scalars: scalars[range.clone()].to_vec().into(),
                indices: SourceIndices::Owned(indices[range.clone()].to_vec().into()),
            });
            for source in &mut coordinator.sources {
                source.publish(range.clone(), Arc::clone(&values));
            }
            pool.install(|| run::drive(&mut coordinator, budget, &executor));
            assert!(!coordinator.failed());
            if range.end < scalars.len() {
                assert!(coordinator.results().is_none());
            }
        }
        let partials = coordinator.results().unwrap().collect::<Vec<_>>();
        for group in groups {
            assert_eq!(
                partials[group]
                    .iter()
                    .fold(VestaProjective::IDENTITY, |sum, point| sum.add(point)),
                expected,
            );
        }
    }
}

#[test]
fn failed_batch_drains_readers_and_preserves_outputs_before_reuse() {
    let scalars = coefficients(1024);
    let bases = vec![VestaAffine::GENERATOR; scalars.len()];
    let input = Input::new(Bases::Affine(&bases), &scalars);
    let inputs = [input; 3];
    let expected = VestaAffine::GENERATOR
        .mul_projective(&scalars.iter().copied().fold(<Fp>::ZERO, |a, b| a.add(&b)));
    let sentinel = VestaAffine::GENERATOR.to_projective();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap();
    let executor = PoolExecutor(&pool);
    let budget = TaskBudget::new(4).unwrap();
    let mut workspace = MsmWorkspace::new();
    let mut output = [sentinel; 3];
    let mut batch = workspace.prepare(&inputs, budget).unwrap();
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            batch.execute(&mut output[..2], &executor)
        }))
        .is_err()
    );
    for work in &mut *batch.work {
        work.affine.clear();
    }
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            batch.execute(&mut output, &executor)
        }))
        .is_err()
    );
    assert_eq!(output, [sentinel; 3]);
    for retained in &workspace.retained {
        for records in &retained.records {
            assert_eq!(Arc::strong_count(records.as_ref().unwrap()), 1);
        }
    }
    workspace
        .prepare(&inputs, budget)
        .unwrap()
        .execute(&mut output, &executor)
        .unwrap();
    assert_eq!(output, [expected; 3]);
}

#[test]
fn source_fragments_spill_and_release_all_readers() {
    let bases = [VestaAffine::GENERATOR; 16];
    let inputs = [ProducedInput::dense(Bases::Affine(&bases))];
    let mut workspace = MsmWorkspace::new();
    let mut batch = workspace
        .prepare_produced(&inputs, TaskBudget::SERIAL, 16)
        .unwrap();
    let mut coordinator = batch.coordinator();
    let mut ready = [None];
    assert_ne!(coordinator.runs[0].ready(&mut ready), 0);
    let mut request = ready[0].unwrap();
    request.offset = 1;
    request.source_scalars = 9;
    request.source_indices = 9;
    let values = (0..10)
        .map(|i| {
            Arc::new(Raw {
                scalars: vec![Fp::from_u64(i); 1].into(),
                indices: SourceIndices::Static(&[7]),
            })
        })
        .collect::<Vec<_>>();
    let row = &mut coordinator.sources[0];
    // Publication order need not match source order.
    for i in (0..8).rev() {
        row.publish(i..i + 1, Arc::clone(&values[i]));
    }
    assert_eq!(row.fragments.spill.capacity(), 0);
    assert!(row.acquire(request).is_none());
    for (i, value) in values.iter().enumerate().skip(8) {
        row.publish(i..i + 1, Arc::clone(value));
    }
    let reads = row.acquire(request).unwrap();
    assert_eq!(reads.fragments.spill.len(), 1);
    for i in 0..9 {
        assert_eq!(
            ReadView::<Fp>::get(&reads, i).unwrap().reduce(),
            <Fp>::from_u64(i as u64 + 1).reduce()
        );
        assert_eq!(ReadView::<u32>::get(&reads, i), Some(&7));
    }
    assert!(ReadView::<Fp>::contiguous(&reads, 0..9).is_none());
    assert_eq!(
        ReadView::<Fp>::contiguous_prefix(&reads, 0..9)
            .unwrap()
            .len(),
        1
    );
    assert!(ReadView::<Fp>::contiguous_prefix(&reads, 10..10).is_none());
    assert!(ReadView::<Fp>::contiguous_prefix(&reads, Range { start: 2, end: 1 }).is_none());
    row.clear();
    assert_eq!(Arc::strong_count(&values[0]), 1);
    assert_eq!(Arc::strong_count(&values[1]), 2);
    drop(reads);
    assert!(values.iter().all(|value| Arc::strong_count(value) == 1));
}

#[test]
fn borrowed_batches_have_no_producer_rows() {
    let scalars = [Fp::ONE; 1];
    let bases = [VestaAffine::GENERATOR; 1];
    let mut workspace = MsmWorkspace::new();
    let mut batch = workspace
        .prepare(
            &[Input::new(Bases::Affine(&bases), &scalars)],
            TaskBudget::SERIAL,
        )
        .unwrap();
    assert_eq!(batch.coordinator().sources.capacity(), 0);
}
