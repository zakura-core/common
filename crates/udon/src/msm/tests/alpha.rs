use super::*;
use crate::msm::execution::MsmPlan;

#[derive(Default)]
struct NoJoin(core::sync::atomic::AtomicUsize);
impl crate::exec::Executor for NoJoin {
    fn join<L, R, A, B>(&self, _: L, _: R) -> (A, B)
    where
        L: FnOnce() -> A + Send,
        R: FnOnce() -> B + Send,
        A: Send,
        B: Send,
    {
        self.0.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        panic!("unexpected executor work")
    }
}
impl NoJoin {
    fn check(&self) {
        assert_eq!(self.0.load(core::sync::atomic::Ordering::Relaxed), 0);
    }
}

fn differentials<C: PastaCurve>() {
    let affine: Vec<_> = (1..=41)
        .map(|i| {
            *AffinePoint::<C>::GENERATOR
                .mul_projective(&PastaField::from_u64(i))
                .to_point()
                .as_affine()
                .unwrap()
        })
        .collect();
    let scalars: Vec<_> = field_samples::<C::Scalar>().take(73).collect();
    for width in 5..=7 {
        let d = AlphaDescription::new(width).unwrap();
        let mut codes = vec![0; d.codes()];
        let mut coefficients = vec![AlphaCoefficient::ZERO; d.layers()];
        let mut scratch = vec![0; d.codebook_scratch()];
        let book = AlphaCodebook::prepare(d, &mut codes, &mut coefficients, &mut scratch);
        let r = d.requirements::<C, AffinePoint<C>>(affine.len()).unwrap();
        let mut entries = vec![AffinePoint::GENERATOR; r.table_entries];
        let mut projective = vec![ProjectivePoint::IDENTITY; r.projective_scratch];
        let mut field = vec![PastaField::ZERO; r.field_scratch];
        AlphaTable::prepare(
            book,
            &affine,
            &mut entries,
            &mut projective,
            &mut field,
            TaskBudget::new(3).unwrap(),
            &Pool,
        );
        let table = AlphaTable::bind(book, &entries);
        let prepared: Vec<_> = entries
            .iter()
            .map(PreparedAffinePoint::from_affine)
            .collect();
        // Thirty-three dense terms cross every width's parallel crossover.
        for bases in [
            Bases::Alpha(table.range(3..40).range(2..35)),
            Bases::AlphaPrepared(AlphaTable::bind(book, &prepared).range(4..37)),
        ] {
            for n in [0, 1, 17, 31, 73] {
                let ix: Vec<_> = (0..n).map(|i| (i * 13 % 31) as u32).collect();
                let input = Input::indexed(bases, &ix, &scalars[..n]).unwrap();
                let expected = reference(&input);
                for tasks in [1, 3] {
                    for cap in [1, 17, 73] {
                        let options = BatchOptions::new(
                            ArithmeticOptions::DEFAULT
                                .with_max_terms_per_pass(NonZeroUsize::new(cap)),
                        )
                        .with_task_budget(TaskBudget::new(tasks).unwrap());
                        let r = input.requirements_with(options).unwrap();
                        let mut buffers = Buffers::new(r);
                        assert_eq!(
                            input
                                .execute_with(options, &Pool, buffers.borrow())
                                .unwrap(),
                            expected,
                            "width={width} n={n} tasks={tasks} cap={cap}"
                        );
                        buffers.tails(r);
                    }
                }
            }
            let dense = Input::new(bases, &scalars[..bases.len()]);
            let expected = reference(&dense);
            let mut records = vec![ScalarStorage::ZERO; bases.len()];
            let prepared = PreparedScalars::prepare(
                &scalars[..bases.len()],
                &mut records,
                TaskBudget::SERIAL,
                &SerialExecutor,
            );
            let parallel = ExecutionOptions::DEFAULT.with_task_budget(TaskBudget::new(3).unwrap());
            let plan = MsmPlan::for_input(&Input::new_prepared(bases, prepared), parallel).unwrap();
            assert_ne!(prepared.alpha_cache_len(&plan), 0);
            let mut digits = vec![0xa5; prepared.alpha_cache_len(&plan) + 5];
            let cached =
                prepared.cache_alpha(&plan, book, &mut digits, TaskBudget::new(3).unwrap(), &Pool);
            for input in [
                dense,
                Input::new_prepared(bases, prepared),
                Input::new_prepared(bases, cached),
            ] {
                for accumulation in [
                    Accumulation::Affine,
                    Accumulation::Projective,
                    Accumulation::Hybrid,
                ] {
                    let options = BatchOptions::new(
                        ArithmeticOptions::DEFAULT
                            .with_algorithm(Algorithm::Alpha { accumulation })
                            .unwrap(),
                    )
                    .with_task_budget(TaskBudget::new(3).unwrap());
                    let r = input.requirements_with(options).unwrap();
                    let mut buffers = Buffers::new(r);
                    assert_eq!(
                        input
                            .execute_with(options, &Pool, buffers.borrow())
                            .unwrap(),
                        expected
                    );
                    buffers.tails(r);
                }
            }
            let input = Input::new_prepared(bases, cached);
            assert_eq!(input.requirements(parallel).unwrap().digits(), 0);
            // A serial automatic plan consults the width's own crossover and
            // consumes the cache only when it still selects the table.
            let serial = input.requirements(ExecutionOptions::default()).unwrap();
            assert_eq!(
                serial.digits() == 0,
                d.amortized(bases.len(), TaskBudget::SERIAL)
            );
            assert_eq!(&digits[digits.len() - 5..], &[0xa5; 5]);
            // Force full-width alpha affine passes; cancellation must empty a
            // bucket before a later term repopulates it.
            let k = PastaField::<C::Scalar>::from_u64(7).invert().unwrap();
            for ks in [&[k, k.neg()][..], &[k, k.neg(), PastaField::ZERO, k][..]] {
                let ix = vec![7; ks.len()];
                let input = Input::indexed(bases, &ix, ks).unwrap();
                let options = BatchOptions::new(
                    ArithmeticOptions::DEFAULT
                        .with_algorithm(Algorithm::Alpha {
                            accumulation: Accumulation::Affine,
                        })
                        .unwrap()
                        .with_max_terms_per_pass(NonZeroUsize::new(1)),
                );
                let r = input.requirements_with(options).unwrap();
                let mut buffers = Buffers::new(r);
                let (actual, calls) = super::super::test_support::count_kernels(|| {
                    input
                        .execute_with(options, &SerialExecutor, buffers.borrow())
                        .unwrap()
                });
                assert_eq!(actual, reference(&input));
                assert!(calls.for_geometry(recode::Geometry::Alpha(width)) > 0);
                buffers.tails(r);
            }

            // Four shared terms sit below every width's crossover and fold
            // over the original layer.
            let mut records = [ScalarStorage::ZERO; 4];
            let shared = PreparedScalars::prepare(
                &scalars[..4],
                &mut records,
                TaskBudget::SERIAL,
                &SerialExecutor,
            );
            for (output_stride, term_stride) in [(1, 6), (4, 1), (0, 0)] {
                let matrix =
                    SharedScalarInput::new(bases, shared, 5, output_stride, term_stride).unwrap();
                let options =
                    ExecutionOptions::default().with_task_budget(TaskBudget::new(3).unwrap());
                let r = matrix.requirements(options).unwrap();
                let mut buffers = Buffers::new(r);
                let mut output = [ProjectivePoint::IDENTITY; 5];
                matrix
                    .execute(&mut output, options, &Pool, buffers.borrow())
                    .unwrap();
                for (j, result) in output.into_iter().enumerate() {
                    let indices = core::array::from_fn::<_, 4, _>(|i| {
                        (j * output_stride + i * term_stride) as u32
                    });
                    assert_eq!(
                        result,
                        reference(&Input::indexed(bases, &indices, &scalars[..4]).unwrap())
                    );
                }
                buffers.tails(r);
            }
            // Enough shared terms to amortize the table under a parallel
            // allowance; the alpha matrix kernel must run and match.
            let m = d.layers() / 2;
            let mut records = vec![ScalarStorage::ZERO; m];
            let shared = PreparedScalars::prepare(
                &scalars[..m],
                &mut records,
                TaskBudget::SERIAL,
                &SerialExecutor,
            );
            let matrix = SharedScalarInput::new(bases, shared, 3, 1, 0).unwrap();
            let options = ExecutionOptions::default().with_task_budget(TaskBudget::new(3).unwrap());
            let r = matrix.requirements(options).unwrap();
            let mut buffers = Buffers::new(r);
            let mut output = [ProjectivePoint::IDENTITY; 3];
            let (_, calls) = super::super::test_support::count_kernels(|| {
                matrix
                    .execute(&mut output, options, &SerialExecutor, buffers.borrow())
                    .unwrap()
            });
            assert!(calls.for_geometry(recode::Geometry::Alpha(width)) > 0);
            for (j, result) in output.into_iter().enumerate() {
                let indices = vec![j as u32; m];
                assert_eq!(
                    result,
                    reference(&Input::indexed(bases, &indices, &scalars[..m]).unwrap()),
                    "width={width} output={j}"
                );
            }
            buffers.tails(r);
        }

        let mut records = [ScalarStorage::ZERO; 4];
        let shared = PreparedScalars::prepare(
            &scalars[..4],
            &mut records,
            TaskBudget::SERIAL,
            &SerialExecutor,
        );
        // Repeated ranges must retain the physical stride of the full α bank.
        for odd_width in [2, 5, width] {
            let odd = AlphaTable::bind(book, &prepared)
                .range(3..38)
                .range(2..33)
                .odd_multiples(odd_width)
                .unwrap()
                .range(2..29);
            let matrix = SharedScalarInput::new(Bases::OddPrepared(odd), shared, 3, 1, 6).unwrap();
            let options = ExecutionOptions::default();
            let r = matrix.requirements(options).unwrap();
            let mut buffers = Buffers::new(r);
            let mut output = [ProjectivePoint::IDENTITY; 3];
            matrix
                .execute(&mut output, options, &SerialExecutor, buffers.borrow())
                .unwrap();
            for (j, result) in output.into_iter().enumerate() {
                let indices = core::array::from_fn::<_, 4, _>(|i| (7 + j + 6 * i) as u32);
                assert_eq!(
                    result,
                    reference(
                        &Input::indexed(Bases::Affine(&affine), &indices, &scalars[..4]).unwrap()
                    )
                );
            }
            buffers.tails(r);
        }
    }
}

#[test]
fn pallas_alpha() {
    differentials::<Pallas>();
}
#[test]
fn vesta_alpha() {
    differentials::<Vesta>();
}

fn wnaf<C: PastaCurve>() {
    let g = AffinePoint::<C>::GENERATOR;
    let bases: Vec<_> = (0..160)
        .map(|i| if i % 3 == 0 { g.neg() } else { g })
        .collect();
    for width in [3, 5, 7, 8] {
        let mut entries = vec![
            g;
            OddTable::<C>::requirements(width, bases.len())
                .unwrap()
                .table_entries
        ];
        let table = OddTable::prepare(
            width,
            &bases,
            &mut entries,
            &mut vec![ProjectivePoint::IDENTITY; bases.len()],
            &mut vec![PastaField::ZERO; bases.len()],
            TaskBudget::new(3).unwrap(),
            &Pool,
        )
        .unwrap();
        let mut scalars: Vec<_> = field_samples::<C::Scalar>().take(4).collect();
        scalars[0] = PastaField::ONE;
        scalars[1] = PastaField::<C::Scalar>::ONE.neg();
        let mut records = vec![ScalarStorage::ZERO; PreparedScalars::<C>::storage_len(4).unwrap()];
        let prepared =
            PreparedScalars::prepare(&scalars, &mut records, TaskBudget::SERIAL, &SerialExecutor);
        for outputs in [0, 1, 17, 33] {
            let table = table.range(3..159);
            let matrix =
                SharedScalarInput::new(Bases::Odd(table), prepared, outputs, 1, 40).unwrap();
            let expected: Vec<_> = (0..outputs)
                .map(|i| {
                    let ix: Vec<_> = (0..4).map(|j| (3 + i + 40 * j) as u32).collect();
                    reference(&Input::indexed(Bases::Affine(&bases), &ix, &scalars).unwrap())
                })
                .collect();
            for tasks in [1, 3] {
                for limit in [None, Some(1100)] {
                    let options = ExecutionOptions::default()
                        .with_task_budget(TaskBudget::new(tasks).unwrap())
                        .with_memory_limit(limit.unwrap_or(usize::MAX));
                    let r = matrix.requirements(options).unwrap();
                    let mut buffers = Buffers::new(r);
                    let mut output = vec![ProjectivePoint::IDENTITY; outputs];
                    matrix
                        .execute(&mut output, options, &Pool, buffers.borrow())
                        .unwrap();
                    assert_eq!(output, expected, "width={width} outputs={outputs}");
                    buffers.tails(r);
                }
            }
        }
    }
}
#[test]
fn pallas_shared_wnaf() {
    wnaf::<Pallas>();
}
#[test]
fn vesta_shared_wnaf() {
    wnaf::<Vesta>();
}

#[test]
fn shared_wnaf_parallel_tiles_and_resource_errors() {
    let g = AffinePoint::<Vesta>::GENERATOR;
    let entries = [g];
    let table = OddTable::bind(2, &entries, 1, 1).unwrap();
    let mut records = [ScalarStorage::ZERO; 2];
    let scalars =
        PreparedScalars::signed(&[1, -1], &mut records, TaskBudget::SERIAL, &SerialExecutor);
    let input = SharedScalarInput::new(Bases::Odd(table), scalars, 777, 0, 0).unwrap();
    let options = ExecutionOptions::default().with_task_budget(TaskBudget::new(3).unwrap());
    let r = input.requirements(options).unwrap();
    let mut buffers = Buffers::new(r);
    let mut output = vec![ProjectivePoint::GENERATOR; 777];
    input
        .execute(&mut output, options, &Pool, buffers.borrow())
        .unwrap();
    assert!(output.iter().all(ProjectivePoint::is_identity));
    buffers.tails(r);

    let too_small = options.with_memory_limit(0);
    let mut buffers = Buffers::new(r);
    let mut output = vec![ProjectivePoint::GENERATOR; 777];
    assert!(matches!(
        input.execute(&mut output, too_small, &Pool, buffers.borrow()),
        Err(CurveError::MemoryLimit { .. })
    ));
    assert!(output.iter().all(|p| *p == ProjectivePoint::GENERATOR));
    assert!(buffers.digits.iter().all(|d| *d == 73));
    assert!(
        buffers
            .field
            .iter()
            .all(|f| f.reduce() == PastaField::<_>::ONE.reduce())
    );
}

#[test]
fn alpha_resource_fallbacks_and_staging() {
    fn check<C: PastaCurve>() {
        use crate::msm::execution::{BatchPlan, JobStorage, WorkerStorage};
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
        let scalars = [PastaField::<C::Scalar>::from_u64(7).invert().unwrap()];
        let input = Input::new(Bases::Alpha(table), &scalars);
        let originals = [g];
        let plain = Input::new(Bases::Affine(&originals), &scalars);
        let options = ExecutionOptions::DEFAULT.with_memory_limit(4096);
        let expected = g.mul_projective(&scalars[0]);
        let r = input.requirements(options).unwrap();
        assert_eq!(r, plain.requirements(options).unwrap());
        let mut buffers = Buffers::new(r);
        let (actual, calls) = super::super::test_support::count_kernels(|| {
            input
                .execute(options, &SerialExecutor, buffers.borrow())
                .unwrap()
        });
        assert_eq!(actual, expected);
        assert_eq!(calls.for_geometry(recode::Geometry::Alpha(7)), 0);
        buffers.tails(r);
        // Capacity-only admission must restart from the original ordinary plan.
        let mut buffers = Buffers::new(r);
        assert_eq!(
            input
                .execute(ExecutionOptions::DEFAULT, &SerialExecutor, buffers.borrow())
                .unwrap(),
            expected
        );
        buffers.tails(r);

        let inputs = [input, input];
        let mut jobs = [JobStorage::EMPTY; 2];
        let mut workers = [WorkerStorage::EMPTY; 2];
        let batch = BatchPlan::new(&inputs, options, &mut jobs, &mut workers).unwrap();
        let r = batch.requirements();
        let mut buffers = Buffers::new(r);
        let mut output = [ProjectivePoint::IDENTITY; 2];
        batch.execute(&mut output, &SerialExecutor, buffers.borrow());
        assert_eq!(output, [expected; 2]);
        buffers.tails(r);

        let mut records = [ScalarStorage::ZERO];
        let prepared =
            PreparedScalars::prepare(&scalars, &mut records, TaskBudget::SERIAL, &SerialExecutor);
        let matrix = SharedScalarInput::new(Bases::Alpha(table), prepared, 2, 0, 0).unwrap();
        let r = matrix.requirements(options).unwrap();
        for options in [options, ExecutionOptions::DEFAULT] {
            let mut buffers = Buffers::new(r);
            matrix
                .execute(&mut output, options, &SerialExecutor, buffers.borrow())
                .unwrap();
            assert_eq!(output, [expected; 2]);
            buffers.tails(r);
        }
        // One alpha deposit per term plus one survivor per bucket. The
        // corresponding Booth staging needs two deposits per term.
        let arithmetic = ArithmeticOptions::DEFAULT
            .with_algorithm(Algorithm::Booth {
                width: None,
                accumulation: Accumulation::Affine,
            })
            .unwrap();
        let alpha = super::super::schedule::fixed_geometry::<C>(
            8192,
            recode::Geometry::Alpha(7),
            arithmetic,
        )
        .unwrap();
        let booth = super::super::schedule::fixed_geometry::<C>(
            8192,
            recode::Geometry::Booth(7),
            arithmetic,
        )
        .unwrap();
        assert_eq!(alpha.work.affine(), 8192 + 2 * 64);
        assert_eq!(alpha.work.field(), 2 * (8192 + 64) + 2 * 64);
        assert_eq!(
            booth.work.bytes::<C>().unwrap() - alpha.work.bytes::<C>().unwrap(),
            1024 * 1024
        );
    }
    check::<Pallas>();
    check::<Vesta>();
}

#[test]
fn alpha_cache_admission_and_preflight() {
    use std::panic::{AssertUnwindSafe, catch_unwind};
    let executor = NoJoin::default();
    let d = AlphaDescription::new(7).unwrap();
    let mut codes = vec![0; d.codes()];
    let mut coefficients = vec![AlphaCoefficient::ZERO; d.layers()];
    let book = AlphaCodebook::prepare(
        d,
        &mut codes,
        &mut coefficients,
        &mut vec![0; d.codebook_scratch()],
    );
    let g = AffinePoint::<Pallas>::GENERATOR;
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
    for n in [0, 1, 1025, 8193] {
        let scalars = vec![
            PastaField::<<Pallas as PastaCurve>::Scalar>::from_u64(7)
                .invert()
                .unwrap();
            n
        ];
        let mut records = vec![ScalarStorage::ZERO; n];
        let prepared =
            PreparedScalars::prepare(&scalars, &mut records, TaskBudget::SERIAL, &SerialExecutor);
        let indices = vec![0; n];
        let input = Input::indexed_prepared(Bases::Alpha(table), &indices, prepared).unwrap();
        let plan = MsmPlan::for_input(&input, ExecutionOptions::DEFAULT).unwrap();
        let bytes = prepared.alpha_cache_len(&plan);
        assert_eq!(bytes != 0, (128..=8192).contains(&n));
        let mut storage = vec![0xa5; bytes + 1];
        let cached = prepared.cache_alpha(&plan, book, &mut storage, TaskBudget::SERIAL, &executor);
        if bytes != 0 {
            let cached_input =
                Input::indexed_prepared(Bases::Alpha(table), &indices, cached).unwrap();
            assert_eq!(
                cached_input
                    .requirements(ExecutionOptions::DEFAULT)
                    .unwrap()
                    .digits(),
                0
            );
            let mut parallel = vec![0xa5; bytes + 1];
            let _ = prepared.cache_alpha(
                &plan,
                book,
                &mut parallel,
                TaskBudget::new(3).unwrap(),
                &Pool,
            );
            assert_eq!(
                &parallel[..bytes],
                cached.cached_digits(recode::Geometry::Alpha(7)).unwrap()
            );
            let mut short = vec![0xa5; bytes - 1];
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    let _ = prepared.cache_alpha(
                        &plan,
                        book,
                        &mut short,
                        TaskBudget::new(3).unwrap(),
                        &executor,
                    );
                }))
                .is_err()
            );
            assert!(short.iter().all(|&b| b == 0xa5));
            let other_d = AlphaDescription::new(5).unwrap();
            let mut other_codes = vec![0; other_d.codes()];
            let mut other_coefficients = vec![AlphaCoefficient::ZERO; other_d.layers()];
            let other = AlphaCodebook::prepare(
                other_d,
                &mut other_codes,
                &mut other_coefficients,
                &mut vec![0; other_d.codebook_scratch()],
            );
            let mut untouched = vec![0xa5; bytes];
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    let _ = prepared.cache_alpha(
                        &plan,
                        other,
                        &mut untouched,
                        TaskBudget::new(3).unwrap(),
                        &executor,
                    );
                }))
                .is_err()
            );
            assert!(untouched.iter().all(|&b| b == 0xa5));
        }
        for incompatible in [
            MsmPlan::new(n, ExecutionOptions::DEFAULT).unwrap(),
            MsmPlan::new(n + 1, ExecutionOptions::DEFAULT).unwrap(),
            MsmPlan::for_input(
                &input,
                ExecutionOptions::DEFAULT.with_memory_limit(if n <= 1 { 4096 } else { 8192 }),
            )
            .unwrap(),
        ] {
            assert_eq!(cached.alpha_cache_len(&incompatible), 0);
            let mut untouched = [0xa5; 3];
            let same = cached.cache_alpha(
                &incompatible,
                book,
                &mut untouched,
                TaskBudget::new(3).unwrap(),
                &executor,
            );
            assert_eq!(same.retained_bytes(), cached.retained_bytes());
            assert_eq!(untouched, [0xa5; 3]);
        }
        assert_eq!(storage[bytes], 0xa5);
    }
    executor.check();
}

#[test]
fn alpha_selection_uses_size_workers_and_available_scratch() {
    fn check<C: PastaCurve>() {
        use crate::msm::execution::ProducedInput;
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
        let bases = Bases::Alpha(table);
        let scalars: Vec<_> = field_samples::<C::Scalar>().take(64).collect();
        let indices = [0; 64];
        let mut records = [ScalarStorage::ZERO; 64];
        let prepared =
            PreparedScalars::prepare(&scalars, &mut records, TaskBudget::SERIAL, &SerialExecutor);
        let input = Input::indexed_prepared(bases, &indices, prepared).unwrap();
        let parallel = ExecutionOptions::DEFAULT.with_task_budget(TaskBudget::new(3).unwrap());
        let plan = MsmPlan::for_input(&input, parallel).unwrap();
        let mut digits = vec![0; prepared.alpha_cache_len(&plan)];
        assert!(!digits.is_empty());
        let cached = prepared.cache_alpha(
            &plan,
            book,
            &mut digits,
            TaskBudget::SERIAL,
            &SerialExecutor,
        );
        let expected = reference(&Input::indexed(bases, &indices, &scalars).unwrap());
        for (options, alpha) in [
            (ExecutionOptions::DEFAULT, false),
            (parallel, true),
            (parallel.with_memory_limit(8192), false),
        ] {
            for scalars in [prepared, cached] {
                let input = Input::indexed_prepared(bases, &indices, scalars).unwrap();
                let plan = MsmPlan::for_input(&input, options).unwrap();
                assert_eq!(scalars.alpha_cache_len(&plan) != 0, alpha);
                let produced = MsmPlan::for_produced(
                    ProducedInput::indexed(bases, 64),
                    NonZeroUsize::new(64).unwrap(),
                    options,
                )
                .unwrap();
                assert_eq!(prepared.alpha_cache_len(&produced) != 0, alpha);
                let r = input.requirements(options).unwrap();
                let mut buffers = Buffers::new(r);
                let (actual, calls) = super::super::test_support::count_kernels(|| {
                    input
                        .execute(options, &SerialExecutor, buffers.borrow())
                        .unwrap()
                });
                assert_eq!(actual, expected);
                assert_eq!(calls.for_geometry(recode::Geometry::Alpha(7)) != 0, alpha);
                buffers.tails(r);
                assert_eq!(
                    input.execute(options, &Pool, buffers.borrow()).unwrap(),
                    expected
                );
                buffers.tails(r);
            }
        }
    }
    check::<Pallas>();
    check::<Vesta>();
}

#[test]
fn alpha_preparation_checks_lengths_before_writes() {
    use std::panic::{AssertUnwindSafe, catch_unwind};
    let d = AlphaDescription::new(5).unwrap();
    let mut codes = vec![0xa5; d.codes()];
    let mut coefficients = vec![AlphaCoefficient::ZERO; d.layers()];
    let mut scratch = vec![0xa5; d.codebook_scratch() + 1];
    for short in 0..3 {
        assert!(
            catch_unwind(AssertUnwindSafe(|| {
                AlphaCodebook::prepare(
                    d,
                    &mut codes[..d.codes() - usize::from(short == 0)],
                    &mut coefficients[..d.layers() - usize::from(short == 1)],
                    &mut scratch[..d.codebook_scratch() - usize::from(short == 2)],
                );
            }))
            .is_err()
        );
        assert!(codes.iter().all(|&c| c == 0xa5));
        assert!(coefficients.iter().all(|&c| c == AlphaCoefficient::ZERO));
        assert!(scratch.iter().all(|&s| s == 0xa5));
    }
    let book = AlphaCodebook::prepare(d, &mut codes, &mut coefficients, &mut scratch);
    assert_eq!(scratch[d.codebook_scratch()], 0xa5);
    let g = AffinePoint::<Pallas>::GENERATOR;
    let bases = vec![g; 65];
    let r = d
        .requirements::<Pallas, AffinePoint<Pallas>>(bases.len())
        .unwrap();
    let mut entries = vec![g.neg(); r.table_entries];
    let mut projective = vec![ProjectivePoint::IDENTITY; r.projective_scratch + 1];
    let mut field = vec![PastaField::ONE; r.field_scratch + 1];
    let executor = NoJoin::default();
    for short in 0..3 {
        assert!(
            catch_unwind(AssertUnwindSafe(|| {
                AlphaTable::prepare(
                    book,
                    &bases,
                    &mut entries[..r.table_entries - usize::from(short == 0)],
                    &mut projective[..r.projective_scratch - usize::from(short == 1)],
                    &mut field[..r.field_scratch - usize::from(short == 2)],
                    TaskBudget::new(3).unwrap(),
                    &executor,
                );
            }))
            .is_err()
        );
        assert!(entries.iter().all(|&p| p == g.neg()));
        assert!(projective.iter().all(ProjectivePoint::is_identity));
        assert!(field.iter().all(PastaField::is_one));
    }
    let table = AlphaTable::prepare(
        book,
        &bases,
        &mut entries,
        &mut projective,
        &mut field,
        TaskBudget::new(3).unwrap(),
        &Pool,
    );
    assert!(projective[r.projective_scratch].is_identity());
    assert!(field[r.field_scratch].is_one());
    assert!(catch_unwind(|| table.range(0..bases.len() + 1)).is_err());
    for width in [0, 1, 6, u8::MAX] {
        assert!(matches!(
            table.odd_multiples(width),
            Err(CurveError::InvalidWindowBits { .. })
        ));
    }
    assert!(catch_unwind(|| AlphaTable::<Pallas>::bind(book, &entries[1..])).is_err());
    let empty = AlphaTable::<Pallas>::prepare(
        book,
        &[] as &[AffinePoint<Pallas>],
        &mut [],
        &mut projective,
        &mut field,
        TaskBudget::new(3).unwrap(),
        &executor,
    );
    assert!(empty.is_empty());
    executor.check();
}

#[test]
fn odd_table_dimensions_fail_before_writes() {
    use std::panic::{AssertUnwindSafe, catch_unwind};
    let g = AffinePoint::<Pallas>::GENERATOR;
    for width in [0, 1, 9, u8::MAX] {
        assert!(matches!(
            OddTable::<Pallas>::requirements(width, 1),
            Err(CurveError::InvalidWindowBits { .. })
        ));
        assert!(matches!(
            OddTable::bind(width, &[g], 1, 1),
            Err(CurveError::InvalidWindowBits { .. })
        ));
    }
    assert_eq!(
        OddTable::<Pallas>::requirements(8, usize::MAX),
        Err(CurveError::SizeOverflow)
    );
    assert!(matches!(
        OddTable::bind(8, &[g], 1, usize::MAX),
        Err(CurveError::SizeOverflow)
    ));
    let mut entries = [g; 1];
    let mut projective = [ProjectivePoint::GENERATOR; 2];
    let mut field = [PastaField::ONE; 2];
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            let _ = OddTable::prepare(
                3,
                &[g],
                &mut entries,
                &mut projective,
                &mut field,
                TaskBudget::SERIAL,
                &SerialExecutor,
            );
        }))
        .is_err()
    );
    assert_eq!(entries, [g]);
    assert_eq!(projective, [ProjectivePoint::GENERATOR; 2]);
    assert!(field.iter().all(PastaField::is_one));
    let table = OddTable::prepare(
        2,
        &[g],
        &mut entries,
        &mut projective,
        &mut field,
        TaskBudget::SERIAL,
        &SerialExecutor,
    )
    .unwrap();
    assert_eq!(table.len(), 1);
    assert_eq!(projective[1], ProjectivePoint::GENERATOR);
    assert!(field[1].is_one());
    assert!(catch_unwind(|| table.range(0..2)).is_err());
    assert!(
        OddTable::<Pallas>::bind(8, &[], 0, usize::MAX)
            .unwrap()
            .is_empty()
    );
}

#[test]
fn odd_matrices_use_short_specialization_and_chunked_fallbacks() {
    fn check<C: PastaCurve>() {
        let g = AffinePoint::<C>::GENERATOR;
        let entries = [g];
        let table = OddTable::bind(2, &entries, 1, 1).unwrap();
        let bases = Bases::Odd(table);
        for n in [2, 129, 8193] {
            for short in [false, true] {
                let value = if short {
                    PastaField::<C::Scalar>::ONE
                } else {
                    PastaField::<C::Scalar>::from_u64(7).invert().unwrap()
                };
                let scalars = vec![value; n];
                let mut records = vec![ScalarStorage::ZERO; n];
                let prepared = PreparedScalars::prepare(
                    &scalars,
                    &mut records,
                    TaskBudget::SERIAL,
                    &SerialExecutor,
                );
                let matrix = SharedScalarInput::new(bases, prepared, 2, 0, 0).unwrap();
                let plain =
                    SharedScalarInput::new(Bases::Affine(&entries), prepared, 2, 0, 0).unwrap();
                let expected =
                    g.mul_projective(&value.mul(&PastaField::<C::Scalar>::from_u64(n as u64)));
                for limit in [8192, usize::MAX] {
                    let options = ExecutionOptions::DEFAULT.with_memory_limit(limit);
                    let r = matrix.requirements(options).unwrap();
                    if short || n > 8192 {
                        assert_eq!(r, plain.requirements(options).unwrap());
                    }
                    let mut buffers = Buffers::new(r);
                    let mut output = [ProjectivePoint::IDENTITY; 2];
                    let (_, calls) = super::super::test_support::count_kernels(|| {
                        matrix
                            .execute(&mut output, options, &SerialExecutor, buffers.borrow())
                            .unwrap()
                    });
                    assert_eq!(output, [expected; 2]);
                    if short {
                        assert!(calls.for_geometry(recode::Geometry::Short(1)) > 0);
                    }
                    if !short && (n > 8192 || n * 256 > limit) {
                        assert!(calls.total() > 0);
                    }
                    buffers.tails(r);
                }
                // A capacity-only fallback has the same result and leaves tails.
                let r = plain
                    .requirements(ExecutionOptions::DEFAULT.with_memory_limit(8192))
                    .unwrap();
                let mut buffers = Buffers::new(r);
                let mut output = [ProjectivePoint::IDENTITY; 2];
                matrix
                    .execute(
                        &mut output,
                        ExecutionOptions::DEFAULT,
                        &SerialExecutor,
                        buffers.borrow(),
                    )
                    .unwrap();
                assert_eq!(output, [expected; 2]);
                buffers.tails(r);
            }
        }
    }
    check::<Pallas>();
    check::<Vesta>();
}

// Exercise both sides of the batched coefficient integration threshold, with
// enough deposits to test tail and main-window passes beyond small-bank cases.
#[test]
fn large_alpha_batches_match_independent_multiplication() {
    fn check<C: PastaCurve>(width: u8) {
        let affine: Vec<_> = (1..=19)
            .map(|i| {
                *AffinePoint::<C>::GENERATOR
                    .mul_projective(&PastaField::from_u64(i))
                    .to_point()
                    .as_affine()
                    .unwrap()
            })
            .collect();
        let d = AlphaDescription::new(width).unwrap();
        let mut codes = vec![0; d.codes()];
        let mut coefficients = vec![AlphaCoefficient::ZERO; d.layers()];
        let book = AlphaCodebook::prepare(
            d,
            &mut codes,
            &mut coefficients,
            &mut vec![0; d.codebook_scratch()],
        );
        let mut entries = vec![AffinePoint::GENERATOR; d.layers() * affine.len()];
        AlphaTable::prepare(
            book,
            &affine,
            &mut entries,
            &mut vec![ProjectivePoint::IDENTITY; affine.len()],
            &mut vec![PastaField::ZERO; affine.len()],
            TaskBudget::SERIAL,
            &SerialExecutor,
        );
        let prepared: Vec<_> = entries
            .iter()
            .map(PreparedAffinePoint::from_affine)
            .collect();
        let mut scalars: Vec<_> = field_samples::<C::Scalar>().take(233).collect();
        let mut indices: Vec<_> = (0..scalars.len())
            .map(|i| (i % affine.len()) as u32)
            .collect();
        // Force cancellation as well as unrelated full-width scalar pairs.
        for i in (0..200).step_by(8) {
            scalars[i + 1] = scalars[i].neg();
            indices[i + 1] = indices[i];
            scalars[i + 2] = PastaField::ZERO;
        }
        let expected =
            reference(&Input::indexed(Bases::Affine(&affine), &indices, &scalars).unwrap());
        for bases in [
            Bases::Alpha(AlphaTable::bind(book, &entries)),
            Bases::AlphaPrepared(AlphaTable::bind(book, &prepared)),
        ] {
            let input = Input::indexed(bases, &indices, &scalars).unwrap();
            for tasks in [1, 3] {
                for cap in [17, 97, 233] {
                    let options = BatchOptions::new(
                        ArithmeticOptions::DEFAULT
                            .with_algorithm(Algorithm::Alpha {
                                accumulation: Accumulation::Affine,
                            })
                            .unwrap()
                            .with_max_terms_per_pass(NonZeroUsize::new(cap)),
                    )
                    .with_task_budget(TaskBudget::new(tasks).unwrap());
                    let r = input.requirements_with(options).unwrap();
                    let mut buffers = Buffers::new(r);
                    assert_eq!(
                        input
                            .execute_with(options, &Pool, buffers.borrow())
                            .unwrap(),
                        expected,
                        "width={width} tasks={tasks} cap={cap}"
                    );
                    buffers.tails(r);
                }
            }
        }
    }
    for width in 5..=7 {
        check::<Pallas>(width);
        check::<Vesta>(width);
    }
}

#[test]
fn alpha_fragmented_digit_views_match_reference() {
    use crate::msm::{kernels, storage::Storage};
    use core::{cell::Cell, ops::Range};

    #[derive(Clone, Copy, Debug)]
    enum Contiguous {
        Fragments(usize),
        CodesOnly,
        Never,
    }

    #[derive(Default)]
    struct Accesses {
        large: Cell<usize>,
        codes: Cell<usize>,
        indexed: Cell<usize>,
    }

    #[derive(Clone, Copy)]
    struct Digits<'a> {
        bytes: &'a [u8],
        start: usize,
        len: usize,
        contiguous: Contiguous,
        accesses: &'a Accesses,
    }

    impl Storage<u8> for Digits<'_> {
        fn len(self) -> usize {
            self.len
        }
        fn get(self, index: usize) -> u8 {
            assert!(index < self.len);
            self.accesses.indexed.set(self.accesses.indexed.get() + 1);
            self.bytes[self.start + index]
        }
        fn slice(self, range: Range<usize>) -> Self {
            assert!(range.start <= range.end && range.end <= self.len);
            Self {
                start: self.start + range.start,
                len: range.len(),
                ..self
            }
        }
        fn contiguous(&self) -> Option<&[u8]> {
            let available = match self.contiguous {
                Contiguous::Fragments(grain) => {
                    self.len == 0 || self.start / grain == (self.start + self.len - 1) / grain
                }
                Contiguous::CodesOnly => self.len <= 4,
                Contiguous::Never => false,
            };
            available.then(|| {
                let counter = if self.len > 4 {
                    &self.accesses.large
                } else {
                    &self.accesses.codes
                };
                counter.set(counter.get() + 1);
                &self.bytes[self.start..self.start + self.len]
            })
        }
    }

    fn check<C: PastaCurve>() {
        const TERMS: usize = 257;
        const OFFSET: usize = 512;
        let g = AffinePoint::<C>::GENERATOR;
        let affine: Vec<_> = (1..=19)
            .map(|i| {
                *g.mul_projective(&PastaField::from_u64(i))
                    .to_point()
                    .as_affine()
                    .unwrap()
            })
            .collect();
        let mut scalars: Vec<_> = field_samples::<C::Scalar>().take(TERMS).collect();
        let mut indices: Vec<_> = (0..TERMS).map(|i| (i * 7 % affine.len()) as u32).collect();
        for i in (0..TERMS - 3).step_by(11) {
            scalars[i + 1] = scalars[i].neg();
            indices[i + 1] = indices[i];
            scalars[i + 2] = PastaField::ZERO;
        }
        // This oracle uses the independent binary scalar ladder on originals;
        // it knows nothing about Alpha codes, fragments, passes, or buckets.
        let expected =
            reference(&Input::indexed(Bases::Affine(&affine), &indices, &scalars).unwrap());
        let mut records = vec![ScalarStorage::ZERO; TERMS];
        PreparedScalars::prepare(&scalars, &mut records, TaskBudget::SERIAL, &SerialExecutor);

        for width in 5..=7 {
            let description = AlphaDescription::new(width).unwrap();
            let mut codes = vec![0; description.codes()];
            let mut coefficients = vec![AlphaCoefficient::ZERO; description.layers()];
            let book = AlphaCodebook::prepare(
                description,
                &mut codes,
                &mut coefficients,
                &mut vec![0; description.codebook_scratch()],
            );
            let r = description
                .requirements::<C, AffinePoint<C>>(affine.len())
                .unwrap();
            let mut entries = vec![g; r.table_entries];
            AlphaTable::prepare(
                book,
                &affine,
                &mut entries,
                &mut vec![ProjectivePoint::IDENTITY; r.projective_scratch],
                &mut vec![PastaField::ZERO; r.field_scratch],
                TaskBudget::SERIAL,
                &SerialExecutor,
            );
            let prepared: Vec<_> = entries
                .iter()
                .map(PreparedAffinePoint::from_affine)
                .collect();
            let geometry = recode::Geometry::Alpha(width);
            let stride = geometry.stride();
            let prefix = recode::CHUNK * stride;
            let digit_len = TERMS * stride;
            let mut bytes = vec![0xa5; prefix + digit_len + 7];
            recode::write_bases(
                &records,
                geometry,
                &mut bytes[prefix..prefix + digit_len],
                Bases::Alpha(AlphaTable::bind(book, &entries)),
            );

            for bases in [
                Bases::Alpha(AlphaTable::bind(book, &entries)),
                Bases::AlphaPrepared(AlphaTable::bind(book, &prepared)),
            ] {
                let local_indices = indices.as_slice();
                let input = kernels::BaseView {
                    bases,
                    indices: Some(kernels::Indices::Fragment {
                        view: &local_indices,
                        offset: OFFSET,
                    }),
                };
                for pass in [TERMS, 255, 127] {
                    let arithmetic = ArithmeticOptions::DEFAULT
                        .with_algorithm(Algorithm::Alpha {
                            accumulation: Accumulation::Affine,
                        })
                        .unwrap()
                        .with_max_terms_per_pass(NonZeroUsize::new(pass));
                    let work =
                        super::super::schedule::fixed_geometry::<C>(TERMS, geometry, arithmetic)
                            .unwrap()
                            .work;
                    let mut points = vec![g; work.affine() + 1];
                    let mut projective = vec![g.to_projective(); work.projective() + 1];
                    let mut fields = vec![PastaField::<C::Base>::ONE; work.field() + 1];
                    let mut cursors = vec![usize::MAX; work.indices() + 1];
                    for contiguous in [
                        Contiguous::Fragments(recode::CHUNK * stride),
                        // Provider boundaries may split preparation rows and codes.
                        Contiguous::Fragments(13 * stride + 2),
                        Contiguous::CodesOnly,
                        Contiguous::Never,
                    ] {
                        let accesses = Accesses::default();
                        // A nonzero storage start must remain independent of the
                        // absolute base/index offset and of partition-local digits.
                        let digits = Digits {
                            bytes: &bytes,
                            start: 0,
                            len: bytes.len(),
                            contiguous,
                            accesses: &accesses,
                        }
                        .slice(prefix..prefix + digit_len);
                        let mut scratch = kernels::Work {
                            affine: &mut points[..work.affine()],
                            projective: &mut projective[..work.projective()],
                            field: &mut fields[..work.field()],
                            indices: &mut cursors[..work.indices()],
                        };
                        let mut result = ProjectivePoint::IDENTITY;
                        for window in (0..geometry.windows()).rev() {
                            let partial = kernels::run_selected(
                                &input,
                                records.as_slice(),
                                digits,
                                kernels::Task {
                                    offset: OFFSET,
                                    window,
                                    pass,
                                    geometry,
                                    accumulation: Accumulation::Affine,
                                },
                                &mut scratch,
                            );
                            for _ in 0..geometry.width() {
                                result = result.double();
                            }
                            result = result.add(&partial);
                        }
                        assert_eq!(
                            result, expected,
                            "width={width} pass={pass} provider={contiguous:?}"
                        );
                        match contiguous {
                            Contiguous::Fragments(grain) if grain == recode::CHUNK * stride => {
                                assert!(accesses.large.get() > 0, "exercise whole-fragment reads");
                            }
                            Contiguous::CodesOnly => {
                                assert_eq!(accesses.large.get(), 0);
                                assert!(
                                    accesses.codes.get() > 0,
                                    "exercise per-code contiguous fallback"
                                );
                            }
                            Contiguous::Never => {
                                assert_eq!(accesses.large.get() + accesses.codes.get(), 0);
                                assert!(
                                    accesses.indexed.get() > 0,
                                    "exercise indexed-byte fallback"
                                );
                            }
                            _ => (),
                        }
                        assert!(points[work.affine()] == g);
                        assert!(projective[work.projective()] == g.to_projective());
                        assert_eq!(
                            fields[work.field()].montgomery_limbs(),
                            PastaField::<C::Base>::ONE.montgomery_limbs()
                        );
                        assert_eq!(cursors[work.indices()], usize::MAX);
                    }
                }
            }
            assert!(
                bytes[..prefix]
                    .iter()
                    .chain(&bytes[prefix + digit_len..])
                    .all(|&b| b == 0xa5)
            );
        }
    }
    check::<Pallas>();
    check::<Vesta>();
}
