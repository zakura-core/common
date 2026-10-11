use super::*;
use crate::exec::{Executor, SerialExecutor, TaskBudget};

struct Pool;
impl Executor for Pool {
    fn join<L, R, A, B>(&self, left: L, right: R) -> (A, B)
    where
        L: FnOnce() -> A + Send,
        R: FnOnce() -> B + Send,
        A: Send,
        B: Send,
    {
        rayon::join(left, right)
    }
}

#[test]
fn public_scalars_use_nonexceptional_affine_ladders() {
    fn check<C: PastaCurve>() {
        let g = AffinePoint::<C>::GENERATOR;
        let distinct = [g, g.neg(), g.endomorphism()];
        let bases: Vec<_> = distinct.into_iter().cycle().take(64).collect();
        let r = EisensteinTableBatch::<C>::requirements(bases.len()).unwrap();
        let mut entries = vec![g; r.table_entries];
        let mut projective = vec![ProjectivePoint::IDENTITY; r.projective_scratch];
        let mut field = vec![
            PastaField::ZERO;
            EisensteinTableBatch::<C>::multiplication_scratch(bases.len()).unwrap()
        ];
        let tables = EisensteinTableBatch::prepare(
            &bases,
            &mut entries,
            &mut projective,
            &mut field,
            TaskBudget::SERIAL,
            &SerialExecutor,
        );
        let mut output = vec![ProjectivePoint::IDENTITY; bases.len()];
        for scalar in scalar_corpus::<C>()
            .into_iter()
            .chain([PastaField::from_montgomery_limbs(C::Scalar::MODULUS)])
            .chain(field_samples::<C::Scalar>().take(64))
        {
            let prepared = EisensteinScalar::new(&scalar);
            let zero = scalar.reduce() == PastaField::ZERO;
            assert_eq!(prepared.digits().is_empty(), zero);
            let products =
                distinct.map(|base| multiply(&scalar, |sum| sum.add_mixed(&base)).to_point());
            let expected: Vec<_> = products.into_iter().cycle().take(bases.len()).collect();
            for reuse in [false, true] {
                if reuse {
                    tables.mul_prepared(
                        &prepared,
                        &mut output,
                        &mut field,
                        TaskBudget::SERIAL,
                        &SerialExecutor,
                    );
                } else {
                    tables.mul(
                        &scalar,
                        &mut output,
                        &mut field,
                        TaskBudget::SERIAL,
                        &SerialExecutor,
                    );
                }
                // Every nonzero public scalar stays in the affine ladder.
                // Zero keeps its separate identity path.
                let z = if zero {
                    PastaField::ZERO
                } else {
                    PastaField::ONE
                };
                assert!(output.iter().all(|point| point.z.reduce() == z));
                let inversions = crate::field::count_inversions(|| {
                    for (point, expected) in output.iter().zip(&expected) {
                        assert_eq!(point.to_point(), *expected);
                    }
                    let mut normalized = vec![Point::IDENTITY; bases.len()];
                    batch_normalize(&output, &mut normalized, &mut field);
                    assert_eq!(normalized, expected);
                });
                assert_eq!(inversions, 0);
            }
        }
    }
    check::<Pallas>();
    check::<Vesta>();
}

fn batches<C: PastaCurve, E: CurveTableEntry<C> + Eq>() {
    let g = AffinePoint::<C>::GENERATOR;
    let bases: Vec<_> = (1..=129)
        .map(|i| {
            *g.mul_projective(&PastaField::<_>::from_u64(i))
                .to_point()
                .as_affine()
                .unwrap()
        })
        .collect();
    let cached: Vec<_> = bases.iter().map(PreparedAffinePoint::from_affine).collect();
    for n in [0, 1, 7, 8, 15, 31, 32, 33, 63, 64, 65, 99, 128, 129] {
        let r = EisensteinTableBatch::<C, E>::requirements(n).unwrap();
        let mut entries = vec![E::from_affine(&g); r.table_entries];
        let mut projective = vec![ProjectivePoint::GENERATOR; r.projective_scratch + 1];
        let mut field = vec![PastaField::ONE; r.field_scratch + 1];
        for tasks in [1, 3, 8] {
            let budget = TaskBudget::new(tasks).unwrap();
            let tables = EisensteinTableBatch::prepare(
                &bases[..n],
                &mut entries,
                &mut projective,
                &mut field,
                budget,
                &Pool,
            );
            let expected = tables.as_slice().to_vec();
            let tables = EisensteinTableBatch::prepare(
                &cached[..n],
                &mut entries,
                &mut projective,
                &mut field,
                budget,
                &Pool,
            );
            assert_eq!(tables.as_slice(), expected);
            assert_eq!(projective[r.projective_scratch], ProjectivePoint::GENERATOR);
            assert_eq!(
                (field[r.field_scratch]).reduce(),
                (PastaField::<_>::ONE).reduce()
            );
            EisensteinTableBatch::<C, E>::bind(tables.as_slice());
            assert!(tables.get(n).is_none());
            let required = EisensteinTableBatch::<C, E>::multiplication_scratch(n).unwrap();
            let mut scratch = vec![PastaField::ONE; required + 1];
            let mut output = vec![ProjectivePoint::GENERATOR; n];
            for scalar in scalar_corpus::<C>().into_iter().step_by(7) {
                let prepared = EisensteinScalar::new(&scalar);
                tables.mul_prepared(&prepared, &mut output, &mut scratch, budget, &Pool);
                assert_eq!(
                    (scratch[required]).reduce(),
                    (PastaField::<_>::ONE).reduce()
                );
                for (i, base) in bases[..n].iter().enumerate() {
                    let expected = multiply(&scalar, |sum| sum.add_mixed(base));
                    assert_eq!(output[i], expected, "n={n}, tasks={tasks}, term={i}");
                    assert_eq!(tables.get(i).unwrap().mul_prepared(&prepared), expected);
                }
            }
        }
    }
}

#[test]
fn pallas() {
    rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap()
        .install(|| {
            batches::<Pallas, AffinePoint<Pallas>>();
            batches::<Pallas, PreparedAffinePoint<Pallas>>();
            batches::<Pallas, crate::curve::RotatedAffinePoint<Pallas>>();
        });
}
#[test]
fn vesta() {
    // Nested joins must also finish when no other worker is available.
    rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap()
        .install(|| {
            batches::<Vesta, AffinePoint<Vesta>>();
            batches::<Vesta, PreparedAffinePoint<Vesta>>();
            batches::<Vesta, crate::curve::RotatedAffinePoint<Vesta>>();
        });
}

#[test]
fn errors_preserve_preparation_and_multiplication_buffers() {
    type C = Pallas;
    let g = AffinePoint::<C>::GENERATOR;
    for n in [7, 8, 63, 64, 65] {
        let r = EisensteinTableBatch::<C>::requirements(n).unwrap();
        for failure in 0..3 {
            let bases = vec![g; n];
            let mut entries = vec![g; r.table_entries];
            let mut projective = vec![ProjectivePoint::GENERATOR; r.projective_scratch];
            let mut field = vec![PastaField::ONE; r.field_scratch];
            if failure == 0 {
                entries.pop();
            }
            if failure == 1 {
                field.pop();
            }
            if failure == 2 && projective.pop().is_none() {
                continue;
            }
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                EisensteinTableBatch::prepare(
                    &bases,
                    &mut entries,
                    &mut projective,
                    &mut field,
                    TaskBudget::SERIAL,
                    &SerialExecutor,
                );
            }));
            assert!(result.is_err());
            assert!(entries.iter().all(|&p| p == g));
            assert!(projective.iter().all(|&p| p == ProjectivePoint::GENERATOR));
            assert!(field.iter().all(|f| f.reduce() == PastaField::ONE));
        }
        let mut entries = vec![g; r.table_entries];
        let mut projective = vec![ProjectivePoint::IDENTITY; r.projective_scratch];
        let mut field = vec![PastaField::ZERO; r.field_scratch];
        let tables = EisensteinTableBatch::prepare(
            &vec![g; n],
            &mut entries,
            &mut projective,
            &mut field,
            TaskBudget::SERIAL,
            &SerialExecutor,
        );
        let required = EisensteinTableBatch::<C>::multiplication_scratch(n).unwrap();
        let mut field = vec![PastaField::ONE; required];
        let mut output = vec![ProjectivePoint::GENERATOR; n + 1];
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                tables.mul(
                    &PastaField::<_>::ONE,
                    &mut output,
                    &mut field,
                    TaskBudget::SERIAL,
                    &SerialExecutor,
                );
            }))
            .is_err()
        );
        assert!(output.iter().all(|&p| p == ProjectivePoint::GENERATOR));
        assert!(field.iter().all(|f| f.reduce() == PastaField::ONE));
        let scalar = PastaField::<_>::from_u64(1234567).invert().unwrap();
        let expected = g.mul_projective(&scalar);
        for capacity in [0, required / 2, required.saturating_sub(1), required] {
            tables.mul(
                &scalar,
                &mut output[..n],
                &mut field[..capacity],
                TaskBudget::new(3).unwrap(),
                &SerialExecutor,
            );
            assert!(output[..n].iter().all(|p| *p == expected));
            assert_eq!(output[n], ProjectivePoint::GENERATOR);
        }
    }
    assert!(
        std::panic::catch_unwind(|| {
            EisensteinTableBatch::<C>::bind(&[g; 7]);
        })
        .is_err()
    );
    assert!(matches!(
        EisensteinTableBatch::<C>::requirements(usize::MAX),
        Err(CurveError::SizeOverflow)
    ));
    assert!(matches!(
        EisensteinTableBatch::<C>::multiplication_scratch(usize::MAX),
        Err(CurveError::SizeOverflow)
    ));
}
