use zakura_udon::{
    curve::*,
    exec::{Executor, SerialExecutor, TaskBudget},
    field::{Fp, Fq},
};

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
fn independent_legacy_key_agreement_and_effective_batches() {
    let cases: Vec<_> = include_bytes!("fixtures/key-agreement.bin")
        .chunks_exact(96)
        .map(|c| {
            (
                <Fq>::from_bytes(c[..32].try_into().unwrap()).unwrap(),
                PallasPoint::from_bytes(c[32..64].try_into().unwrap()).unwrap(),
                PallasPoint::from_bytes(c[64..].try_into().unwrap()).unwrap(),
            )
        })
        .collect();
    for (scalar, base, expected) in &cases {
        assert_eq!(base.mul_projective(scalar).to_point(), *expected);
        // Exercise the shared-inversion path directly against frozen legacy
        // products, including its identity lane, rather than a Udon oracle.
        let mut batch = vec![base.to_projective(); 33];
        batch[32] = PallasProjective::IDENTITY;
        batch_mul_same_scalar(
            &mut batch,
            scalar,
            &mut vec![Fp::ZERO; same_scalar_scratch::<Pallas>(33).unwrap()],
            TaskBudget::SERIAL,
            &SerialExecutor,
        );
        assert!(batch[..32].iter().all(|p| p.to_point() == *expected));
        assert!(batch[32].is_identity());
    }
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(3)
        .build()
        .unwrap();
    pool.install(|| {
        for n in [0, 1, 7, 8, 16, 31, 32, 33, 63, 64, 65, 128, 132] {
            let inputs: Vec<_> = cases[..n]
                .iter()
                .map(|(_, base, _)| base.double())
                .collect();
            let size = same_scalar_scratch::<Pallas>(n).unwrap();
            for scalar in [<Fq>::ZERO, <Fq>::ONE, <Fq>::ONE.neg(), cases[17].0] {
                let expected: Vec<_> = inputs.iter().map(|base| base.mul(&scalar)).collect();
                for capacity in [0, size / 2, size.saturating_sub(1), size] {
                    let mut output = inputs.clone();
                    let mut fields = vec![Fp::ONE; capacity + 1];
                    batch_mul_same_scalar_prepared(
                        &mut output,
                        &EisensteinScalar::new(&scalar),
                        if capacity == size {
                            &mut fields
                        } else {
                            &mut fields[..capacity]
                        },
                        TaskBudget::new(3).unwrap(),
                        &Pool,
                    );
                    assert_eq!(output, expected, "{n} points with {capacity} fields");
                    assert_eq!(fields[capacity].reduce(), Fp::ONE);
                    let mut normalized = vec![PallasPoint::IDENTITY; n];
                    let mut scratch = vec![Fp::ZERO; n];
                    batch_normalize(&output, &mut normalized, &mut scratch);
                    assert_eq!(
                        normalized,
                        expected
                            .iter()
                            .map(PallasProjective::to_point)
                            .collect::<Vec<_>>()
                    );
                }
            }
        }
    });
    assert!(same_scalar_scratch::<Pallas>(usize::MAX).is_err());
}

#[test]
fn independently_retained_tables_share_ladders_without_copying_entries() {
    let bases: Vec<_> = (1..=129)
        .map(|n| {
            *PallasAffine::GENERATOR
                .mul_projective(&<Fq>::from_u64(n))
                .to_point()
                .as_affine()
                .unwrap()
        })
        .collect();
    let mut storage =
        vec![[RotatedAffinePoint::from_affine(&PallasAffine::GENERATOR); 8]; bases.len()];
    let tables: Vec<_> = bases
        .iter()
        .zip(&mut storage)
        .map(|(base, entries)| {
            EisensteinTable::prepare(
                base,
                entries,
                &mut [PallasProjective::IDENTITY; 8],
                &mut [Fp::ZERO; 8],
            )
        })
        .collect();
    let refs: Vec<_> = tables.iter().rev().collect();
    let scalar = <Fq>::from_u64(89).invert().unwrap();
    let expected: Vec<_> = refs
        .iter()
        .map(|t| t.base().mul_projective(&scalar))
        .collect();
    let size = EisensteinTableBatch::<Pallas, RotatedAffinePoint<Pallas>>::multiplication_scratch(
        refs.len(),
    )
    .unwrap();
    for capacity in [0, size / 2, size] {
        let mut fields = vec![Fp::ONE; capacity + 1];
        let mut output = vec![PallasProjective::IDENTITY; refs.len()];
        EisensteinTableBatch::mul_borrowed(
            &refs,
            &scalar,
            &mut output,
            &mut fields,
            TaskBudget::new(3).unwrap(),
            &SerialExecutor,
        );
        assert_eq!(output, expected);
        assert_eq!(fields[capacity].reduce(), Fp::ONE);
    }
    let mut output = vec![PallasProjective::GENERATOR; refs.len() + 1];
    let mut fields = vec![Fp::ONE; size];
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            EisensteinTableBatch::mul_borrowed(
                &refs,
                &scalar,
                &mut output,
                &mut fields,
                TaskBudget::SERIAL,
                &SerialExecutor,
            )
        }))
        .is_err()
    );
    assert!(output.iter().all(|p| *p == PallasProjective::GENERATOR));
    assert!(fields.iter().all(|f| f.reduce() == Fp::ONE));
    assert_eq!(core::mem::size_of::<PallasAffine>(), 64);
    assert_eq!(core::mem::size_of::<PreparedAffinePoint<Pallas>>(), 96);
    assert_eq!(core::mem::size_of::<RotatedAffinePoint<Pallas>>(), 128);
}
