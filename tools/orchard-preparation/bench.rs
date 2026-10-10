//! Paired, single-worker consumers of archived Pasta and current Udon APIs.
use ff::PrimeField;
use group::{Curve, Group, GroupEncoding};
use pasta_curves::{glv::{Decomposed, Table}, pallas};
use std::{hint::black_box, time::{Duration, Instant}};
use udon::{curve::*, exec::{SerialExecutor, TaskBudget}, field::{Fp, Fq}};

fn measure(name: &str, n: usize, mut f: impl FnMut(usize)) {
    for i in 0..8 { f(i % 16); }
    let start = Instant::now();
    let mut iterations = 0;
    while start.elapsed() < Duration::from_millis(60) {
        for i in 0..16 { f(i); }
        iterations += 16;
    }
    println!("{name},{n},{iterations},{}", start.elapsed().as_nanos());
}

fn main() {
    let candidate = std::env::args().nth(1).unwrap() == "candidate";
    let bytes = std::fs::read(std::env::args_os().nth(2).unwrap()).unwrap();
    let scalar_bytes: Vec<[u8; 32]> = bytes.chunks_exact(96).skip(4).take(16).map(|c| c[..32].try_into().unwrap()).collect();
    let base_bytes: Vec<[u8; 32]> = bytes.chunks_exact(96).skip(4).map(|c| c[32..64].try_into().unwrap()).collect();
    for n in [1, 8, 16, 32, 50, 64, 100, 128, 256, 512, 2048] {
        if candidate {
            let scalars: Vec<_> = scalar_bytes.iter().map(|b| <Fq>::from_bytes(*b).unwrap()).collect();
            let prepared: Vec<_> = scalars.iter().map(EisensteinScalar::<Pallas>::new).collect();
            let bases: Vec<_> = base_bytes.iter().cycle().take(n).map(|b| PallasAffine::from_bytes(*b).unwrap()).collect();
            let r = EisensteinTableBatch::<Pallas, RotatedAffinePoint<Pallas>>::requirements(n).unwrap();
            let mut entries = vec![RotatedAffinePoint::from_affine(&bases[0]); r.table_entries];
            let mut projective = vec![PallasProjective::IDENTITY; r.projective_scratch];
            let mut fields = vec![Fp::ZERO; r.field_scratch.max(EisensteinTableBatch::<Pallas>::multiplication_scratch(n).unwrap()).max(n)];
            let tables = EisensteinTableBatch::prepare(&bases, &mut entries, &mut projective, &mut fields, TaskBudget::SERIAL, &SerialExecutor);
            let mut output = vec![PallasProjective::IDENTITY; n];
            let mut affine = vec![PallasPoint::IDENTITY; n];
            let retained: Vec<_> = (0..n).map(|i| tables.get(i).unwrap()).collect();
            let refs: Vec<_> = retained.iter().collect();
            measure("retained", n, |i| {
                EisensteinTableBatch::mul_borrowed_prepared(black_box(&refs), black_box(&prepared[i]), &mut output, &mut fields, TaskBudget::SERIAL, &SerialExecutor);
                batch_normalize(&output, &mut affine, &mut fields);
                black_box(&affine);
            });
            drop(refs); drop(retained);
            measure("prepare", n, |_| {
                black_box(EisensteinTableBatch::prepare(black_box(&bases), &mut entries, &mut projective, &mut fields, TaskBudget::SERIAL, &SerialExecutor));
            });
            measure("prepare_use", n, |i| {
                let tables = EisensteinTableBatch::prepare(black_box(&bases), &mut entries, &mut projective, &mut fields, TaskBudget::SERIAL, &SerialExecutor);
                tables.mul_prepared(black_box(&prepared[i]), &mut output, &mut fields, TaskBudget::SERIAL, &SerialExecutor);
                batch_normalize(&output, &mut affine, &mut fields);
                black_box(&affine);
            });
            let inputs: Vec<_> = bases.iter().map(|p| p.to_projective().double()).collect();
            let mut fields = vec![Fp::ZERO; same_scalar_scratch::<Pallas>(n).unwrap().max(n)];
            measure("projective_affine", n, |i| {
                output.copy_from_slice(&inputs);
                batch_mul_same_scalar(&mut output, black_box(&scalars[i]), &mut fields, TaskBudget::SERIAL, &SerialExecutor);
                batch_normalize(&output, &mut affine, &mut fields);
                black_box(&affine);
            });
        } else {
            let scalars: Vec<_> = scalar_bytes.iter().map(|b| pallas::Scalar::from_repr(*b).unwrap()).collect();
            let prepared: Vec<_> = scalars.iter().map(Decomposed::<pallas::Point>::new).collect();
            let bases: Vec<_> = base_bytes.iter().cycle().take(n).map(|b| pallas::Point::from_bytes(b).unwrap()).collect();
            let tables = Table::batch(&bases);
            let refs: Vec<_> = tables.iter().collect();
            let mut affine = vec![pallas::Point::identity().to_affine(); n];
            measure("retained", n, |i| {
                let output = Table::mul_decomposed_batch(black_box(&refs), black_box(&prepared[i]));
                pallas::Point::batch_normalize(&output, &mut affine);
                black_box(&affine);
            });
            measure("prepare", n, |_| { black_box(Table::batch(black_box(&bases))); });
            measure("prepare_use", n, |i| {
                let tables = Table::batch(black_box(&bases));
                let refs: Vec<_> = tables.iter().collect();
                let output = Table::mul_decomposed_batch(&refs, black_box(&prepared[i]));
                pallas::Point::batch_normalize(&output, &mut affine);
                black_box(&affine);
            });
            let inputs: Vec<_> = bases.iter().map(pallas::Point::double).collect();
            let mut output = inputs.clone();
            measure("projective_affine", n, |i| {
                output.copy_from_slice(&inputs);
                // Match the archived implementation's size-based dispatch:
                // its effective-affine kernel alone is not the small-batch path.
                if n >= 32 {
                    pasta_curves::glv::bench_internals::batch_mul_same_scalar_effective(&mut output, black_box(&scalars[i]));
                } else {
                    pasta_curves::glv::bench_internals::batch_mul_same_scalar_normalized(&mut output, black_box(&scalars[i]));
                }
                pallas::Point::batch_normalize(&output, &mut affine);
                black_box(&affine);
            });
        }
    }
}
