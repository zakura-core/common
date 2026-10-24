//! Focused screens for changes that alter arithmetic or storage strategy.

use super::{
    commitment::{MsmWorkspace, normalized},
    worker::Execution,
};
use crate::resource_tests::PoolExecutor;
use std::{hint::black_box, time::Instant};
use udon::{
    curve::{EisensteinTableBatch, Vesta, VestaAffine, VestaProjective},
    exec::{ExecutionOptions, Executor, SerialExecutor, TaskBudget},
    fft::{Domain, ElementOrder, Tables, TablesMut, VanishingDivision},
    field::{Fp, Fq},
    msm::{Bases, Input, PreparedScalars, ScalarStorage, Scratch, SharedScalarInput},
};

fn random_fields(count: usize) -> Vec<Fp> {
    let mut value = <Fp>::from_u64(0x9e37_79b9_7f4a_7c15);
    (0..count)
        .map(|_| {
            value = value.square().add(&<Fp>::from_u64(17));
            value
        })
        .collect()
}

#[test]
#[ignore = "isolated quotient arithmetic benchmark"]
fn measure_fused_division() {
    const N: usize = sensei_shared::N;
    let target = crate::test_codec::target();
    let options = ExecutionOptions::default().with_task_budget(TaskBudget::SERIAL);
    let samples = random_fields(8 * N);
    let domain = Domain::for_size(samples.len()).unwrap();
    let mut twiddles = vec![Fp::ZERO; samples.len() / 2];
    TablesMut {
        forward: Some(&mut twiddles),
        inverse: None,
        inverse_finish: None,
    }
    .prepare(domain.subgroup());
    let forward = Tables {
        forward: Some(&twiddles),
        inverse: None,
        inverse_finish: None,
    }
    .bind(domain.subgroup());
    let inverse = target.fft().class_plan(3);
    let division = VanishingDivision::new(domain, &<Fp>::ZETA, N).unwrap();
    let mut factors = [Fp::ZERO; 8];
    let factors = division.prepare_factors(&mut factors, &mut [Fp::ZERO; 8]);
    let mut ordinary = samples.clone();
    let mut transformed = samples.clone();
    let mut output = vec![Fp::ZERO; samples.len()];
    // Warm both transforms and exclude test input resets from the timings.
    for repetition in 0..13 {
        ordinary.copy_from_slice(&samples);
        transformed.copy_from_slice(&samples);
        let started = Instant::now();
        factors.divide_in_place(&mut ordinary, ElementOrder::Natural);
        inverse
            .inverse(&mut ordinary, options, &SerialExecutor, &mut [])
            .unwrap();
        let ordinary_ns = started.elapsed().as_nanos();
        let started = Instant::now();
        forward
            .forward(&mut transformed, options, &SerialExecutor, &mut [])
            .unwrap();
        division.write_pieces(
            &transformed,
            ElementOrder::Natural,
            &mut output.chunks_exact_mut(N).collect::<Vec<_>>(),
            &mut [Fp::ZERO; 8],
        );
        let fused_ns = started.elapsed().as_nanos();
        assert!(
            ordinary
                .iter()
                .zip(&output)
                .all(|(a, b)| a.reduce() == b.reduce())
        );
        if repetition > 0 {
            eprintln!("SENSEI_DIVISION_NS ordinary={ordinary_ns} fused={fused_ns}");
        }
        black_box(&output);
    }
}

#[derive(Default)]
struct MatrixScratch {
    records: Vec<ScalarStorage<Vesta>>,
    scalars: Vec<ScalarStorage<Vesta>>,
    digits: Vec<u8>,
    affine: Vec<VestaAffine>,
    projective: Vec<VestaProjective>,
    field: Vec<Fq>,
    indices: Vec<usize>,
}

impl MatrixScratch {
    fn blocks(
        &mut self,
        bases: Bases<'_, Vesta>,
        coefficients: &[Fp],
        outputs: &mut [VestaProjective],
        execution: Execution<'_>,
    ) {
        self.records.resize(coefficients.len(), ScalarStorage::ZERO);
        let prepared = PreparedScalars::prepare(
            coefficients,
            &mut self.records,
            execution.budget,
            &execution,
        );
        let input =
            SharedScalarInput::new(bases, prepared, outputs.len(), 2 * coefficients.len(), 1)
                .unwrap();
        let options = ExecutionOptions::default().with_task_budget(execution.budget);
        let r = input.requirements(options).unwrap();
        self.scalars.resize(r.scalars(), ScalarStorage::ZERO);
        self.digits.resize(r.digits(), 0);
        self.affine.resize(r.affine(), VestaAffine::GENERATOR);
        self.projective
            .resize(r.projective(), VestaProjective::IDENTITY);
        self.field.resize(r.field(), Fq::ZERO);
        self.indices.resize(r.indices(), 0);
        input
            .execute(
                outputs,
                options,
                &execution,
                Scratch::new(
                    &mut self.scalars,
                    &mut self.digits,
                    &mut self.affine,
                    &mut self.projective,
                    &mut self.field,
                    &mut self.indices,
                ),
            )
            .unwrap();
    }
}

#[test]
#[ignore = "isolated virtual IPA round benchmark"]
fn measure_virtual_ipa_blocks() {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(16)
        .build()
        .unwrap();
    let executor = PoolExecutor(&pool);
    let execution = Execution::new(&executor, TaskBudget::new(16).unwrap());
    let inner = Execution::new(&executor, TaskBudget::new(8).unwrap());
    let bases = crate::test_codec::target()
        .parameters()
        .coefficient_generators();
    // One later virtual round in each of the three materialized banks.
    for (size, half) in [(2048, 256), (256, 32), (32, 4)] {
        let bases = if size == 2048 {
            crate::test_codec::target().parameters().coefficient_bases()
        } else {
            Bases::Prepared(&bases[..size])
        };
        let coefficients = random_fields(2 * half);
        let weights = random_fields(size / half);
        let indices: [Vec<u32>; 2] = core::array::from_fn(|side| {
            (0..size)
                .filter(|m| m / half % 2 == side)
                .map(|m| m as u32)
                .collect()
        });
        let mut expanded = [vec![Fp::ZERO; size / 2], vec![Fp::ZERO; size / 2]];
        let block_weights: [Vec<_>; 2] =
            core::array::from_fn(|side| weights.iter().skip(side).step_by(2).copied().collect());
        let mut direct_workspace = MsmWorkspace::new();
        let mut outer_workspace = MsmWorkspace::new();
        let mut sides = core::array::from_fn::<_, 2, _>(|_| {
            (
                MatrixScratch::default(),
                vec![VestaProjective::IDENTITY; size / (2 * half)],
            )
        });
        for repetition in 0..13 {
            let started = Instant::now();
            for side in 0..2 {
                for (value, &index) in expanded[side].iter_mut().zip(&indices[side]) {
                    let m = index as usize;
                    *value = weights[m / half].mul(&coefficients[(1 - side) * half + m % half]);
                }
            }
            let inputs = core::array::from_fn::<_, 2, _>(|side| {
                Input::indexed(bases, &indices[side], &expanded[side]).unwrap()
            });
            let mut direct = [VestaProjective::IDENTITY; 2];
            direct_workspace
                .prepare(&inputs, execution.budget)
                .unwrap()
                .execute(&mut direct, &execution)
                .unwrap();
            let direct_ns = started.elapsed().as_nanos();
            let started = Instant::now();
            let run_side =
                |side: usize, (scratch, blocks): &mut (MatrixScratch, Vec<VestaProjective>)| {
                    let offset = side * half;
                    let bases = match bases {
                        Bases::Prepared(points) => Bases::Prepared(&points[offset..]),
                        Bases::CompactPrepared(tables) => Bases::CompactPrepared(
                            EisensteinTableBatch::bind(&tables.as_slice()[8 * offset..]),
                        ),
                        _ => unreachable!(),
                    };
                    scratch.blocks(
                        bases,
                        &coefficients[(1 - side) * half..(2 - side) * half],
                        blocks,
                        inner,
                    );
                    normalized(blocks)
                };
            let [left, right] = &mut sides;
            let (left, right) = execution.join(|| run_side(0, left), || run_side(1, right));
            let points = [left, right];
            let inputs = core::array::from_fn::<_, 2, _>(|side| {
                Input::new(Bases::Points(&points[side]), &block_weights[side])
            });
            let mut factored = [VestaProjective::IDENTITY; 2];
            outer_workspace
                .prepare(&inputs, execution.budget)
                .unwrap()
                .execute(&mut factored, &execution)
                .unwrap();
            let factored_ns = started.elapsed().as_nanos();
            assert_eq!(normalized(&direct), normalized(&factored));
            if repetition > 0 {
                eprintln!(
                    "SENSEI_VIRTUAL_IPA_NS size={size} half={half} direct={direct_ns} factored={factored_ns}"
                );
            }
            black_box(factored);
        }
    }
}
