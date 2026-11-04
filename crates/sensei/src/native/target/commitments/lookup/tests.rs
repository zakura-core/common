use super::*;
use crate::resource_tests::PoolExecutor;
use udon::exec::TaskBudget;

impl Parameters {
    /// Fixture census and forced recipes share exactly the production planner.
    pub(crate) fn measure_lookup_pair_recipes(
        &self,
        pairs: &[LookupCommitPair<'_>],
        execution: Execution<'_>,
    ) {
        for (index, pair) in pairs.iter().enumerate() {
            let input = Polynomial::column(self, pair.input_runs, pair.input).unwrap();
            let table = Polynomial::column(self, pair.table_runs, pair.table).unwrap();
            let difference = Polynomial::new(
                Bases::Prepared(&self.srs.lagrange_generators),
                pair.input
                    .iter()
                    .zip(pair.table.iter())
                    .enumerate()
                    .map(|(row, (i, t))| (row as u32, i.sub(t))),
            );
            eprintln!(
                "LOOKUP_SHAPE pair={index} runs={}/{} support={}/{}/{} cost={}/{}/{} sorted={}/{} recipe={:?}",
                pair.input_runs.len(),
                pair.table_runs.len(),
                input.scalars.len(),
                table.scalars.len(),
                difference.scalars.len(),
                input.cost,
                table.cost,
                difference.cost,
                input.sorted.is_some(),
                table.sorted.is_some(),
                recipe(input.cost, table.cost, difference.cost),
            );
        }
        let mut workspace = MsmWorkspace::new();
        let expected = self
            .commit_lookup_pairs_with_recipe::<true>(
                pairs,
                &mut workspace,
                execution,
                Some(Recipe::Independent),
            )
            .unwrap();
        let mut times: [Vec<_>; 5] = std::array::from_fn(|_| Vec::new());
        // Rotate recipe order to reduce drift; every result is checked outside
        // the timed region. The production proof benchmark measures the full
        // stage, including compression, permutation, and transcript writes.
        for repetition in 0..103 {
            for offset in 0..5 {
                let index = (repetition + offset) % 5;
                let forced = [
                    None,
                    Some(Recipe::Independent),
                    Some(Recipe::InputDifference),
                    Some(Recipe::TableDifference),
                    None,
                ][index];
                let start = std::time::Instant::now();
                let actual = if index == 4 {
                    self.commit_lookup_pairs_with_recipe::<false>(
                        pairs,
                        &mut workspace,
                        execution,
                        forced,
                    )
                } else {
                    self.commit_lookup_pairs_with_recipe::<true>(
                        pairs,
                        &mut workspace,
                        execution,
                        forced,
                    )
                }
                .unwrap();
                let elapsed = start.elapsed();
                assert_eq!(actual, expected);
                if repetition >= 3 {
                    times[index].push(elapsed);
                }
            }
        }
        for (name, mut times) in [
            "auto",
            "independent",
            "input_difference",
            "table_difference",
            "auto_interval",
        ]
        .into_iter()
        .zip(times)
        {
            times.sort_unstable();
            eprintln!(
                "LOOKUP_RECIPE recipe={name} median_ns={}",
                times[times.len() / 2].as_nanos()
            );
        }
    }
}

fn runs(column: &[Fp]) -> Vec<(u32, Fp)> {
    let mut runs = Vec::new();
    for (row, value) in column[..USABLE_ROWS_END].iter().enumerate() {
        if row == 0 || value.reduce() != column[row - 1].reduce() {
            runs.push((row as u32, *value));
        }
    }
    runs
}

fn arbitrary(seed: usize) -> Fp {
    <Fp>::from_u64(seed as u64 + 17).invert().unwrap()
}

#[test]
fn every_pair_recipe_matches_dense_with_independent_tails_and_blinds() {
    let parameters = crate::test_codec::target().parameters();
    let mut cases = Vec::new();
    for shape in 0..6 {
        let mut input = vec![<Fp>::ZERO; N];
        let mut table = input.clone();
        for row in 0..USABLE_ROWS_END {
            let value = match shape {
                0 => <Fp>::ZERO,
                1 => <Fp>::from_u64(1023),
                2 => <Fp>::from_u64((row / 3 % 1024) as u64),
                3 => <Fp>::from_u64((row % 1024) as u64).neg(),
                _ => arbitrary(row / 5),
            };
            input[row] = value;
            table[row] = if row % 7 == 0 { arbitrary(row) } else { value };
        }
        if shape == 0 {
            table.fill(<Fp>::ZERO);
        }
        if shape == 5 {
            table.copy_from_slice(&input);
        }
        for row in USABLE_ROWS_END..N {
            input[row] = arbitrary(2 * row + shape);
            table[row] = if shape == 5 {
                input[row]
            } else {
                arbitrary(3 * row + shape)
            };
        }
        cases.push((SharedPoly::new(input), SharedPoly::new(table)));
    }
    let run_pairs = cases
        .iter()
        .map(|(i, t)| (runs(i), runs(t)))
        .collect::<Vec<_>>();
    let pairs = cases
        .iter()
        .zip(&run_pairs)
        .enumerate()
        .map(
            |(index, ((input, table), (input_runs, table_runs)))| LookupCommitPair {
                input,
                table,
                input_runs,
                table_runs,
                input_blind: arbitrary(index),
                table_blind: if index == 5 {
                    arbitrary(index)
                } else {
                    arbitrary(index + 100)
                },
            },
        )
        .collect::<Vec<_>>();
    let oracle_jobs = pairs
        .iter()
        .flat_map(|pair| {
            [
                (pair.input, &pair.input_blind),
                (pair.table, &pair.table_blind),
            ]
        })
        .collect::<Vec<_>>();
    let expected = parameters
        .commit_lagrange_batch_projective(
            &oracle_jobs,
            &mut MsmWorkspace::new(),
            crate::test_codec::execution(),
        )
        .unwrap();
    let mut workspace = MsmWorkspace::new();
    for workers in [1, 10, 16] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .build()
            .unwrap();
        let executor = PoolExecutor(&pool);
        let execution = Execution::new(&executor, TaskBudget::new(workers).unwrap());
        for recipe in [
            None,
            Some(Recipe::Independent),
            Some(Recipe::InputDifference),
            Some(Recipe::TableDifference),
        ] {
            for _ in 0..2 {
                let actual = pool
                    .install(|| {
                        parameters.commit_lookup_pairs_with_recipe::<true>(
                            &pairs,
                            &mut workspace,
                            execution,
                            recipe,
                        )
                    })
                    .unwrap();
                assert_eq!(actual, expected, "workers={workers}, recipe={recipe:?}");
            }
        }
    }
}

#[test]
fn pair_recipes_validate_both_columns_before_selecting_storage() {
    let parameters = crate::test_codec::target().parameters();
    let column = SharedPoly::new(vec![Fp::ZERO; N]);
    let valid = [(0, Fp::ZERO)];
    for invalid in [
        vec![],
        vec![(1, Fp::ZERO)],
        vec![(0, Fp::ZERO), (0, Fp::ONE)],
        vec![(0, Fp::ZERO), (USABLE_ROWS_END as u32, Fp::ONE)],
    ] {
        for (input_runs, table_runs) in [(&invalid[..], &valid[..]), (&valid[..], &invalid[..])] {
            let pair = LookupCommitPair {
                input: &column,
                table: &column,
                input_runs,
                table_runs,
                input_blind: Fp::ONE,
                table_blind: Fp::ONE,
            };
            for recipe in [
                Recipe::Independent,
                Recipe::InputDifference,
                Recipe::TableDifference,
            ] {
                assert!(matches!(
                    parameters.commit_lookup_pairs_with_recipe::<true>(
                        core::slice::from_ref(&pair),
                        &mut MsmWorkspace::new(),
                        crate::test_codec::execution(),
                        Some(recipe),
                    ),
                    Err(TargetError::Dimension)
                ));
            }
        }
    }
}

#[test]
fn cost_comparison_preserves_ties_and_both_difference_directions() {
    assert_eq!(recipe(100, 100, 100), Recipe::Independent);
    assert_eq!(recipe(100, 200, 190), Recipe::Independent);
    assert_eq!(recipe(100, 200, 30), Recipe::InputDifference);
    assert_eq!(recipe(200, 100, 30), Recipe::TableDifference);
    assert_eq!(
        scalar_cost(&<Fp>::from_u64(17)),
        scalar_cost(&<Fp>::from_u64(17).neg())
    );
    assert!(scalar_cost(&arbitrary(7)) > scalar_cost(&<Fp>::from_u64(1023)));
}

#[test]
fn sorted_suffix_commitments_cover_boundaries_gaps_and_maximum_variation() {
    let parameters = crate::test_codec::target().parameters();
    let profiles = [
        vec![(0, 0)],
        vec![(0, 1023)],
        vec![(0, 0), (1, 1023)],
        vec![(0, 37), (USABLE_ROWS_END as u32 - 1, 1003)],
        (0..1024)
            .map(|value| ((value * USABLE_ROWS_END / 1024) as u32, value as u64))
            .collect(),
    ];
    for profile in profiles {
        let runs = profile
            .iter()
            .map(|&(row, value)| (row, <Fp>::from_u64(value)))
            .collect::<Vec<_>>();
        let prefix = SortedPrefix::from_runs(&runs).unwrap();
        let mut column = vec![<Fp>::ZERO; N];
        for (index, &(row, value)) in runs.iter().enumerate() {
            let end = runs
                .get(index + 1)
                .map_or(USABLE_ROWS_END, |&(row, _)| row as usize);
            column[row as usize..end].fill(value);
        }
        for (index, value) in column[USABLE_ROWS_END..].iter_mut().enumerate() {
            *value = if index % 2 == 0 {
                arbitrary(index)
            } else {
                <Fp>::ZERO
            };
        }
        let blind = arbitrary(123);
        let expected = parameters
            .commit_lagrange_projective(
                &column,
                &blind,
                &mut MsmWorkspace::new(),
                crate::test_codec::execution(),
            )
            .unwrap();
        let mut correction = vec![<Fp>::ZERO; N];
        for row in USABLE_ROWS_END..N {
            correction[row] = column[row].sub(&prefix.last);
        }
        let tail = parameters
            .commit_lagrange_projective(
                &correction,
                &blind,
                &mut MsmWorkspace::new(),
                crate::test_codec::execution(),
            )
            .unwrap();
        assert_eq!(
            parameters.sorted_lookup_suffixes.commit(&prefix).add(&tail),
            expected
        );
        let interval = Polynomial::interval(parameters, &runs, &column).unwrap();
        assert_eq!(
            prefix.interval_cost
                + column[USABLE_ROWS_END..]
                    .iter()
                    .filter(|value| !value.is_zero())
                    .map(scalar_cost)
                    .sum::<usize>(),
            interval.cost
        );
        let selected = Polynomial::column(parameters, &runs, &column).unwrap();
        if runs.len() == 1 {
            assert!(
                selected.sorted.is_none(),
                "constant prefixes retain interval MSMs"
            );
        }
        if runs.len() == 1024 {
            assert!(selected.sorted.is_some());
        }
    }
}

#[test]
fn sorted_prefix_rejects_malformed_or_non_ten_bit_profiles() {
    for profile in [
        vec![],
        vec![(1, 0)],
        vec![(0, 1024)],
        vec![(0, 7), (1, 6)],
        vec![(0, 0), (0, 1)],
        vec![(0, 1), (1, 1)],
        vec![(0, 0), (USABLE_ROWS_END as u32, 1)],
    ] {
        let runs = profile
            .into_iter()
            .map(|(row, value)| (row, <Fp>::from_u64(value)))
            .collect::<Vec<_>>();
        assert!(SortedPrefix::from_runs(&runs).is_none());
    }
    assert!(SortedPrefix::from_runs(&[(0, <Fp>::ONE.neg())]).is_none());
    assert!(SortedPrefix::from_runs(&[(0, arbitrary(9))]).is_none());
    // Montgomery representatives in the upper loose half still encode a u10.
    let mut limbs = <Fp>::from_u64(1023).reduce().montgomery_limbs();
    let modulus = <udon::field::PallasBase as udon::field::PrimeModulus>::MODULUS;
    let mut carry = 0u128;
    for (limb, modulus) in limbs.iter_mut().zip(modulus) {
        carry += u128::from(*limb) + u128::from(modulus);
        *limb = carry as u64;
        carry >>= 64;
    }
    let loose = <Fp>::from_montgomery_limbs(limbs);
    assert_eq!(
        SortedPrefix::from_runs(&[(0, loose)])
            .unwrap()
            .last
            .reduce(),
        <Fp>::from_u64(1023).reduce()
    );
}
