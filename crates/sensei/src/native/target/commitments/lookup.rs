//! Joint commitments to permuted lookup columns.
//!
//! The permutation makes many input and table cells equal. Committing their
//! difference can replace either column while retaining both original columns
//! for the product argument and openings. Blinds obey the same linear relation.

use super::*;

mod sorted;
#[cfg(test)]
mod tests;
pub(crate) use sorted::SuffixGenerators;
use sorted::{SortedAnalysis, SortedPrefix};

pub(crate) struct LookupCommitPair<'a> {
    pub(crate) input: &'a SharedPoly,
    pub(crate) table: &'a SharedPoly,
    pub(crate) input_runs: &'a [(u32, Fp)],
    pub(crate) table_runs: &'a [(u32, Fp)],
    pub(crate) input_blind: Fp,
    pub(crate) table_blind: Fp,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Recipe {
    Independent,
    InputDifference,
    TableDifference,
}

/// Support and signed-window cost, before committing storage to a recipe.
#[derive(Clone, Copy)]
struct Analysis {
    cost: usize,
    nonzero: usize,
    sorted: Option<SortedAnalysis>,
}

impl Analysis {
    fn scalars(values: impl IntoIterator<Item = Fp>) -> Self {
        let mut cost = 0;
        let mut nonzero = 0;
        for value in values {
            if !value.is_zero() {
                cost += scalar_cost(&value);
                nonzero += 1;
            }
        }
        Self {
            cost,
            nonzero,
            sorted: None,
        }
    }

    fn column<const SORTED: bool>(
        parameters: &Parameters,
        runs: &[(u32, Fp)],
        dense: &[Fp],
    ) -> Result<Self, TargetError> {
        let intervals = interval_pairs(parameters, runs, dense)?;
        if SORTED && let Some(prefix) = SortedAnalysis::new(runs) {
            let tail = &dense[USABLE_ROWS_END..];
            let interval_cost = prefix.interval_cost + Self::scalars(tail.iter().copied()).cost;
            let mut sorted = Self::scalars(tail.iter().map(|value| value.sub(&prefix.last)));
            sorted.cost += prefix.additions;
            if sorted.cost * 8 < interval_cost * 7 {
                sorted.sorted = Some(prefix);
                return Ok(sorted);
            }
        }
        Ok(Self::scalars(intervals.map(|(_, value)| value)))
    }
}

/// Validates even a column that the chosen pair recipe will not materialize.
fn interval_pairs<'a>(
    parameters: &Parameters,
    runs: &'a [(u32, Fp)],
    dense: &'a [Fp],
) -> Result<impl Iterator<Item = (u32, Fp)> + 'a, TargetError> {
    if dense.len() != N
        || parameters.lagrange_prefix_sums.len() != N
        || runs.first().is_none_or(|&(row, _)| row != 0)
        || runs
            .last()
            .is_none_or(|&(row, _)| row as usize >= USABLE_ROWS_END)
        || runs.windows(2).any(|pair| pair[0].0 >= pair[1].0)
    {
        return Err(TargetError::Dimension);
    }
    let last = runs.last().expect("validated nonempty runs").1;
    Ok(runs
        .windows(2)
        .map(|pair| (pair[1].0 - 1, pair[0].1.sub(&pair[1].1)))
        .chain(core::iter::once((USABLE_ROWS_END as u32 - 1, last)))
        .chain(
            dense[USABLE_ROWS_END..]
                .iter()
                .enumerate()
                .map(|(row, &value)| ((USABLE_ROWS_END + row) as u32, value)),
        ))
}

/// Only the two selected polynomials acquire indexed MSM storage.
struct Polynomial<'a> {
    bases: Bases<'a, Vesta>,
    indices: Vec<u32>,
    scalars: Vec<Fp>,
    #[cfg(test)]
    cost: usize,
    sorted: Option<SortedPrefix>,
}

impl<'a> Polynomial<'a> {
    fn materialize(
        bases: Bases<'a, Vesta>,
        pairs: impl IntoIterator<Item = (u32, Fp)>,
        analysis: Analysis,
    ) -> Self {
        let mut indices = Vec::with_capacity(analysis.nonzero);
        let mut scalars = Vec::with_capacity(analysis.nonzero);
        for (index, scalar) in pairs {
            if !scalar.is_zero() {
                indices.push(index);
                scalars.push(scalar);
            }
        }
        Self {
            bases,
            indices,
            scalars,
            #[cfg(test)]
            cost: analysis.cost,
            sorted: None,
        }
    }

    fn materialize_column(
        parameters: &'a Parameters,
        runs: &[(u32, Fp)],
        dense: &[Fp],
        analysis: Analysis,
    ) -> Result<Self, TargetError> {
        if let Some(prefix) = analysis.sorted {
            let mut polynomial = Self::materialize(
                parameters.lagrange_bases(),
                dense[USABLE_ROWS_END..]
                    .iter()
                    .enumerate()
                    .map(|(row, value)| ((USABLE_ROWS_END + row) as u32, value.sub(&prefix.last))),
                analysis,
            );
            polynomial.sorted = Some(prefix.materialize(runs));
            Ok(polynomial)
        } else {
            Ok(Self::materialize(
                Bases::Prepared(&parameters.lagrange_prefix_sums),
                interval_pairs(parameters, runs, dense)?,
                analysis,
            ))
        }
    }

    #[cfg(test)]
    fn new(bases: Bases<'a, Vesta>, pairs: impl IntoIterator<Item = (u32, Fp)>) -> Self {
        let pairs = pairs.into_iter().collect::<Vec<_>>();
        let analysis = Analysis::scalars(pairs.iter().map(|&(_, scalar)| scalar));
        Self::materialize(bases, pairs, analysis)
    }

    #[cfg(test)]
    fn interval(
        parameters: &'a Parameters,
        runs: &[(u32, Fp)],
        dense: &[Fp],
    ) -> Result<Self, TargetError> {
        let analysis = Analysis::column::<false>(parameters, runs, dense)?;
        Self::materialize_column(parameters, runs, dense, analysis)
    }

    #[cfg(test)]
    fn column(
        parameters: &'a Parameters,
        runs: &[(u32, Fp)],
        dense: &[Fp],
    ) -> Result<Self, TargetError> {
        let analysis = Analysis::column::<true>(parameters, runs, dense)?;
        Self::materialize_column(parameters, runs, dense, analysis)
    }

    fn term(self) -> (CommitmentTerm<'a>, Option<SortedPrefix>) {
        (
            CommitmentTerm::Indexed {
                bases: self.bases,
                indices: Column::new(self.indices),
                scalars: Column::new(self.scalars),
            },
            self.sorted,
        )
    }
}

/// A small signed coefficient uses few nonzero windows; general field values
/// need both GLV halves. This is a conservative comparison of representations,
/// not a prediction of wall time or a replacement for Udon's kernel selection.
fn scalar_cost(scalar: &Fp) -> usize {
    let positive = scalar
        .to_canonical_uint()
        .highest_set_bit()
        .map_or(0, |bit| bit + 1);
    let bits = if positive <= 128 {
        positive
    } else {
        scalar
            .neg()
            .to_canonical_uint()
            .highest_set_bit()
            .map_or(0, |bit| bit + 1)
    };
    1 + if bits <= 128 { bits.div_ceil(4) } else { 64 }
}

fn recipe(input: usize, table: usize, difference: usize) -> Recipe {
    let independent = input + table;
    let input_difference = input + difference + 1;
    let table_difference = table + difference + 1;
    // Keep the existing route for ties and small estimated savings: gathering
    // the difference and reconstructing a point must also pay for themselves.
    if input_difference.min(table_difference) * 8 >= independent * 7 {
        Recipe::Independent
    } else if input_difference <= table_difference {
        Recipe::InputDifference
    } else {
        Recipe::TableDifference
    }
}

impl Parameters {
    pub(crate) fn commit_lookup_pairs_projective(
        &self,
        pairs: &[LookupCommitPair<'_>],
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<Vec<VestaProjective>, TargetError> {
        self.commit_lookup_pairs_with_recipe::<true>(pairs, workspace, execution, None)
    }

    fn commit_lookup_pairs_with_recipe<const SORTED: bool>(
        &self,
        pairs: &[LookupCommitPair<'_>],
        workspace: &mut MsmWorkspace,
        execution: Execution<'_>,
        forced: Option<Recipe>,
    ) -> Result<Vec<VestaProjective>, TargetError> {
        let mut terms = Vec::with_capacity(4 * pairs.len());
        let mut recipes = Vec::with_capacity(pairs.len());
        let mut prefixes = Vec::new();
        for pair in pairs {
            if pair.input.len() != N || pair.table.len() != N {
                return Err(TargetError::Dimension);
            }
            let input = Analysis::column::<SORTED>(self, pair.input_runs, pair.input)?;
            let table = Analysis::column::<SORTED>(self, pair.table_runs, pair.table)?;
            let difference_values = || {
                pair.input
                    .iter()
                    .zip(pair.table.iter())
                    .enumerate()
                    .map(|(row, (input, table))| (row as u32, input.sub(table)))
            };
            let difference = Analysis::scalars(difference_values().map(|(_, value)| value));
            let selected =
                forced.unwrap_or_else(|| recipe(input.cost, table.cost, difference.cost));
            let input = || Polynomial::materialize_column(self, pair.input_runs, pair.input, input);
            let table = || Polynomial::materialize_column(self, pair.table_runs, pair.table, table);
            let difference =
                || Polynomial::materialize(self.lagrange_bases(), difference_values(), difference);
            let difference_blind = pair.input_blind.sub(&pair.table_blind);
            let (first, first_blind, second, second_blind) = match selected {
                Recipe::Independent => (input()?, pair.input_blind, table()?, pair.table_blind),
                Recipe::InputDifference => {
                    (input()?, pair.input_blind, difference(), difference_blind)
                }
                Recipe::TableDifference => {
                    (table()?, pair.table_blind, difference(), difference_blind)
                }
            };
            for (polynomial, blind) in [(first, first_blind), (second, second_blind)] {
                let (term, prefix) = polynomial.term();
                if let Some(prefix) = prefix {
                    prefixes.push((terms.len(), prefix));
                }
                terms.push(term);
                terms.push(CommitmentTerm::Fixed {
                    base: self.prepared_blind_generator(),
                    scalar: blind,
                });
            }
            recipes.push(selected);
        }
        let (mut points, prefixes) = execute_with_side_jobs(
            workspace,
            execution,
            &terms,
            prefixes,
            |(index, prefix), _| (index, self.sorted_lookup_suffixes.commit(&prefix)),
        )
        .ok_or(TargetError::Dimension)?;
        if points.len() != 4 * pairs.len() {
            return Err(TargetError::Dimension);
        }
        for (index, prefix) in prefixes {
            points[index] = points[index].add(&prefix);
        }
        for (index, recipe) in recipes.into_iter().enumerate() {
            let [first, first_blind, second, second_blind] =
                core::array::from_fn(|offset| points[4 * index + offset]);
            let first = first.add(&first_blind);
            let second = second.add(&second_blind);
            let (input, table) = match recipe {
                Recipe::Independent => (first, second),
                Recipe::InputDifference => (first, first.add(&second.neg())),
                Recipe::TableDifference => (first.add(&second), first),
            };
            points[2 * index] = input;
            points[2 * index + 1] = table;
        }
        points.truncate(2 * pairs.len());
        Ok(points)
    }
}
