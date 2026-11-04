//! Polynomial evaluation jobs for [`super::opening`] and [`super::ipa`].
//!
//! Dense jobs share cached powers for their evaluation points. Linear masks
//! and precomputed instance values fill their result slots directly; the
//! caller receives values in job order for its transcript writes.

use super::opening::PolySource;
use crate::Error;
use crate::native::buffer::Buffer;
use crate::native::field::{Fp, PallasBase};
use crate::native::target::N;
use crate::native::worker::Execution;
use alloc::vec::Vec;
use udon::polynomial::EvaluationPlan;

/// Reusable nonconstant challenge powers for the coefficient polynomials opened
/// at the small fixed set of rotated evaluation points.
pub(super) struct EvaluationPowerCache {
    pub(super) entries: Vec<(Fp, Buffer<Fp>)>,
}

impl EvaluationPowerCache {
    pub(super) fn new() -> Self {
        Self {
            entries: Vec::with_capacity(4),
        }
    }

    fn prepare(&mut self, execution: Execution<'_>, point: &Fp) -> usize {
        if let Some(index) = self
            .entries
            .iter()
            .position(|(cached_point, _)| (cached_point).reduce() == (point).reduce())
        {
            index
        } else {
            let mut powers = execution.buffer(EvaluationPlan::<PallasBase>::power_count(N), false);
            EvaluationPlan::prepare(point, &mut powers);
            self.entries.push((*point, powers));
            self.entries.len() - 1
        }
    }

    /// Serial evaluation through the cache, the tests' reference for the
    /// pool evaluation phase.
    #[cfg(test)]
    pub(super) fn evaluate(&mut self, coefficients: &[Fp], point: &Fp) -> Result<Fp, Error> {
        if coefficients.len() != N {
            return Err(Error::InternalInvariant);
        }
        let entry = self.prepare(crate::test_codec::execution(), point);
        // prepare() sizes the powers for the N coefficients checked above.
        EvaluationPlan::bind(point, &self.entries[entry].1)
            .evaluate(coefficients)
            .map_err(|_| Error::InternalInvariant)
    }
}

/// What one evaluation job reads: a full `N`-coefficient polynomial, the
/// linear vanishing mask `[r_0, r_1]`, or a sparse instance's precomputed value.
pub(super) enum EvaluationSource<'a> {
    Dense(PolySource<'a>),
    Linear([Fp; 2]),
    Value(Fp),
}

pub(super) struct EvaluationJob<'a> {
    pub(super) coefficients: EvaluationSource<'a>,
    pub(super) point: Fp,
}

/// Evaluates coefficient polynomials as pool tasks and preserves job order
/// for the caller's transcript writes. A linear source evaluates as one
/// multiply-add, which equals the dense power scan of its zero-padded form.
pub(super) fn parallel_evaluate_polynomials(
    execution: Execution<'_>,
    jobs: Vec<EvaluationJob>,
) -> Result<Vec<Fp>, Error> {
    let mut powers = EvaluationPowerCache::new();
    let mut indexed_jobs = Vec::with_capacity(jobs.len());
    let mut values = alloc::vec![Fp::ZERO; jobs.len()];
    for (index, job) in jobs.into_iter().enumerate() {
        match job.coefficients {
            EvaluationSource::Dense(coefficients) => {
                if coefficients.as_slice().len() != N {
                    return Err(Error::InternalInvariant);
                }
                let point_index = powers.prepare(execution, &job.point);
                indexed_jobs.push((index, coefficients, point_index));
            }
            EvaluationSource::Linear(mask) => values[index] = mask[1].mul_add(&job.point, &mask[0]),
            EvaluationSource::Value(value) => values[index] = value,
        }
    }
    for (index, result) in execution.map(indexed_jobs, |(index, coefficients, point_index), _| {
        let (point, point_powers) = &powers.entries[point_index];
        // Each accepted dense job has N coefficients and a matching cache entry.
        (
            index,
            EvaluationPlan::bind(point, point_powers)
                .evaluate(coefficients.as_slice())
                .map_err(|_| Error::InternalInvariant),
        )
    }) {
        values[index] = result?;
    }
    Ok(values)
}
