//! Test-only serial, fixed-assignment, and full-row preflight references.
//!
//! The sparse references share expression bodies but partition checks
//! independently of production tasks. The full-row reference also avoids
//! prepared active-row selection and omitted fixed root factors. Per-Action
//! adapters retain the tests' comparisons against the proof-wide waves; they
//! reuse production checks and are not independent arithmetic references.

use super::{
    ActionLookupFeeds,
    gates::{check_gates_and_copies_batch, gate_expression_indices},
    lookups::check_lookups_in,
};
use crate::Error;
use crate::native::{
    evaluation::{evaluate_expression, sparse_gate_expression_is_zero},
    field::Fp,
    prover::{AdviceMatrix, LookupWorkspace},
    target::FixedTarget,
    worker::Execution,
};
use alloc::{sync::Arc, vec::Vec};

/// Restores expression order and surfaces the first gate failure.
#[cfg(test)]
fn collect_gate_results(mut results: Vec<(usize, Result<bool, Error>)>) -> Result<(), Error> {
    results.sort_unstable_by_key(|(position, _)| *position);
    for (_, is_zero) in results {
        if !is_zero? {
            return Err(Error::UnsatisfiedWitness);
        }
    }
    Ok(())
}

/// One Action's gate check: the proof-wide wave over a single matrix. Kept as
/// the tests' per-Action oracle for [`check_gates_batch`].
#[cfg(test)]
pub(super) fn check_gates(
    target: &FixedTarget,
    matrix: &Arc<AdviceMatrix>,
    _instance: &[Fp],
) -> Result<(), Error> {
    check_gates_batch(
        crate::test_codec::execution(),
        target,
        core::slice::from_ref(matrix),
    )
    .pop()
    .unwrap_or(Err(Error::InternalInvariant))
}

/// The gate check of every Action as one pool wave. Ordinary gates are
/// independent tasks; full Poseidon rounds use small active-row chunks so the
/// three outputs share S-boxes without making one large task or retaining a
/// witness-wide cache. Tasks are tagged by Action, and each Action's results
/// are restored to expression order and reported separately. A frame that
/// fails to resolve fails every Action alike.
#[cfg(test)]
pub(super) fn check_gates_batch(
    execution: Execution<'_>,
    target: &FixedTarget,
    matrices: &[Arc<AdviceMatrix>],
) -> Vec<Result<(), Error>> {
    check_gates_and_copies_batch(execution, target, matrices, None)
}

/// Fixed-assignment oracle for the dynamic gate check: expression `i` goes
/// to scoped worker `i mod worker_count`.
#[cfg(test)]
pub(super) fn check_gates_fixed(
    target: &FixedTarget,
    matrix: &AdviceMatrix,
    instance: &[Fp],
) -> Result<(), Error> {
    let expressions = gate_expression_indices(target);
    let worker_count = 3.min(expressions.len()).max(1);
    if worker_count == 1 {
        return check_gates_serial(target, matrix, instance);
    }

    // The reference partitions expressions independently of the production chunks.
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(worker_count)
        .build()
        .unwrap();
    let executor = crate::resource_tests::PoolExecutor(&pool);
    let execution = Execution::new(
        &executor,
        udon::exec::TaskBudget::new(worker_count).unwrap(),
    );
    let results = execution.map(0..worker_count, |worker_index, _| {
        expressions
            .iter()
            .copied()
            .enumerate()
            .skip(worker_index)
            .step_by(worker_count)
            .map(|(position, expression)| {
                (
                    position,
                    sparse_gate_expression_is_zero(expression, target, matrix.columns(), instance),
                )
            })
            .collect::<Vec<_>>()
    });
    collect_gate_results(results.into_iter().flatten().collect())
}

#[cfg(test)]
pub(super) fn check_gates_serial(
    target: &FixedTarget,
    matrix: &AdviceMatrix,
    instance: &[Fp],
) -> Result<(), Error> {
    for gate in target.gates() {
        for expression in gate.indices() {
            if !sparse_gate_expression_is_zero(expression, target, matrix.columns(), instance)? {
                return Err(Error::UnsatisfiedWitness);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
pub(super) fn check_gates_full(
    target: &FixedTarget,
    matrix: &AdviceMatrix,
    instance: &[Fp],
) -> Result<(), Error> {
    for gate in target.gates() {
        for expression in gate.indices() {
            if evaluate_expression(expression, target, matrix.columns(), instance)?
                .iter()
                .any(|value| !value.is_zero())
            {
                return Err(Error::UnsatisfiedWitness);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
pub(super) fn check_lookups(
    target: &FixedTarget,
    matrix: &Arc<AdviceMatrix>,
    instance: &[Fp],
) -> Result<ActionLookupFeeds, Error> {
    check_lookups_in(target, matrix, instance, &LookupWorkspace::default())
}
