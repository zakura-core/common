//! Prepared gate tasks and the proof-wide gate/copy wave.
//!
//! Task admission follows the prepared Action and gate order; results are
//! restored to expression order, with copies after every gate expression.

use super::{GateCheck, POSEIDON_FIRST_PROGRAM, copies::check_copies};
use crate::Error;
use crate::native::{
    compiled_gates, generated_expressions::GATE_CONSTRAINT_COUNT, polynomial::SharedPoly,
    prover::AdviceMatrix, target::FixedTarget, worker::Execution,
};
use alloc::{sync::Arc, vec::Vec};

/// Every generated gate expression index, in protocol order.
pub(super) fn gate_expression_indices(target: &FixedTarget) -> Vec<usize> {
    target
        .gates()
        .iter()
        .flat_map(|gate| gate.indices())
        .collect()
}

pub(super) fn check_gates_and_copies_batch(
    execution: Execution<'_>,
    target: &FixedTarget,
    matrices: &[Arc<AdviceMatrix>],
    instances: Option<&[SharedPoly]>,
) -> Vec<Result<(), Error>> {
    let frame = compiled_gates::Frame::prepared(target);
    let columns = matrices
        .iter()
        .map(|matrix| frame.bind(matrix.columns()))
        .collect::<Vec<_>>();
    let action_checks = &target.preflight().gates;
    let per_action = action_checks.len();
    let checks = (0..matrices.len() * per_action)
        .map(|index| (index / per_action, action_checks[index % per_action]));
    let results = execution.map(checks, |(action, check), _| match check {
        GateCheck::Single {
            position,
            expression,
        } => [
            Some((
                position,
                (|| {
                    let columns = columns[action].as_ref().map_err(|&error| error)?;
                    let rows = target
                        .gate_active_rows(expression)
                        .ok_or(Error::InternalInvariant)?;
                    compiled_gates::check(expression, columns, rows)
                })(),
            )),
            None,
            None,
        ],
        GateCheck::Poseidon {
            position,
            start,
            end,
        } => {
            let columns = match &columns[action] {
                Ok(columns) => columns,
                Err(error) => return [Some((position, Err(*error))), None, None],
            };
            let rows = &target
                .gate_active_rows(POSEIDON_FIRST_PROGRAM)
                .expect("prepared gate rows")[start..end];
            let mut zero = [true; 3];
            for &row in rows {
                let bodies = compiled_gates::poseidon_full_round_bodies(columns, usize::from(row));
                for (zero, body) in zero.iter_mut().zip(bodies) {
                    *zero &= body.is_zero();
                }
            }
            core::array::from_fn(|i| Some((position + i, Ok(zero[i]))))
        }
        GateCheck::Copies => [
            Some((
                GATE_CONSTRAINT_COUNT,
                instances.map_or(Ok(true), |instances| {
                    check_copies(target, &matrices[action], &instances[action]).map(|()| true)
                }),
            )),
            None,
            None,
        ],
    });
    results
        .chunks(per_action)
        .map(|action_results| {
            let mut ordered = [Ok(true); GATE_CONSTRAINT_COUNT + 1];
            for &(position, result) in action_results.iter().flatten().flatten() {
                if matches!(ordered[position], Ok(true)) {
                    ordered[position] = result;
                }
            }
            for result in ordered {
                if !result? {
                    return Err(Error::UnsatisfiedWitness);
                }
            }
            Ok(())
        })
        .collect()
}
