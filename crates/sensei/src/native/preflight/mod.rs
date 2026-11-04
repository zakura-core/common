//! Deterministic ordinary-domain constraint checks for native witnesses.
//!
//! Where these checks sit in the pipeline (`native::prove`): the complete
//! randomness schedule is sampled first, then the witness matrices are built
//! and checked here, and only then is any of that randomness spent — the
//! advice blinds and tails are applied by the commitment stage that follows.
//! So the checks see the unblinded witness, a rejected request has already
//! consumed its full RNG schedule (1,552 `u64`s for one Action, 2,736 for
//! two), and nothing here may draw from or reorder that schedule. The exact
//! consumption is frozen protocol behavior pinned by the golden and RNG-tape
//! replay tests; the order is documented, not to be "fixed".
//!
//! [`check_witness_constraints`] coordinates gate, copy, and lookup checks.
//! [`gates`] runs the combined gate/copy wave, [`copies`] resolves prepared
//! copy classes, and [`lookups`] checks membership and retains tuple identities.
//! Test-only references live in `reference.rs`.
//! Successful lookup membership probes return [`WitnessFeeds`] for the later
//! compression stage, avoiding another search for the same tuple identities.
//! These feeds describe usable, unblinded rows; the commitment stage still
//! recomputes rows whose expressions can observe the blinding tail.
//!
//! A failed gate, copy relation, or lookup membership test reports
//! [`Error::UnsatisfiedWitness`]. Errors obtaining a valid frame or evaluating
//! its prepared metadata propagate unchanged: an internal shape failure does
//! not establish that a circuit constraint was false (see [`super::invariant`]).

mod copies;
mod gates;
mod lookups;
#[cfg(test)]
mod reference;

use gates::{check_gates_and_copies_batch, gate_expression_indices};
use lookups::check_lookups_batch_in;
#[cfg(test)]
use lookups::check_lookups_in;

use super::{
    buffer::Buffer, prover::LookupWorkspace, randomness::LOOKUPS_PER_ACTION, worker::Execution,
};
use alloc::{sync::Arc, vec::Vec};

use crate::{
    Error,
    types::{NativeStatement, ProvingRequest},
};

#[cfg(test)]
use super::evaluation::evaluate_expression;
use super::{
    compiled_gates,
    generated_expressions::{
        ExpressionRange, GATE_CONSTRAINT_COUNT, LookupExpressionRanges, LookupInputKernel,
    },
    polynomial::SharedPoly,
    prover::{AdviceMatrix, prepared_lookup_table_tuples},
    target::{ADVICE_COLUMNS, FixedTarget, N, USABLE_ROWS_END},
};

// Full-round constraints in sensei-shared's programs::expression, arm 75..=77.
// The first program supplies the active rows shared by all three constraints.
const POSEIDON_FIRST_PROGRAM: usize = 75;
const POSEIDON_PROGRAMS: core::ops::Range<usize> = POSEIDON_FIRST_PROGRAM..78;

/// Immutable task descriptions contain indices into the target, never self-borrows.
#[derive(Default)]
pub(crate) struct PreparedPreflight {
    gates: Vec<GateCheck>,
    pub(crate) kernels: [Option<LookupInputKernel>; super::randomness::LOOKUPS_PER_ACTION],
}

#[derive(Clone, Copy)]
enum GateCheck {
    Single {
        position: usize,
        expression: usize,
    },
    Poseidon {
        position: usize,
        start: usize,
        end: usize,
    },
    Copies,
}

impl PreparedPreflight {
    pub(crate) fn new(target: &FixedTarget) -> Result<Self, Error> {
        compiled_gates::Frame::resolve(target)?;
        let expressions = gate_expression_indices(target);
        if expressions.len() != GATE_CONSTRAINT_COUNT
            || target.lookups().len() != super::randomness::LOOKUPS_PER_ACTION
        {
            return Err(Error::InternalInvariant);
        }
        let poseidon_rows = target
            .gate_active_rows(POSEIDON_FIRST_PROGRAM)
            .filter(|rows| (76..78).all(|program| target.gate_active_rows(program) == Some(*rows)));
        let mut gates = Vec::with_capacity(
            expressions.len() + poseidon_rows.map_or(0, |rows| rows.len().div_ceil(64)),
        );
        for (position, expression) in expressions.into_iter().enumerate() {
            let rows = target
                .gate_active_rows(expression)
                .ok_or(Error::InternalInvariant)?;
            if rows.iter().any(|&row| usize::from(row) >= N) {
                return Err(Error::InternalInvariant);
            }
            if let Some(rows) = poseidon_rows.filter(|_| POSEIDON_PROGRAMS.contains(&expression)) {
                if expression == POSEIDON_FIRST_PROGRAM {
                    gates.extend(
                        (0..rows.len())
                            .step_by(64)
                            .map(|start| GateCheck::Poseidon {
                                position,
                                start,
                                end: (start + 64).min(rows.len()),
                            }),
                    );
                }
            } else {
                gates.push(GateCheck::Single {
                    position,
                    expression,
                });
            }
        }
        gates.push(GateCheck::Copies);
        let kernels = core::array::from_fn(|index| {
            let lookup = target.lookups().get(index)?;
            let kernel = LookupInputKernel::resolve(target, index)?;
            let tuples = prepared_lookup_table_tuples(target, index)?;
            (lookup.inputs().len() == lookup.tables().len()
                && lookup.inputs().len() == kernel.components()
                && tuples.arity() == kernel.components())
            .then_some(kernel)
        });
        Ok(Self { gates, kernels })
    }
}

/// One lookup's input-side identities for one Action: for every usable row,
/// the index of the prepared table tuple that row's input tuple equals in the
/// lookup's [prepared tuple index](super::prover::prepared_lookup_table_tuples)
/// — the hit the preflight membership probe already found.
/// `commit_lookup_permutations` reads
/// each such row's θ-compressed input as the compressed table's value at that
/// tuple's representative row (equal tuples fold to equal values) and counts
/// the identities straight into the permutation. The blinding tail is never
/// probed, and the usable rows whose expressions can observe it are
/// re-evaluated on the blinded columns there, so nothing about those rows is
/// retained. Built only through [`Self::new`], which validates the length, so
/// consumers read it without re-checking.
pub(crate) struct LookupInputIds {
    programs: ExpressionRange,
    ids: Buffer<u16>,
}

impl LookupInputIds {
    fn new(lookup: LookupExpressionRanges, ids: Buffer<u16>) -> Result<Self, Error> {
        let programs = lookup.inputs();
        if programs.is_empty() || ids.len() != USABLE_ROWS_END {
            return Err(Error::InternalInvariant);
        }
        Ok(Self { programs, ids })
    }

    /// The lookup's input programs, one per component.
    pub(crate) fn programs(&self) -> ExpressionRange {
        self.programs
    }

    /// The table tuple identity of every usable row, row-ascending.
    pub(crate) fn ids(&self) -> &[u16] {
        &self.ids
    }
}

/// One Action's lookup input identities: exactly one [`LookupInputIds`] per
/// fixed lookup, lookup-ascending.
pub(crate) struct ActionLookupFeeds {
    lookups: [LookupInputIds; LOOKUPS_PER_ACTION],
}

impl ActionLookupFeeds {
    fn new(
        target: &FixedTarget,
        lookups: [LookupInputIds; LOOKUPS_PER_ACTION],
    ) -> Result<Self, Error> {
        if lookups.len() != target.lookups().len() {
            return Err(Error::InternalInvariant);
        }
        Ok(Self { lookups })
    }

    #[cfg(test)]
    pub(crate) fn lookups(&self) -> &[LookupInputIds] {
        &self.lookups
    }

    /// The per-lookup identities, lookup-ascending, one per fixed lookup.
    pub(crate) fn into_lookups(self) -> [LookupInputIds; LOOKUPS_PER_ACTION] {
        self.lookups
    }
}

/// Witness-derived feeds retained from preflight for the prover stages: one
/// [`ActionLookupFeeds`] per Action, in request order.
pub(crate) struct WitnessFeeds {
    actions: Vec<ActionLookupFeeds>,
    pub(crate) instances: Vec<SharedPoly>,
}

impl WitnessFeeds {
    /// The per-Action feeds, in request order.
    pub(crate) fn into_actions(self) -> Vec<ActionLookupFeeds> {
        self.actions
    }
}

/// Checks every fixed gate, equality constraint, and lookup on the unblinded
/// witness — after the randomness schedule has been sampled but before any of
/// it is spent (see the module documentation) — returning the retained
/// witness feeds. The matrices are shared with the check tasks and handed on
/// to the advice commitment.
///
/// The checks run as proof-wide waves: every Action's gates and copies in
/// one pool wave, then every Action's lookups in one wave.
/// Every result is collected and then reported in the serial order — Action
/// by Action, gates before copies before lookups — so the first failure
/// surfaced is the one the per-Action sequence would have found. Matrix
/// shapes are validated for every Action before any check runs; that is a
/// structural invariant of the caller's construction, never a witness
/// failure.
pub(crate) fn check_witness_constraints(
    execution: Execution<'_>,
    target: &FixedTarget,
    request: &ProvingRequest,
    statements: &[NativeStatement],
    matrices: &[Arc<AdviceMatrix>],
    scratch: &LookupWorkspace,
) -> Result<WitnessFeeds, Error> {
    if matrices.len() != request.action_count() || statements.len() != matrices.len() {
        return Err(Error::InternalInvariant);
    }

    let action_setup = || -> Result<Vec<SharedPoly>, Error> {
        statements
            .iter()
            .zip(matrices)
            .map(|(statement, matrix)| {
                if matrix.columns().len() != ADVICE_COLUMNS
                    || matrix.columns().iter().any(|column| column.len() != N)
                {
                    return Err(Error::InternalInvariant);
                }
                let mut column = execution.buffer(N, true);
                column[..statement.len()].copy_from_slice(&statement[..]);
                Ok(SharedPoly::new(column))
            })
            .collect()
    };
    #[cfg(test)]
    let instances = super::stage_timing::measure_witness(
        super::stage_timing::WitnessStage::ActionSetup,
        action_setup,
    )?;
    #[cfg(not(test))]
    let instances = action_setup()?;

    let gates = || check_gates_and_copies_batch(execution, target, matrices, Some(&instances));
    #[cfg(test)]
    let gate_results =
        super::stage_timing::measure_witness(super::stage_timing::WitnessStage::Gates, gates);
    #[cfg(not(test))]
    let gate_results = gates();

    let lookups = || check_lookups_batch_in(execution, target, matrices, &instances, scratch);
    #[cfg(test)]
    let lookup_results =
        super::stage_timing::measure_witness(super::stage_timing::WitnessStage::Lookups, lookups);
    #[cfg(not(test))]
    let lookup_results = lookups();

    if gate_results.len() != matrices.len() || lookup_results.len() != matrices.len() {
        return Err(Error::InternalInvariant);
    }
    let mut actions = Vec::with_capacity(matrices.len());
    for (gates, lookups) in gate_results.into_iter().zip(lookup_results) {
        gates?;
        actions.push(lookups?);
    }
    Ok(WitnessFeeds { actions, instances })
}

#[cfg(test)]
mod tests;
