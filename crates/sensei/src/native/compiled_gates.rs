//! Monomorphized preflight bodies from the circuit's expression recipes.
//!
//! Query metadata is checked during preparation and column shapes once per
//! Action. The row loop has direct, infallible array reads and field
//! arithmetic, with no operand stack or per-instruction dispatch.

use crate::Error;

use super::{
    field::Fp,
    generated_expressions::{GATE_CONSTRAINT_COUNT, constant},
    programs::{self, Algebra},
    queries::{ADVICE_QUERIES, FIXED_QUERIES},
    target::{ADVICE_COLUMNS, FIXED_COLUMNS, FixedTarget, N},
};

/// The fixed frame shared by all gate tasks for an Action. Query descriptors
/// must agree with the tables specialized into the recipes' field algebra.
#[derive(Clone, Copy)]
pub(super) struct Frame<'a> {
    fixed: &'a [[Fp; N]; FIXED_COLUMNS],
}

impl<'a> Frame<'a> {
    pub(super) fn resolve(target: &'a FixedTarget) -> Result<Self, Error> {
        // Both metadata and columns come from FixedTarget::build, so a mismatch
        // is a preparation failure, not an unsatisfied witness constraint.
        if target.queries().fixed() != FIXED_QUERIES || target.queries().advice() != ADVICE_QUERIES
        {
            return Err(Error::InternalInvariant);
        }
        Ok(Self {
            fixed: target
                .fixed_values()
                .try_into()
                .map_err(|_| Error::InternalInvariant)?,
        })
    }

    /// Borrows a target whose query metadata was validated at preparation.
    /// [`super::preflight::PreparedPreflight::new`] calls [`Self::resolve`]
    /// before [`FixedTarget::build`] returns; that also checks the fixed-column
    /// count, while each column's `[Fp; N]` type fixes its row count.
    pub(super) fn prepared(target: &'a FixedTarget) -> Self {
        Self {
            fixed: target
                .fixed_values()
                .try_into()
                .expect("prepared fixed columns"),
        }
    }

    pub(super) fn bind<'b, A: AsRef<[Fp]>>(
        &'b self,
        advice: &'b [A],
    ) -> Result<Columns<'b>, Error> {
        if advice.len() != ADVICE_COLUMNS {
            return Err(Error::InternalInvariant);
        }
        let mut columns = [&self.fixed[0]; ADVICE_COLUMNS];
        // Witness construction supplies full N-row columns; this checks their
        // representation, before check() tests any circuit equation.
        for (slot, column) in columns.iter_mut().zip(advice) {
            *slot = column
                .as_ref()
                .try_into()
                .map_err(|_| Error::InternalInvariant)?;
        }
        Ok(Columns {
            fixed: self.fixed,
            advice: columns,
        })
    }
}

pub(super) struct Columns<'a> {
    fixed: &'a [[Fp; N]; FIXED_COLUMNS],
    advice: [&'a [Fp; N]; ADVICE_COLUMNS],
}

struct Row<'a, 'b> {
    columns: &'a Columns<'b>,
    row: usize,
}

impl Algebra for Row<'_, '_> {
    type Value = Fp;

    #[inline(always)]
    fn fixed(&self, index: u8) -> Fp {
        let query = FIXED_QUERIES[usize::from(index)];
        self.columns.fixed[query.column][self.row.wrapping_add(query.rotation as usize) & (N - 1)]
    }

    #[inline(always)]
    fn advice(&self, index: u8) -> Fp {
        let query = ADVICE_QUERIES[usize::from(index)];
        self.columns.advice[query.column][self.row.wrapping_add(query.rotation as usize) & (N - 1)]
    }

    #[inline(always)]
    fn gated(&self, _factor: impl FnOnce() -> Fp, body: Fp) -> Fp {
        body
    }

    // Preserve the existing shared-power / sum-of-products interpolation
    // kernel instead of expanding the tree's cloned power chains.
    #[inline(always)]
    fn interpolate_x(&self, digit: Fp) -> Fp {
        let mut powers = [<Fp>::ONE; 8];
        for i in 1..powers.len() {
            powers[i] = powers[i - 1].mul(&digit);
        }
        let coefficients = [
            self.fixed(0),
            self.fixed(3),
            self.fixed(4),
            self.fixed(5),
            self.fixed(6),
            self.fixed(7),
            self.fixed(8),
            self.fixed(9),
        ];
        <Fp>::sum_of_products(&powers, &coefficients)
            .add(&constant(13))
            .sub(&self.advice(0))
    }
}

#[inline(always)]
fn body<const INDEX: usize>(columns: &Columns<'_>, row: usize) -> Fp {
    programs::expression(&Row { columns, row }, INDEX)
}

fn check_program<const INDEX: usize>(columns: &Columns<'_>, rows: &[u16]) -> bool {
    rows.iter()
        .all(|&row| body::<INDEX>(columns, usize::from(row)).is_zero())
}

/// Dispatch once for the whole active-row list. Each function specializes
/// the recipe index before looping, so rows do not dispatch by program ID.
pub(super) fn check(expression: usize, columns: &Columns<'_>, rows: &[u16]) -> Result<bool, Error> {
    Ok(CHECKS.get(expression).ok_or(Error::InternalInvariant)?(
        columns, rows,
    ))
}

pub(super) fn poseidon_full_round_bodies(columns: &Columns<'_>, row: usize) -> [Fp; 3] {
    Row { columns, row }.poseidon_full_round_bodies()
}

macro_rules! gate_checks {
    ($($index:literal),+ $(,)?) => {
        const CHECKS: [fn(&Columns<'_>, &[u16]) -> bool; GATE_CONSTRAINT_COUNT] =
            [$(check_program::<$index>),+];
        #[cfg(test)]
        const BODIES: [fn(&Columns<'_>, usize) -> Fp; GATE_CONSTRAINT_COUNT] =
            [$(body::<$index>),+];
    };
}

gate_checks![
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
    74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
    98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
    117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135,
    136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154,
    155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
    174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192,
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::{
        evaluation::query_value,
        generated_expressions::{QueryKind, evaluate, program_trees},
    };
    use std::prelude::v1::*;

    #[test]
    fn compiled_gate_bodies_match_tree_reference() {
        let mut state = 0x7f4a_7c15_9e37_79b9u64;
        let mut next = || {
            <Fp>::from_bytes_reduced(&core::array::from_fn::<_, 64, _>(|_| {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                state as u8
            }))
        };
        let mut fixed = alloc::vec![ [<Fp>::ZERO; N]; FIXED_COLUMNS];
        let mut advice = alloc::vec![ alloc::vec![ <Fp>::ZERO; N]; ADVICE_COLUMNS];
        for column in fixed
            .iter_mut()
            .map(|column| &mut column[..])
            .chain(advice.iter_mut().map(Vec::as_mut_slice))
        {
            for (row, value) in column.iter_mut().enumerate() {
                *value = if row < 8 {
                    <Fp>::from_u64(row as u64)
                } else {
                    next()
                };
            }
        }
        let frame = Frame {
            fixed: fixed.as_slice().try_into().unwrap(),
        };
        let columns = frame.bind(&advice).unwrap();

        // Every gate, every row: this includes both rotation wraps, small
        // selector roots, and unrelated full-width fixed/advice values.
        // Comparing bodies also exercises rows where their selector is zero.
        for (program, kernel) in BODIES.iter().enumerate() {
            let body = program_trees(program).unwrap().dynamic_body().unwrap();
            assert_eq!(body.query_dependencies().instance, 0);
            for row in 0..N {
                let expected = evaluate(body, &mut |kind, index| match kind {
                    QueryKind::Fixed => query_value(&FIXED_QUERIES, index, &fixed, row),
                    QueryKind::Advice => query_value(&ADVICE_QUERIES, index, &advice, row),
                    QueryKind::Instance => panic!("gate recipes must not read instances"),
                })
                .unwrap();
                assert_eq!(
                    (kernel(&columns, row)).reduce(),
                    (expected).reduce(),
                    "program {program}, row {row}"
                );
                assert_eq!(
                    check(program, &columns, &[row as u16]),
                    Ok(expected.is_zero())
                );
            }
        }
        for row in 0..N {
            let bodies = poseidon_full_round_bodies(&columns, row);
            for (program, value) in (75..78).zip(bodies) {
                assert_eq!((value).reduce(), (BODIES[program](&columns, row)).reduce());
            }
        }
    }

    #[test]
    fn compiled_gate_checks_validate_frames_and_keep_sparse_row_selection() {
        let target = crate::test_codec::target();
        let frame = Frame::resolve(target).unwrap();
        let mut advice = alloc::vec![ alloc::vec![ <Fp>::ZERO; N]; ADVICE_COLUMNS];
        assert!(frame.bind(&advice[..ADVICE_COLUMNS - 1]).is_err());
        advice[0].pop();
        assert!(frame.bind(&advice).is_err());
        advice[0].push(<Fp>::ZERO);

        // Gate 1's body a0 * (a4 - a5) can fail only at the chosen row.
        // Empty lists and lists omitting that row must remain satisfied.
        advice[0][N - 1] = <Fp>::ONE;
        advice[4][N - 1] = <Fp>::ONE;
        let columns = frame.bind(&advice).unwrap();
        assert_eq!(check(1, &columns, &[]), Ok(true));
        assert_eq!(check(1, &columns, &[0, 1]), Ok(true));
        assert_eq!(check(1, &columns, &[0, (N - 1) as u16]), Ok(false));
        assert_eq!(
            check(GATE_CONSTRAINT_COUNT, &columns, &[]),
            Err(Error::InternalInvariant)
        );
    }
}
