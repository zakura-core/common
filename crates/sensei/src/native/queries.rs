//! Shared query tables and prover-owned permutation column order.

pub(crate) use sensei_shared::queries::{ADVICE_QUERIES, FIXED_QUERIES};
#[cfg(feature = "prover")]
pub(crate) use sensei_shared::queries::{INSTANCE_QUERIES, Query};

/// The column set a [`PermutationColumn`] indexes into.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ColumnKind {
    /// An instance column.
    Instance,
    /// An advice column.
    Advice,
    /// A fixed column.
    Fixed,
}

/// One column participating in the permutation argument.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PermutationColumn {
    /// The column set the column belongs to.
    pub kind: ColumnKind,
    /// The column's index within that set.
    pub index: usize,
}

const fn build_permutation_columns<const N: usize, const R: usize>(
    runs: [(ColumnKind, usize, usize); R],
) -> [PermutationColumn; N] {
    let mut columns = [PermutationColumn {
        kind: ColumnKind::Instance,
        index: 0,
    }; N];
    let mut run_index = 0;
    let mut column_index = 0;
    while run_index < R {
        let (kind, start, end) = runs[run_index];
        if start >= end {
            panic!("permutation column runs must be nonempty");
        }

        let mut index = start;
        while index < end {
            if column_index == N {
                panic!("too many permutation columns");
            }
            columns[column_index] = PermutationColumn { kind, index };
            column_index += 1;
            index += 1;
        }
        run_index += 1;
    }
    if column_index != N {
        panic!("wrong number of permutation columns");
    }
    columns
}

macro_rules! permutation_column_runs {
    ($($kind:ident: $start:literal..$end:literal),+ $(,)?) => {
        build_permutation_columns([$(
            (ColumnKind::$kind, $start, $end),
        )+])
    };
}

/// The permutation argument's columns, in protocol order.
pub const PERMUTATION_COLUMNS: [PermutationColumn; sensei_shared::PERMUTATION_COLUMN_COUNT] = permutation_column_runs![
    Instance: 0..1,
    Advice: 0..10,
    Fixed: 3..4,
    Fixed: 8..11,
];
