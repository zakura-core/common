//! The pinned circuit's shared query descriptors and ordered query tables.
//!
//! The prover consumes these directly; host-side generators consume them
//! when a prepared artifact bakes in fixed-query structure (the gate-selector
//! artifact, for example). Macros validate expression operands against the same
//! fixed, advice, and instance tables. Permutation columns belong to the prover.
//!
//! A [`Query`] contains a column index and rotation. Its position in a query
//! table is a separate index: fixed-query 0 reads fixed column 3. The fused
//! evaluator's [`GATE_QUERY_DESCRIPTORS`] adds frame positions on top of those
//! per-kind query indices.
//!
//! Where index spaces meet, use `column_index` for a column within its kind,
//! `query_index` for a position in that kind's query table, and `frame_slot`
//! for a position in the fused gate frame. Use `program_index` for a recipe
//! selected by [`crate::programs::expression`] and `row` for the row being
//! evaluated, keeping its domain explicit.

mod gate_frame;

pub use gate_frame::{GATE_QUERY_COUNT, GATE_QUERY_DESCRIPTORS, QueryKind};

/// One column query of the pinned circuit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Query {
    /// The queried column's index within its kind's column set.
    pub column: usize,
    /// Row offset relative to the evaluation point: zero is the current row,
    /// positive values read later rows, and negative values read earlier rows.
    pub rotation: i32,
}

/// Expands ordered column runs `(start, end, rotation)` into a query table.
///
/// Each run covers the half-open column interval `start..end`. Runs retain
/// their input order; columns within a run increase by one. Repeated columns
/// and rotations are preserved. The const parameter `N` is the output query
/// count, independent of the circuit's row count [`crate::N`].
///
/// ```
/// use zakura_sensei_shared::queries::{Query, build_queries};
///
/// const QUERIES: [Query; 3] = build_queries([(2, 4, 0), (2, 3, -1)]);
/// assert_eq!(QUERIES, [
///     Query { column: 2, rotation: 0 },
///     Query { column: 3, rotation: 0 },
///     Query { column: 2, rotation: -1 },
/// ]);
/// ```
///
/// # Panics
///
/// Panics if a run is empty or reversed, or if the runs do not contain exactly
/// `N` queries. Column bounds depend on the query kind and are not checked here.
pub const fn build_queries<const N: usize, const R: usize>(
    runs: [(usize, usize, i32); R],
) -> [Query; N] {
    let mut queries = [Query {
        column: 0,
        rotation: 0,
    }; N];
    let mut run_index = 0;
    let mut query_index = 0;
    while run_index < R {
        let (start, end, rotation) = runs[run_index];
        if start >= end {
            panic!("query runs must be nonempty");
        }

        let mut column = start;
        while column < end {
            if query_index == N {
                panic!("too many queries");
            }
            queries[query_index] = Query { column, rotation };
            query_index += 1;
            column += 1;
        }
        run_index += 1;
    }
    if query_index != N {
        panic!("wrong number of queries");
    }
    queries
}

macro_rules! query_runs {
    ($($start:literal..$end:literal => $rotation:expr),+ $(,)?) => {
        build_queries([$(($start, $end, $rotation)),+])
    };
}

/// The fixed queries of the pinned circuit, in protocol order.
///
/// Every fixed column is queried once at rotation zero. The order is the
/// circuit's query-registration order, so a query index is not generally its
/// column index. [`GATE_QUERY_DESCRIPTORS`] refers to indices in this array.
pub const FIXED_QUERIES: [Query; 29] = query_runs![
    3..4 => 0,
    0..1 => 0,
    11..12 => 0,
    4..11 => 0,
    12..13 => 0,
    1..3 => 0,
    13..29 => 0,
];

/// The advice queries of the pinned circuit, in protocol order.
pub const ADVICE_QUERIES: [Query; 25] = query_runs![
    0..10 => 0,
    9..10 => 1,
    9..10 => -1,
    2..6 => 1,
    0..2 => 1,
    7..9 => 1,
    6..7 => -1,
    1..2 => -1,
    6..7 => 1,
    7..9 => -1,
];

/// The instance queries of the pinned circuit, in protocol order.
pub const INSTANCE_QUERIES: [Query; 1] = query_runs![0..1 => 0];
