//! Shared gate and lookup expression layout for proving and verification.
use core::ops::Range;
pub(crate) use sensei_shared::expressions::PROGRAM_COUNT;
#[derive(Clone, Copy)]
pub(crate) struct ExpressionRange {
    pub(super) start: usize,
    pub(super) end: usize,
}

impl ExpressionRange {
    pub(crate) fn indices(self) -> Range<usize> {
        self.start..self.end
    }

    #[cfg(feature = "prover")]
    pub(crate) fn len(self) -> usize {
        self.end - self.start
    }

    #[cfg(feature = "prover")]
    pub(crate) fn is_empty(self) -> bool {
        self.start == self.end
    }
}

#[derive(Clone, Copy)]
pub(crate) struct LookupExpressionRanges {
    pub(super) inputs: ExpressionRange,
    pub(super) tables: ExpressionRange,
}

impl LookupExpressionRanges {
    pub(crate) fn inputs(self) -> ExpressionRange {
        self.inputs
    }

    pub(crate) fn tables(self) -> ExpressionRange {
        self.tables
    }
}

const fn build_contiguous_ranges<const N: usize>(
    mut start: usize,
    ends: [usize; N],
) -> [ExpressionRange; N] {
    let mut ranges = [ExpressionRange { start: 0, end: 0 }; N];
    let mut index = 0;
    while index < N {
        let end = ends[index];
        if end < start {
            panic!("expression range endpoints must be nondecreasing");
        }
        ranges[index] = ExpressionRange { start, end };
        start = end;
        index += 1;
    }
    ranges
}

const fn build_contiguous_lookups<const N: usize>(
    mut start: usize,
    ends: [(usize, usize); N],
) -> [LookupExpressionRanges; N] {
    let empty = ExpressionRange { start: 0, end: 0 };
    let mut lookups = [LookupExpressionRanges {
        inputs: empty,
        tables: empty,
    }; N];
    let mut index = 0;
    while index < N {
        let (input_end, table_end) = ends[index];
        if input_end < start || table_end < input_end {
            panic!("lookup expression range endpoints must be nondecreasing");
        }
        lookups[index] = LookupExpressionRanges {
            inputs: ExpressionRange {
                start,
                end: input_end,
            },
            tables: ExpressionRange {
                start: input_end,
                end: table_end,
            },
        };
        start = table_end;
        index += 1;
    }
    lookups
}

macro_rules! contiguous_ranges {
    ($start:expr; [$($end:expr),+ $(,)?]) => {
        build_contiguous_ranges($start, [$($end),+])
    };
}

macro_rules! contiguous_lookups {
    ($start:expr; [$(($input_end:expr, $table_end:expr)),+ $(,)?]) => {
        build_contiguous_lookups($start, [$(($input_end, $table_end)),+])
    };
}

pub(crate) const GATES: &[ExpressionRange] = &contiguous_ranges!(0; [
    4, 5, 6, 8, 9, 11, 23, 24, 30, 34, 35, 41, 45, 47, 52, 55, 56, 59, 63, 67, 75, 78, 82,
    85, 86, 88, 91, 95, 96, 98, 101, 105, 119, 122, 125, 126, 128, 130, 135, 139, 140, 144,
    149, 156, 159, 162, 163, 165, 167, 172, 176, 177, 181, 186, 193,
]);

pub(crate) const LOOKUPS: &[LookupExpressionRanges] = &contiguous_lookups!(GATES[GATES.len() - 1].end; [
    (194, 195),
    (198, 201),
    (204, PROGRAM_COUNT),
]);

/// Number of gate constraint programs — the y-slots the gate fold advances.
pub(crate) const GATE_CONSTRAINT_COUNT: usize = GATES[GATES.len() - 1].end;
