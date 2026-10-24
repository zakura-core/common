//! The fused gate evaluator's frame of references into the query tables.
//!
//! Each descriptor stores a column kind and an index into that kind's query
//! table, not an absolute column index. A frame slot is a third index space:
//! `GATE_QUERY_DESCRIPTORS[slot]` first selects a query, and that query selects
//! the column and rotation. The prepared selector recipe uses fixed frame
//! slots from this table.

/// The kind of column a gate query reads.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QueryKind {
    /// A fixed-column query.
    Fixed,
    /// An advice-column query.
    Advice,
    /// An instance-column query.
    Instance,
}

/// Number of values in the fused gate evaluator's query frame.
pub const GATE_QUERY_COUNT: usize = 49;

const fn build_query_descriptors<const N: usize>(
    segments: [(QueryKind, usize, usize); N],
) -> [(QueryKind, usize); GATE_QUERY_COUNT] {
    let mut descriptors = [(QueryKind::Fixed, 0); GATE_QUERY_COUNT];
    let mut segment_index = 0;
    let mut descriptor_index = 0;
    while segment_index < N {
        let (kind, start, end) = segments[segment_index];
        if start >= end {
            panic!("query descriptor ranges must be nonempty");
        }

        let mut query_index = start;
        while query_index < end {
            if descriptor_index == GATE_QUERY_COUNT {
                panic!("too many query descriptors");
            }
            descriptors[descriptor_index] = (kind, query_index);
            descriptor_index += 1;
            query_index += 1;
        }
        segment_index += 1;
    }
    if descriptor_index != GATE_QUERY_COUNT {
        panic!("wrong number of query descriptors");
    }
    descriptors
}

macro_rules! query_descriptors {
    ($($kind:ident: $start:literal..$end:literal),+ $(,)?) => {
        build_query_descriptors([$(
            (QueryKind::$kind, $start, $end),
        )+])
    };
}

/// Query descriptors used by the fused gate evaluator, in frame order.
///
/// Each pair is `(kind, query index within that kind's table)`. For example,
/// frame slot 25 is fixed-query 0, which reads fixed column 3 through
/// [`super::FIXED_QUERIES`]. Slots 0..25 are advice queries; all later slots
/// are fixed queries. No instance queries are used by the current frame.
pub const GATE_QUERY_DESCRIPTORS: [(QueryKind, usize); GATE_QUERY_COUNT] = query_descriptors![
    Advice: 0..25,
    Fixed: 0..1,
    Fixed: 2..11,
    Fixed: 13..14,
    Fixed: 16..29,
];
