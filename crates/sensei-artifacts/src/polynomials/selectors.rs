//! Evaluate fixed-only gate selectors on the extended coset.
//!
//! The shared circuit recipe consumes a query frame, rather than a fixed
//! column row. Frame descriptors choose each fixed column; advice and instance
//! slots are zero because selector preparation depends only on fixed queries.
//! Output is row-major in `prepare_gate_selectors` slot order.

use bento::bytes_of_slice;
use sensei_shared::{
    EXTENDED_N,
    queries::{FIXED_QUERIES, GATE_QUERY_COUNT, GATE_QUERY_DESCRIPTORS, QueryKind},
    selectors::{PREPARED_GATE_SELECTOR_ROW, prepare_gate_selectors},
};
use udon::field::Fp;

use crate::{Error, context::Context};

/// Generates the exact bytes of the gate-selectors artifact: the shared
/// selector recipe evaluated on every extended-coset row's fixed-query frame.
pub(crate) fn generate(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    let fixed_cosets = context.fixed_cosets()?;
    let selectors = (0..EXTENDED_N)
        .map(|row| {
            let queries: [Fp; GATE_QUERY_COUNT] =
                std::array::from_fn(|frame_index| match GATE_QUERY_DESCRIPTORS[frame_index] {
                    (QueryKind::Fixed, query_index) => {
                        let query = FIXED_QUERIES[query_index];
                        fixed_cosets[query.column][row]
                    }
                    (QueryKind::Advice | QueryKind::Instance, _) => <Fp>::ZERO,
                });
            prepare_gate_selectors(&queries).map(|value| value.reduce().into_loose())
        })
        .collect::<Vec<[Fp; PREPARED_GATE_SELECTOR_ROW]>>();
    Ok(bytes_of_slice(&selectors).to_vec())
}
