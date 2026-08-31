use std::{
    fmt,
    sync::{Arc, Mutex},
};

use crate::poly::EvaluationCacheLayout;

const RETAINED_QUOTIENT_CIRCUIT_COUNTS: [usize; 3] = [1, 2, 4];
const MAX_RETAINED_QUOTIENT_CACHE_LAYOUT_BYTES: usize = 64 * 1024;

pub(super) struct QuotientCacheLayouts {
    layouts: Mutex<[Option<Arc<EvaluationCacheLayout>>; RETAINED_QUOTIENT_CIRCUIT_COUNTS.len()]>,
}

impl Default for QuotientCacheLayouts {
    fn default() -> Self {
        Self {
            layouts: Mutex::new(std::array::from_fn(|_| None)),
        }
    }
}

impl fmt::Debug for QuotientCacheLayouts {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("QuotientCacheLayouts")
            .finish_non_exhaustive()
    }
}

impl QuotientCacheLayouts {
    fn index(circuit_count: usize) -> Option<usize> {
        RETAINED_QUOTIENT_CIRCUIT_COUNTS
            .iter()
            .position(|count| *count == circuit_count)
    }

    pub(super) fn get(&self, circuit_count: usize) -> Option<Arc<EvaluationCacheLayout>> {
        let index = Self::index(circuit_count)?;
        self.layouts
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())[index]
            .clone()
    }

    pub(super) fn retain(&self, circuit_count: usize, layout: EvaluationCacheLayout) {
        let Some(index) = Self::index(circuit_count) else {
            return;
        };
        let mut layouts = self
            .layouts
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let existing_bytes = layouts
            .iter()
            .enumerate()
            .filter(|(candidate, _)| *candidate != index)
            .filter_map(|(_, layout)| layout.as_ref())
            .map(|layout| layout.payload_bytes())
            .sum::<usize>();
        if existing_bytes.saturating_add(layout.payload_bytes())
            <= MAX_RETAINED_QUOTIENT_CACHE_LAYOUT_BYTES
        {
            layouts[index] = Some(Arc::new(layout));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_counts_are_bounded() {
        assert_eq!(RETAINED_QUOTIENT_CIRCUIT_COUNTS, [1, 2, 4]);
        assert_eq!(MAX_RETAINED_QUOTIENT_CACHE_LAYOUT_BYTES, 64 * 1024);
    }
}
