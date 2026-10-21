//! Initialized lookup storage; leases end at each stage's final reader.

use super::PreparedLookupTable;
#[cfg(test)]
use crate::native::buffer::BufferInventory;
use crate::native::{
    buffer::BufferPool,
    field::{CanonicalUint, Fp},
    randomness::LOOKUPS_PER_ACTION,
    target::{FixedTarget, USABLE_ROWS_END},
};

/// Canonical sort key, θ-compressed field value, usable-row multiplicity,
/// and uncompressed tuple identity. Only the canonical key orders entries;
/// the identity maps the sorted entry back to the preflight tuple.
pub(super) type SortKey = (CanonicalUint, Fp, u16, usize);

#[derive(Default)]
pub(crate) struct LookupWorkspace {
    pub(crate) ids: BufferPool<u16>,
    pub(super) indices: BufferPool<u16>,
    pub(super) counts: BufferPool<u32>,
    pub(super) slots: BufferPool<u32>,
    pub(super) keys: BufferPool<SortKey>,
    pub(super) entries: BufferPool<(Fp, u16)>,
    pub(super) runs: BufferPool<(u32, Fp)>,
}

impl LookupWorkspace {
    pub(crate) fn provision_ids(&self, actions: usize) {
        self.ids
            .provision(USABLE_ROWS_END, actions * LOOKUPS_PER_ACTION, 0);
    }

    pub(super) fn provision(&self, target: &FixedTarget, actions: usize, workers: usize) {
        let preparation = target.lookup_preparation();
        let size = |index: usize| match preparation.tables[index].as_deref() {
            Some(PreparedLookupTable::Static { order, .. }) => order.entries.len(),
            Some(PreparedLookupTable::Distinct { distinct }) => distinct.len(),
            None => 0,
        };
        for &index in &preparation.unique_sources {
            let len = size(index);
            if len == 0 {
                continue;
            }
            let capacity = len.next_power_of_two();
            // Sum equal capacity classes before provisioning; independent
            // tables can have consumers running at the same time.
            let counts = preparation
                .unique_sources
                .iter()
                .zip(&preparation.consumer_counts)
                .filter(|(other, _)| size(**other).next_power_of_two() == capacity)
                .map(|(_, &consumers)| (actions * consumers).min(workers))
                .sum();
            self.counts.provision(len, counts, 0);
            if matches!(
                preparation.tables[index].as_deref(),
                Some(PreparedLookupTable::Distinct { .. })
            ) {
                let tables = preparation
                    .unique_sources
                    .iter()
                    .filter(|&&other| {
                        matches!(
                            preparation.tables[other].as_deref(),
                            Some(PreparedLookupTable::Distinct { .. })
                        ) && size(other).next_power_of_two() == capacity
                    })
                    .count();
                self.indices.provision(len, tables, 0);
                self.keys.provision(len, tables, Self::empty_key());
                self.entries.provision(len, tables, (Fp::ZERO, 0));
                self.slots
                    .provision((len * 4).next_power_of_two().max(8), tables, 0);
            }
        }
        // Runs live through the whole commitment batch. The usable-row bound
        // also covers theta collisions without a counting pass or growth.
        self.runs.provision(
            USABLE_ROWS_END,
            2 * actions * LOOKUPS_PER_ACTION,
            (0, Fp::ZERO),
        );
    }

    pub(super) fn empty_key() -> SortKey {
        (<Fp>::ZERO.to_canonical_uint(), Fp::ZERO, 0, 0)
    }

    #[cfg(test)]
    pub(crate) fn inventory(&self) -> BufferInventory {
        [
            self.ids.inventory(),
            self.indices.inventory(),
            self.counts.inventory(),
            self.slots.inventory(),
            self.keys.inventory(),
            self.entries.inventory(),
            self.runs.inventory(),
        ]
        .into_iter()
        .fold(
            BufferInventory {
                allocations: 0,
                buffers: 0,
                bytes: 0,
            },
            |a, b| BufferInventory {
                allocations: a.allocations + b.allocations,
                buffers: a.buffers + b.buffers,
                bytes: a.bytes + b.bytes,
            },
        )
    }

    #[cfg(test)]
    pub(crate) fn dirty(&self) {
        self.ids.dirty(u16::MAX);
        self.indices.dirty(u16::MAX);
        self.counts.dirty(u32::MAX);
        self.slots.dirty(u32::MAX);
        self.keys
            .dirty((<Fp>::ONE.to_canonical_uint(), Fp::ONE, u16::MAX, usize::MAX));
        self.entries.dirty((Fp::ONE, u16::MAX));
        self.runs.dirty((u32::MAX, Fp::ONE));
    }
}

#[cfg(test)]
mod tests {
    use super::super::{
        compress_table_from_prepared, count_input_entries_in, count_input_values,
        permute_usable_values, prepared_table_access_in, reconstruct_permuted_in,
    };
    use super::*;
    use crate::native::test_support::reduced_values;

    #[test]
    fn dirty_storage_rebuilds_theta_maps_and_returns_failed_counts() {
        let target = crate::test_codec::target();
        let scratch = LookupWorkspace::default();
        scratch.provision(target, 2, 4);
        let inventory = scratch.inventory();
        // Force compressed representatives to collide, then reuse the returned
        // sort storage for real theta-dependent tables below.
        let collision_lookup = target
            .lookup_preparation()
            .tables
            .iter()
            .position(|table| {
                matches!(table.as_deref(), Some(PreparedLookupTable::Distinct { .. }))
            })
            .unwrap();
        scratch.dirty();
        assert!(
            prepared_table_access_in(
                target,
                collision_lookup,
                &[Fp::ZERO; crate::native::target::N],
                &scratch,
            )
            .is_none()
        );
        assert_eq!(scratch.inventory(), inventory);
        for theta in [
            <Fp>::from_u64(17),
            <Fp>::ZERO,
            <Fp>::from_u64(29),
            <Fp>::ONE,
            <Fp>::ONE.neg(),
            <Fp>::from_u64(43),
        ] {
            for lookup in 0..LOOKUPS_PER_ACTION {
                scratch.dirty();
                let table = compress_table_from_prepared(target, lookup, &theta).unwrap();
                let Some(access) = prepared_table_access_in(target, lookup, &table, &scratch)
                else {
                    assert_eq!(scratch.inventory(), inventory);
                    continue;
                };
                let (order, probe, entry_of_id) = access.parts();
                assert!(
                    order
                        .entries
                        .windows(2)
                        .all(|pair| pair[0].0.to_canonical_uint() < pair[1].0.to_canonical_uint())
                );
                let mut ids = target.lookup_preparation().sides[lookup]
                    .as_ref()
                    .unwrap()
                    .tuples
                    .row_ids()
                    .to_vec();
                let counts =
                    count_input_entries_in(order, probe, entry_of_id, &ids, &table, &scratch)
                        .unwrap();
                assert_eq!(
                    counts,
                    count_input_values(order, probe, &table[..USABLE_ROWS_END]).unwrap()
                );
                let actual = reconstruct_permuted_in(
                    order,
                    &counts,
                    USABLE_ROWS_END,
                    crate::test_codec::execution(),
                    &scratch,
                )
                .unwrap();
                let expected = permute_usable_values(
                    table[..USABLE_ROWS_END].to_vec(),
                    table[..USABLE_ROWS_END].to_vec(),
                )
                .unwrap();
                assert_eq!(reduced_values(&actual.input), reduced_values(&expected.0));
                assert_eq!(reduced_values(&actual.table), reduced_values(&expected.1));
                let runs = |values: &[(u32, Fp)]| {
                    values
                        .iter()
                        .map(|(row, value)| (*row, value.to_canonical_uint()))
                        .collect::<Vec<_>>()
                };
                assert_eq!(
                    runs(&actual.input_runs),
                    runs(&super::super::column_runs(&actual.input))
                );
                assert_eq!(
                    runs(&actual.table_runs),
                    runs(&super::super::column_runs(&actual.table))
                );
                drop(actual);
                drop(counts);
                let before_failure = scratch.inventory();
                ids[100] = u16::MAX;
                assert!(
                    count_input_entries_in(order, probe, entry_of_id, &ids, &table, &scratch)
                        .is_err()
                );
                assert_eq!(scratch.inventory(), before_failure);
                drop(access);
                assert_eq!(scratch.inventory(), inventory);
            }
        }
    }
}
