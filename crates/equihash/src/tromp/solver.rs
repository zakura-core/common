// Equihash solver, derived from John Tromp's solver.
// Copyright (c) 2016 John Tromp, The Zcash developers
// Copyright (c) 2026 The Zakura developers
// Distributed under the MIT software license, see LICENSE-MIT.

use std::vec::Vec;

use crate::blake2b::SolverHashState;

use super::SOLVER_PARAMS;

mod memory;

use memory::Table;

const DIGIT_BITS: usize = SOLVER_PARAMS.n as usize / (SOLVER_PARAMS.k as usize + 1);
const ROUNDS: usize = SOLVER_PARAMS.k as usize;
const REST_BITS: usize = 8;
const BUCKET_BITS: usize = DIGIT_BITS - REST_BITS;
const BUCKETS: usize = 1 << BUCKET_BITS;
const SLOT_BITS: usize = REST_BITS + 2;
const SLOT_MASK: u32 = (1 << SLOT_BITS) - 1;
const SLOTS: usize = (1 << SLOT_BITS) * 9 / 14;
const RESTS: usize = 1 << REST_BITS;
const COLLISION_CAPACITY: usize = 16;
const PROOF_SIZE: usize = 1 << ROUNDS;
const MAX_SOLUTIONS: usize = 8;
const HASH_TABLE_MULTIPLIER: u32 = 0x9e37_79b1;
const HASHES: usize = 1 << (DIGIT_BITS + 1);
const HASHES_PER_BLAKE: usize = 512 / SOLVER_PARAMS.n as usize;
const HASH_BYTES: usize = SOLVER_PARAMS.n as usize / 8;
const HASH_OUTPUT: usize = HASHES_PER_BLAKE * HASH_BYTES;
const HASH_BLOCKS: usize = HASHES / HASHES_PER_BLAKE;
const HASH_BATCH: usize = 64;
const OUTPUT_BATCH: usize = 64;
const INITIAL_WORDS: usize = TABLE_WORDS[0] - 1;
const FINAL_WORDS: usize = HASH_WORDS[ROUNDS - 1];
const FINAL_MAP_BITS: usize = SLOT_BITS + 1;
const FINAL_MAP_SIZE: usize = 1 << FINAL_MAP_BITS;
const FINAL_MAP_MASK: usize = FINAL_MAP_SIZE - 1;
const _: () = assert!(FINAL_WORDS == 1);
const INITIAL_BYTES: usize = INITIAL_WORDS * core::mem::size_of::<u32>();
const HASH_WORDS: [usize; ROUNDS] = {
    let mut words = [0; ROUNDS];
    let mut round = 0;
    while round < ROUNDS {
        words[round] = hash_size(round).div_ceil(4);
        round += 1;
    }
    words
};
const TABLE_WORDS: [usize; 2] = [
    1 + (SOLVER_PARAMS.n as usize - DIGIT_BITS + REST_BITS).div_ceil(32),
    1 + (SOLVER_PARAMS.n as usize - 2 * DIGIT_BITS + REST_BITS).div_ceil(32),
];

#[derive(Clone, Copy)]
struct Layout {
    previous_words: usize,
    next_words: usize,
    previous_padding: usize,
    next_padding: usize,
}

impl Layout {
    fn new(round: usize) -> Self {
        let bytes = hash_size(round);
        let next_words = bytes.div_ceil(4);
        let previous_bytes = if round == 0 { 0 } else { hash_size(round - 1) };
        let previous_words = previous_bytes.div_ceil(4);
        Self {
            previous_words,
            next_words,
            previous_padding: previous_words * 4 - previous_bytes,
            next_padding: next_words * 4 - bytes,
        }
    }
}

const fn hash_size(round: usize) -> usize {
    (SOLVER_PARAMS.n as usize - (round + 1) * DIGIT_BITS + REST_BITS).div_ceil(8)
}

fn tree(bucket: usize, left: usize, right: usize) -> u32 {
    (((bucket as u32) << SLOT_BITS | left as u32) << SLOT_BITS) | right as u32
}

fn children(node: u32) -> (usize, usize, usize) {
    (
        (node >> (2 * SLOT_BITS)) as usize,
        ((node >> SLOT_BITS) & SLOT_MASK) as usize,
        (node & SLOT_MASK) as usize,
    )
}

fn attributes(round: usize, bucket: usize) -> usize {
    bucket * SLOTS * TABLE_WORDS[round & 1] + (round / 2) * SLOTS
}

// Prefetch only addresses inside a live table. On other architectures the
// ordinary reads and writes retain the same behavior.
#[allow(unsafe_code)]
fn prefetch(table: &[u32], index: usize) {
    #[cfg(target_arch = "x86_64")]
    {
        debug_assert!(index < table.len());
        // SAFETY: callers derive this index from a bounded bucket and slot,
        // and the reserved tree/hash widths fit in the allocated table.
        unsafe {
            core::arch::x86_64::_mm_prefetch(
                table.as_ptr().add(index).cast(),
                core::arch::x86_64::_MM_HINT_T0,
            );
        }
    }
    #[cfg(not(target_arch = "x86_64"))]
    let _ = (table, index);
}

struct Collisions {
    counts: [u16; RESTS],
    slots: [[u16; COLLISION_CAPACITY]; RESTS],
}

impl Collisions {
    fn new() -> Self {
        Self {
            counts: [0; RESTS],
            slots: [[0; COLLISION_CAPACITY]; RESTS],
        }
    }

    fn clear(&mut self) {
        self.counts.fill(0);
    }

    fn add(&mut self, slot: usize, key: usize) -> Option<&[u16]> {
        let count = self.counts[key] as usize;
        self.counts[key] += 1;
        if count >= COLLISION_CAPACITY {
            return None;
        }
        let slots = &mut self.slots[key];
        slots[count] = slot as u16;
        Some(&slots[..count])
    }
}

#[derive(Clone, Copy, Default)]
struct ActiveRow {
    right: u16,
    key: u8,
    previous: u8,
}

#[derive(Clone, Copy)]
struct InitialOutput<'a> {
    attribute: usize,
    hash: usize,
    source: &'a [u8; INITIAL_BYTES],
    index: u32,
}

fn flush_initial(table: &mut [u32], pending: &[InitialOutput<'_>]) {
    for output in pending {
        table[output.attribute] = output.index;
        let (source, remainder) = output.source.as_chunks::<4>();
        debug_assert!(remainder.is_empty());
        let destination = &mut table[output.hash..output.hash + INITIAL_WORDS];
        for (destination, source) in destination.iter_mut().zip(source) {
            *destination = u32::from_ne_bytes(*source);
        }
    }
}

#[derive(Clone, Copy)]
struct RowOutput<'a, const WORDS: usize> {
    attribute: usize,
    hash: usize,
    node: u32,
    left: &'a [u32; WORDS],
    right: &'a [u32; WORDS],
}

fn flush_rows<const PREVIOUS: usize, const NEXT: usize>(
    next: &mut [u32],
    pending: &[RowOutput<'_, PREVIOUS>],
) {
    for output in pending {
        next[output.attribute] = output.node;
        let destination: &mut [u32; NEXT] = (&mut next[output.hash..output.hash + NEXT])
            .try_into()
            .unwrap();
        for (word, destination) in destination.iter_mut().enumerate() {
            *destination =
                output.left[word + PREVIOUS - NEXT] ^ output.right[word + PREVIOUS - NEXT];
        }
    }
}

fn row_byte<const WORDS: usize>(row: &[u32; WORDS], offset: usize) -> u8 {
    row[offset / 4].to_ne_bytes()[offset % 4]
}

fn row_extra_hash<const WORDS: usize>(row: &[u32; WORDS], padding: usize, odd: bool) -> usize {
    if odd {
        (((row_byte(row, padding) & 0xf) as usize) << 4)
            | (row_byte(row, padding + 1) >> 4) as usize
    } else {
        row_byte(row, padding) as usize
    }
}

fn row_bucket<const WORDS: usize>(
    left: &[u32; WORDS],
    right: &[u32; WORDS],
    padding: usize,
    odd: bool,
) -> usize {
    let first = row_byte(left, padding + 1) ^ row_byte(right, padding + 1);
    let second = row_byte(left, padding + 2) ^ row_byte(right, padding + 2);
    if odd {
        (((first & 0xf) as usize) << 8) | second as usize
    } else {
        ((first as usize) << 4) | (second >> 4) as usize
    }
}

// Full-word matches form insertion-ordered chains. Epoch tags reuse the
// map between buckets without clearing every key, head or tail.
struct FinalGroups {
    keys: [u32; FINAL_MAP_SIZE],
    tags: [u32; FINAL_MAP_SIZE],
    heads: [u16; FINAL_MAP_SIZE],
    tails: [u16; FINAL_MAP_SIZE],
    next: [u16; SLOTS],
    epoch: u32,
}

impl FinalGroups {
    fn new() -> Self {
        // At most one entry exists per retained source row. The spare entry
        // guarantees termination of linear probing, even for adverse words.
        assert!(FINAL_MAP_SIZE.is_power_of_two() && FINAL_MAP_SIZE > SLOTS);
        Self {
            keys: [0; FINAL_MAP_SIZE],
            tags: [0; FINAL_MAP_SIZE],
            heads: [0; FINAL_MAP_SIZE],
            tails: [0; FINAL_MAP_SIZE],
            next: [0; SLOTS],
            epoch: 0,
        }
    }

    fn advance_epoch(&mut self) {
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.tags.fill(0);
            self.epoch = 1;
        }
    }

    fn insert(&mut self, right: usize, word: u32) -> Option<(u16, u16)> {
        debug_assert!(right < SLOTS);
        let mut position = (word.wrapping_mul(HASH_TABLE_MULTIPLIER)
            >> (u32::BITS as usize - FINAL_MAP_BITS)) as usize;
        loop {
            if self.tags[position] != self.epoch {
                self.keys[position] = word;
                self.tags[position] = self.epoch;
                self.heads[position] = right as u16;
                self.tails[position] = right as u16;
                return None;
            }
            if self.keys[position] == word {
                let head = self.heads[position];
                let tail = self.tails[position];
                self.next[tail as usize] = right as u16;
                self.tails[position] = right as u16;
                return Some((head, tail));
            }
            position = (position + 1) & FINAL_MAP_MASK;
        }
    }
}

// Apply the original per-rest cap before considering full-word equality.
// Equal complete words necessarily have the same rest key. Their retained
// slot chains therefore emit the same prior matches in the same order.
fn collect_final_candidates(
    bucket: usize,
    rows: &[[u32; FINAL_WORDS]],
    groups: &mut FinalGroups,
    candidates: &mut Vec<u32>,
) {
    groups.advance_epoch();
    let mut rest_counts = [0_u16; RESTS];
    let layout = Layout::new(ROUNDS);
    for (right, right_row) in rows.iter().enumerate() {
        let key = row_extra_hash(right_row, layout.previous_padding, true);
        let previous = rest_counts[key] as usize;
        rest_counts[key] += 1;
        if previous >= COLLISION_CAPACITY {
            continue;
        }
        let Some((mut left, tail)) = groups.insert(right, right_row[0]) else {
            continue;
        };
        loop {
            candidates.push(tree(bucket, left as usize, right));
            if left == tail {
                break;
            }
            left = groups.next[left as usize];
        }
    }
}

/// Owns the tables for one single-threaded Tromp solver instance.
pub(super) struct Solver {
    tables: [Table; 2],
    counts: [[u32; BUCKETS]; 2],
    index_keys: [u32; 2 * PROOF_SIZE],
    index_tags: [u32; 2 * PROOF_SIZE],
    index_epoch: u32,
    solutions: Vec<Vec<u32>>,
}

impl Solver {
    pub(super) fn new() -> Self {
        for round in 0..ROUNDS {
            assert!(round / 2 + 1 + Layout::new(round).next_words <= TABLE_WORDS[round & 1]);
        }
        Self {
            tables: [
                Table::new_zeroed(BUCKETS * SLOTS * TABLE_WORDS[0]),
                Table::new_zeroed(BUCKETS * SLOTS * TABLE_WORDS[1]),
            ],
            counts: [[0; BUCKETS]; 2],
            index_keys: [0; 2 * PROOF_SIZE],
            index_tags: [0; 2 * PROOF_SIZE],
            index_epoch: 0,
            solutions: Vec::with_capacity(MAX_SOLUTIONS),
        }
    }

    pub(super) fn run(&mut self, state: &SolverHashState) -> Vec<Vec<u32>> {
        self.counts[0].fill(0);
        self.index_tags.fill(0);
        self.index_epoch = 0;
        self.solutions.clear();
        self.initial(state);
        self.round::<1, { HASH_WORDS[0] }, { HASH_WORDS[1] }>();
        self.round::<2, { HASH_WORDS[1] }, { HASH_WORDS[2] }>();
        self.round::<3, { HASH_WORDS[2] }, { HASH_WORDS[3] }>();
        self.round::<4, { HASH_WORDS[3] }, { HASH_WORDS[4] }>();
        self.round::<5, { HASH_WORDS[4] }, { HASH_WORDS[5] }>();
        self.round::<6, { HASH_WORDS[5] }, { HASH_WORDS[6] }>();
        self.round::<7, { HASH_WORDS[6] }, { HASH_WORDS[7] }>();
        self.round::<8, { HASH_WORDS[7] }, { HASH_WORDS[8] }>();
        self.final_round();
        let mut solutions = core::mem::take(&mut self.solutions);
        solutions.sort();
        solutions.dedup();
        solutions
    }

    fn initial(&mut self, state: &SolverHashState) {
        let layout = Layout::new(0);
        debug_assert_eq!(layout.next_padding, 0);
        let mut hashes = [0; HASH_BATCH * HASH_OUTPUT];
        let table = &mut self.tables[0];
        let counts = &mut self.counts[0];
        for block in (0..HASH_BLOCKS).step_by(HASH_BATCH) {
            let count = HASH_BATCH.min(HASH_BLOCKS - block);
            state.generate(block as u32, &mut hashes[..count * HASH_OUTPUT]);
            let dummy = hashes[..INITIAL_BYTES].try_into().unwrap();
            let mut pending = [InitialOutput {
                attribute: 0,
                hash: 0,
                source: dummy,
                index: 0,
            }; HASH_BATCH];
            let mut buffered = 0;
            let (digests, remainder) = hashes[..count * HASH_OUTPUT].as_chunks::<HASH_OUTPUT>();
            debug_assert!(remainder.is_empty());
            for (offset, digest) in digests.iter().enumerate() {
                let (parts, remainder) = digest.as_chunks::<HASH_BYTES>();
                debug_assert!(remainder.is_empty());
                for (part, source) in parts.iter().enumerate() {
                    let bucket = ((source[0] as usize) << 4) | (source[1] >> 4) as usize;
                    let slot = counts[bucket] as usize;
                    counts[bucket] += 1;
                    if slot >= SLOTS {
                        continue;
                    }
                    let attr = attributes(0, bucket) + slot;
                    let hash = attributes(0, bucket) + SLOTS + slot * layout.next_words;
                    prefetch(table, attr);
                    prefetch(table, hash);
                    prefetch(table, hash + layout.next_words - 1);
                    pending[buffered] = InitialOutput {
                        attribute: attr,
                        hash,
                        source: source[HASH_BYTES - INITIAL_BYTES..].try_into().unwrap(),
                        index: ((block + offset) * HASHES_PER_BLAKE + part) as u32,
                    };
                    buffered += 1;
                    if buffered == HASH_BATCH {
                        flush_initial(table, &pending);
                        buffered = 0;
                    }
                }
            }
            flush_initial(table, &pending[..buffered]);
        }
    }

    fn round<const ROUND: usize, const PREVIOUS: usize, const NEXT: usize>(&mut self) {
        let round = ROUND;
        let layout = Layout::new(round);
        let odd = round & 1 != 0;
        let [first, second] = &mut self.tables;
        let (previous, next): (&[u32], &mut [u32]) = if odd {
            (first, second)
        } else {
            (second, first)
        };
        let [first, second] = &mut self.counts;
        let (previous_counts, next_counts) = if odd {
            (first, second)
        } else {
            (second, first)
        };
        let mut collisions = Collisions::new();
        let mut active = [ActiveRow::default(); SLOTS];
        debug_assert_eq!(layout.previous_words, PREVIOUS);
        debug_assert_eq!(layout.next_words, NEXT);
        let dummy: &[u32; PREVIOUS] = previous[..PREVIOUS].try_into().unwrap();
        let mut pending = [RowOutput {
            attribute: 0,
            hash: 0,
            node: 0,
            left: dummy,
            right: dummy,
        }; OUTPUT_BATCH];
        let mut buffered = 0;
        for (bucket, previous_count) in previous_counts.iter_mut().enumerate() {
            collisions.clear();
            let rows = attributes(round - 1, bucket) + SLOTS;
            let count = (*previous_count as usize).min(SLOTS);
            *previous_count = 0;
            let input = &previous[rows..rows + count * PREVIOUS];
            let (rows, remainder) = input.as_chunks::<PREVIOUS>();
            debug_assert!(remainder.is_empty());
            let mut active_count = 0;
            for (right, right_row) in rows.iter().enumerate() {
                let key = row_extra_hash(right_row, layout.previous_padding, odd);
                let previous = collisions.counts[key] as usize;
                let _ = collisions.add(right, key);
                // The first row cannot be active, so even this unconditional
                // write has a spare descriptor throughout the input scan.
                active[active_count] = ActiveRow {
                    right: right as u16,
                    key: key as u8,
                    previous: previous.min(COLLISION_CAPACITY) as u8,
                };
                active_count += usize::from(previous != 0 && previous < COLLISION_CAPACITY);
            }
            for descriptor in &active[..active_count] {
                let right = descriptor.right as usize;
                let right_row = &rows[right];
                let colliding =
                    &collisions.slots[descriptor.key as usize][..descriptor.previous as usize];
                for &current_left in colliding {
                    let current_left = current_left as usize;
                    let left_row = &rows[current_left];
                    if left_row[PREVIOUS - 1] == right_row[PREVIOUS - 1] {
                        continue;
                    }
                    let next_bucket = row_bucket(left_row, right_row, layout.previous_padding, odd);
                    let slot = next_counts[next_bucket] as usize;
                    next_counts[next_bucket] += 1;
                    if slot >= SLOTS {
                        continue;
                    }
                    let attr = attributes(round, next_bucket) + slot;
                    let hash = attributes(round, next_bucket) + SLOTS + slot * layout.next_words;
                    prefetch(next, attr);
                    prefetch(next, hash);
                    prefetch(next, hash + layout.next_words - 1);
                    pending[buffered] = RowOutput {
                        attribute: attr,
                        hash,
                        node: tree(bucket, current_left, right),
                        left: left_row,
                        right: right_row,
                    };
                    buffered += 1;
                    if buffered == OUTPUT_BATCH {
                        flush_rows::<PREVIOUS, NEXT>(next, &pending);
                        buffered = 0;
                    }
                }
            }
        }
        flush_rows::<PREVIOUS, NEXT>(next, &pending[..buffered]);
    }

    fn final_round(&mut self) {
        let mut groups = FinalGroups::new();
        let mut candidates = Vec::with_capacity(COLLISION_CAPACITY);
        for bucket in 0..BUCKETS {
            let count = (self.counts[0][bucket] as usize).min(SLOTS);
            self.counts[0][bucket] = 0;
            let start = attributes(ROUNDS - 1, bucket) + SLOTS;
            let input = &self.tables[0][start..start + count * FINAL_WORDS];
            let (rows, remainder) = input.as_chunks::<FINAL_WORDS>();
            debug_assert!(remainder.is_empty());
            candidates.clear();
            collect_final_candidates(bucket, rows, &mut groups, &mut candidates);
            for &node in &candidates {
                self.candidate(node);
            }
        }
    }

    fn candidate(&mut self, node: u32) {
        self.index_epoch = self.index_epoch.wrapping_add(1);
        if self.index_epoch == 0 {
            self.index_tags.fill(0);
            self.index_epoch = 1;
        }
        if self.unique(ROUNDS, node) && self.solutions.len() < MAX_SOLUTIONS {
            let mut proof = vec![0; PROOF_SIZE];
            self.list(ROUNDS, node, &mut proof);
            self.solutions.push(proof);
        }
    }

    fn unique(&mut self, round: usize, node: u32) -> bool {
        if round == 0 {
            let mut slot =
                (node.wrapping_mul(HASH_TABLE_MULTIPLIER) >> (32 - (ROUNDS + 1))) as usize;
            while self.index_tags[slot] == self.index_epoch {
                if self.index_keys[slot] == node {
                    return false;
                }
                slot = (slot + 1) & (2 * PROOF_SIZE - 1);
            }
            self.index_tags[slot] = self.index_epoch;
            self.index_keys[slot] = node;
            return true;
        }
        let (bucket, left, right) = children(node);
        let previous = round - 1;
        let attr = attributes(previous, bucket);
        let left = self.tables[previous & 1][attr + left];
        let right = self.tables[previous & 1][attr + right];
        self.unique(previous, left) && self.unique(previous, right)
    }

    fn list(&self, round: usize, node: u32, proof: &mut [u32]) {
        if round == 0 {
            proof[0] = node;
            return;
        }
        let (bucket, left, right) = children(node);
        let previous = round - 1;
        let attr = attributes(previous, bucket);
        let size = 1 << previous;
        let (first, second) = proof.split_at_mut(size);
        self.list(previous, self.tables[previous & 1][attr + left], first);
        self.list(previous, self.tables[previous & 1][attr + right], second);
        if first[0] > second[0] {
            first.swap_with_slice(second);
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::{
        COLLISION_CAPACITY, Collisions, MAX_SOLUTIONS, PROOF_SIZE, RESTS, ROUNDS, SLOTS, Solver,
        attributes, tree,
    };

    #[test]
    fn final_scan_preserves_candidate_order_capacity_and_reset() {
        let mut groups = super::FinalGroups::new();
        let mut candidates = Vec::new();
        for pattern in 0..5 {
            let mut rows = Vec::new();
            let mut reference = vec![Vec::new(); RESTS];
            let mut expected = Vec::new();
            for right in 0..SLOTS {
                let key = match pattern {
                    0 | 2 => 7,
                    1 => right % 3,
                    4 => right / COLLISION_CAPACITY,
                    _ => (right * 97 + right / 5) % RESTS,
                };
                let payload = match pattern {
                    0 | 1 | 4 => 0,
                    2 => right % 2,
                    _ => right % 4,
                };
                let word = u32::from_ne_bytes([
                    (key >> 4) as u8,
                    ((key & 0xf) << 4) as u8,
                    payload as u8,
                    0,
                ]);
                rows.push([word]);
                let previous = &mut reference[key];
                if previous.len() == COLLISION_CAPACITY {
                    continue;
                }
                for &(left, left_word) in previous.iter() {
                    if left_word == word {
                        expected.push(tree(pattern, left, right));
                    }
                }
                previous.push((right, word));
            }
            candidates.clear();
            super::collect_final_candidates(pattern, &rows, &mut groups, &mut candidates);
            assert_eq!(candidates, expected);
            // Old epoch-one entries must not survive wraparound.
            groups.epoch = u32::MAX;
            candidates.clear();
            super::collect_final_candidates(pattern, &rows, &mut groups, &mut candidates);
            assert_eq!(groups.epoch, 1);
            assert_eq!(candidates, expected);
        }
    }

    #[test]
    fn collision_groups_preserve_insertion_order_capacity_and_reset() {
        let mut collisions = Collisions::new();
        for pattern in 0..4 {
            collisions.clear();
            let mut reference = vec![Vec::new(); RESTS];
            for slot in 0..SLOTS {
                let key = match pattern {
                    0 => 7,
                    1 => slot % RESTS,
                    2 => slot % 8,
                    _ => (slot * 97 + slot / 5) % RESTS,
                };
                let previous = &mut reference[key];
                let result = collisions.add(slot, key);
                if previous.len() == COLLISION_CAPACITY {
                    assert!(result.is_none());
                    continue;
                }
                let expected: Vec<_> = previous.iter().map(|&slot| slot as u16).collect();
                assert_eq!(result.unwrap(), expected);
                previous.push(slot);
            }
        }
    }

    #[test]
    fn repeated_leaf_rejection_solution_cap_and_epoch_wrap() {
        let mut solver = Solver::new();
        // A complete tree with distinct leaves exercises extraction and the
        // uniqueness set independently of the final hash collision test.
        for index in 0..PROOF_SIZE {
            solver.tables[0][attributes(0, 0) + index] = index as u32;
        }
        for round in 1..ROUNDS {
            for index in 0..PROOF_SIZE >> round {
                solver.tables[round & 1][attributes(round, 0) + index] =
                    tree(0, 2 * index, 2 * index + 1);
            }
        }
        solver.candidate(tree(0, 0, 0));
        assert!(solver.solutions.is_empty());
        solver.index_epoch = u32::MAX;
        for _ in 0..MAX_SOLUTIONS + 2 {
            solver.candidate(tree(0, 0, 1));
        }
        assert_eq!(solver.solutions.len(), MAX_SOLUTIONS);
        let expected: Vec<_> = (0..PROOF_SIZE as u32).collect();
        assert!(solver.solutions.iter().all(|proof| *proof == expected));
        assert_eq!(solver.index_epoch, (MAX_SOLUTIONS + 2) as u32);
    }
}
