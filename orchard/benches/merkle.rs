use std::collections::HashSet;
use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion, Throughput};
use group::ff::{FromUniformBytes, PrimeField};
use incrementalmerkletree::{Hashable, Level};
use orchard::tree::MerkleHashOrchard;
use pasta_curves::pallas;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

/// A 1,024-leaf subtree is large enough to amortize fixed hash setup.
const TREE_HEIGHT: usize = 10;
const TREE_LEAVES: usize = 1 << TREE_HEIGHT;
/// A full binary tree has one fewer parent than leaves.
const TREE_INTERNAL_NODES: usize = TREE_LEAVES - 1;
/// Width required by the field's uniform-byte reduction.
const UNIFORM_BYTES: usize = 64;
/// Orchard's note-commitment tree is binary.
const CHILDREN_PER_PARENT: usize = 2;
/// Position of the left child in each binary chunk.
const LEFT_CHILD: usize = 0;
/// Position of the right child in each binary chunk.
const RIGHT_CHILD: usize = 1;
/// Byte width required by `ChaCha20Rng::from_seed`.
const RNG_SEED_BYTES: usize = 32;
/// Fixed deterministic seed used only to make benchmark revisions comparable.
const FIXTURE_SEED: [u8; RNG_SEED_BYTES] = [0x53; RNG_SEED_BYTES];
/// Level used when hashing pairs of leaves.
const LEAF_PARENT_LEVEL: u8 = 0;
/// A 4,096-leaf subtree of pairwise-distinct leaves, generated once.
const DISTINCT_TREE_HEIGHT: usize = 12;
const DISTINCT_TREE_LEAVES: usize = 1 << DISTINCT_TREE_HEIGHT;
const DISTINCT_TREE_INTERNAL_NODES: usize = DISTINCT_TREE_LEAVES - 1;
/// Seed of the stream the distinct leaves are drawn from. Differs from
/// `FIXTURE_SEED` so the two trees never share a leaf.
const DISTINCT_SEED: [u8; RNG_SEED_BYTES] = [0xd1; RNG_SEED_BYTES];

fn fixture_leaves() -> Vec<MerkleHashOrchard> {
    let mut rng = ChaCha20Rng::from_seed(FIXTURE_SEED);

    (0..TREE_LEAVES)
        .map(|_| {
            let mut uniform = [0; UNIFORM_BYTES];
            rng.fill_bytes(&mut uniform);
            let value = pallas::Base::from_uniform_bytes(&uniform);
            MerkleHashOrchard::from_bytes(&value.to_repr()).unwrap()
        })
        .collect()
}

/// Draws `count` leaves from `rng`, rejecting any repeat, so every leaf in
/// the returned tree is a distinct field element by construction rather than
/// by probability.
fn distinct_leaves(rng: &mut ChaCha20Rng, count: usize) -> Vec<MerkleHashOrchard> {
    let mut seen = HashSet::with_capacity(count);
    let mut leaves = Vec::with_capacity(count);
    while leaves.len() < count {
        let mut uniform = [0; UNIFORM_BYTES];
        rng.fill_bytes(&mut uniform);
        let value = pallas::Base::from_uniform_bytes(&uniform);
        if seen.insert(value.to_repr()) {
            leaves.push(MerkleHashOrchard::from_bytes(&value.to_repr()).unwrap());
        }
    }
    leaves
}

fn merkle_root(mut nodes: Vec<MerkleHashOrchard>) -> MerkleHashOrchard {
    let mut level = 0;

    while nodes.len() > 1 {
        let merkle_level =
            Level::from(u8::try_from(level).expect("benchmark tree height fits in u8"));
        nodes = nodes
            .as_chunks::<CHILDREN_PER_PARENT>()
            .0
            .iter()
            .map(|children| {
                MerkleHashOrchard::combine(
                    merkle_level,
                    &children[LEFT_CHILD],
                    &children[RIGHT_CHILD],
                )
            })
            .collect();
        level += 1;
    }

    nodes.pop().expect("benchmark tree is non-empty")
}

fn merkle_root_batch(mut nodes: Vec<MerkleHashOrchard>) -> MerkleHashOrchard {
    let mut level = 0;

    while nodes.len() > 1 {
        let merkle_level =
            Level::from(u8::try_from(level).expect("benchmark tree height fits in u8"));
        nodes = MerkleHashOrchard::combine_batch(
            merkle_level,
            nodes
                .as_chunks::<CHILDREN_PER_PARENT>()
                .0
                .iter()
                .map(|children| (&children[LEFT_CHILD], &children[RIGHT_CHILD])),
        );
        level += 1;
    }

    nodes.pop().expect("benchmark tree is non-empty")
}

fn benchmark_merkle(c: &mut Criterion) {
    let leaves = fixture_leaves();
    let distinct = distinct_leaves(
        &mut ChaCha20Rng::from_seed(DISTINCT_SEED),
        DISTINCT_TREE_LEAVES,
    );
    let level = Level::from(LEAF_PARENT_LEVEL);

    c.bench_function("orchard-merkle-combine", |bencher| {
        bencher.iter(|| {
            black_box(MerkleHashOrchard::combine(
                level,
                black_box(&leaves[LEFT_CHILD]),
                black_box(&leaves[RIGHT_CHILD]),
            ))
        });
    });

    let mut group = c.benchmark_group("orchard-merkle-tree");
    group.throughput(Throughput::Elements(TREE_INTERNAL_NODES as u64));
    group.bench_function(format!("{TREE_LEAVES}-leaves"), |bencher| {
        bencher.iter_batched(
            || leaves.clone(),
            |leaves| black_box(merkle_root(leaves)),
            BatchSize::LargeInput,
        );
    });
    group.bench_function(format!("{TREE_LEAVES}-leaves-batch"), |bencher| {
        bencher.iter_batched(
            || leaves.clone(),
            |leaves| black_box(merkle_root_batch(leaves)),
            BatchSize::LargeInput,
        );
    });

    // One fixed vector of pairwise-distinct leaves, generated once above
    // and cloned per sample exactly like the 1,024-leaf cases.
    group.throughput(Throughput::Elements(DISTINCT_TREE_INTERNAL_NODES as u64));
    group.bench_function(
        format!("{DISTINCT_TREE_LEAVES}-leaves-distinct"),
        |bencher| {
            bencher.iter_batched(
                || distinct.clone(),
                |leaves| black_box(merkle_root(leaves)),
                BatchSize::LargeInput,
            );
        },
    );
    group.bench_function(
        format!("{DISTINCT_TREE_LEAVES}-leaves-distinct-batch"),
        |bencher| {
            bencher.iter_batched(
                || distinct.clone(),
                |leaves| black_box(merkle_root_batch(leaves)),
                BatchSize::LargeInput,
            );
        },
    );
    group.finish();
}

criterion_group!(benches, benchmark_merkle);
criterion_main!(benches);
