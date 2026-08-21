use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion, Throughput};
use group::ff::{FromUniformBytes, PrimeField};
use incrementalmerkletree::{Hashable, Level};
use orchard::tree::{
    testing::{fixture_leaves as edge_fixture_leaves, FIXTURE_LEAVES},
    MerkleHashOrchard,
};
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

    // The 2,048-leaf edge-case fixture shared with the library's fixed-vector
    // test (`tree::tests::fixture_tree_matches_vectors`): distinct leaves
    // mixing protocol special values, single-bit and single-word patterns,
    // and empty roots into a BLAKE2b fill, so the timed tree contains the
    // inputs that random sampling never produces.
    let fixture = edge_fixture_leaves();
    group.throughput(Throughput::Elements((FIXTURE_LEAVES - 1) as u64));
    group.bench_function(format!("{FIXTURE_LEAVES}-leaves-fixture"), |bencher| {
        bencher.iter_batched(
            || fixture.clone(),
            |leaves| black_box(merkle_root(leaves)),
            BatchSize::LargeInput,
        );
    });
    group.bench_function(
        format!("{FIXTURE_LEAVES}-leaves-fixture-batch"),
        |bencher| {
            bencher.iter_batched(
                || fixture.clone(),
                |leaves| black_box(merkle_root_batch(leaves)),
                BatchSize::LargeInput,
            );
        },
    );
    group.finish();
}

criterion_group!(benches, benchmark_merkle);
criterion_main!(benches);
