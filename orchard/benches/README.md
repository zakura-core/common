# Orchard proving and verification benchmarks

These harnesses exercise the complete one-Action Orchard proving and
verification paths. They are intended for controlled comparisons between two
already-built revisions, not for microbenchmarking isolated arithmetic.

## Merkle hashing

The Merkle harness measures one parent hash and construction of complete
subtrees, scalar and batched: a 1,024-leaf tree of seeded random leaves, and
the 2,048-leaf edge-case fixture shared with the library's fixed-vector test
(`orchard::tree::testing::fixture_leaves`, which is why the bench needs the
`test-dependencies` feature; add `weighted-merkle` to time that evaluator):

```console
cargo +1.88 bench --locked -p zakura-orchard --features test-dependencies --bench merkle
```

The fixture's distinct leaves mix the protocol's special values, single-bit
and single-Sinsemilla-word patterns, and the empty roots into a BLAKE2b fill,
so the timed tree contains inputs that random sampling never produces, and
`tree::tests::fixture_tree_matches_vectors` pins the same tree's nodes to
fixed vectors. The deterministic leaves are generated outside the timed
routines. Criterion also excludes the per-sample clone of the leaf vector from
the whole-tree measurement.

## One-Action prover

Build or run the Criterion target with one Rayon worker:

```console
RAYON_NUM_THREADS=1 cargo +1.88 bench --locked \
    -p zakura-orchard --features circuit \
    --bench orchard_k11_prover
```

Key generation and one genuine proof-verification preflight occur before the
timed routine. The benchmark uses ten flat samples, a two-second warmup, and a
15-second measurement interval.

## Batch verifier fixture corpus

The batch-verifier harness is an ignored library test because it needs access
to Orchard's internal Halo 2 instance representation. Build the test binary
without running it:

```console
cargo +1.88 test --locked --release \
    -p zakura-orchard --features circuit --lib --no-run
```

Cargo prints the test executable path. Copy that executable to a stable path
before timing. Build both revisions before starting any benchmark leg.

Generate one corpus from the control binary:

```console
RAYON_NUM_THREADS=1 \
ORCHARD_BATCH_FIXTURE_CORPUS=/absolute/path/orchard-batch-v1.bin \
ORCHARD_BATCH_FIXTURE_GENERATE=1 \
./orchard-test-control --ignored --exact \
    circuit::benchmark::benchmark_batch_verifier \
    --test-threads=1 --nocapture
```

The corpus contains 64 deterministic, distinct, valid one-Action proofs. The
output path must not already exist. Record its SHA-256 hash and reuse the same
bytes for every binary:

```console
RAYON_NUM_THREADS=1 \
ORCHARD_BATCH_FIXTURE_CORPUS=/absolute/path/orchard-batch-v1.bin \
./orchard-test-candidate --ignored --exact \
    circuit::benchmark::benchmark_batch_verifier \
    --test-threads=1 --nocapture
```

Before timing, every invocation checks the corpus encoding, proof count,
proof uniqueness, and a complete 64-proof batch verification. Corpus loading
and this validation are outside the timed region.

The standard run measures batch sizes 1, 2, 16, and 64 with three warmups and
15 samples per size. Set `ORCHARD_BATCH_SCREEN=1` only for diagnostic screens;
that mode measures batch sizes 1 and 64 with one warmup and seven samples.

## Comparison protocol

For final comparisons:

1. Build and hash both source revisions and all binaries before timing.
2. Generate and hash the fixture corpus once, then reuse it byte-for-byte.
3. Keep the machine on external power and free of competing build or benchmark
   processes.
4. Set `RAYON_NUM_THREADS=1` for every preflight and timed leg.
5. Qualify the host with two control runs before comparing revisions.
6. Run one balanced control/candidate/candidate/control bracket.
7. Retain raw samples, binary and corpus hashes, source commits, feature sets,
   and pre/post host telemetry.

Do not generate proofs, compile code, or load the fixture file inside a timed
sample.
