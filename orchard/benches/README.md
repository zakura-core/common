# Orchard proving and verification benchmarks

These harnesses exercise complete Orchard proving and verification paths. They
are intended for controlled comparisons between two already-built revisions,
not for microbenchmarking isolated arithmetic.

## Merkle hashing

The Merkle harness measures one parent hash and construction of complete
subtrees, scalar and batched:

```console
cargo +1.88 bench --locked -p zakura-orchard --bench merkle
```

- `1024-leaves[-batch]`: one fixed vector of seeded pseudorandom leaves,
  reused for every sample (the per-sample clone is excluded from the
  measurement). This is the historical baseline.
- `4096-leaves-distinct[-batch]`: a 2^12-leaf tree of seeded pseudorandom
  leaves drawn with repeats rejected, so every leaf is distinct by
  construction; generated once and, like the 1,024-leaf cases, cloned per
  sample outside the measurement.

In both cases leaf generation happens outside the timed routines.

## Prover

Build or run the Criterion target with one Rayon worker:

```console
RAYON_NUM_THREADS=1 cargo +1.88 bench --locked \
    -p zakura-orchard --features circuit \
    --bench orchard_k11_prover
```

Key generation and genuine proof-verification preflights occur before the
timed routines. The benchmark measures one-, two-, and four-Action proofs with
ten flat samples, a two-second warmup, and a 15-second measurement interval.

For a multicore run, set both thread-count variables to the same value:

```console
RAYON_NUM_THREADS=10 ORCHARD_K11_PROVER_THREADS=10 \
    cargo +1.88 bench --locked \
    -p zakura-orchard --features circuit \
    --bench orchard_k11_prover
```

## Proving-key generation

The proving-key benchmark uses the same Orchard circuit and Criterion timing
configuration:

```console
RAYON_NUM_THREADS=10 cargo +1.88 bench --locked \
    -p zakura-orchard --features circuit \
    --bench orchard_k11_keygen
```

## Witness assignment

The ignored witness-assignment benchmark uses the production Orchard circuit,
reuses its V1 floor plan, and writes every generated advice value to benchmark
storage. Circuit configuration, fixture generation, floor planning, and
per-sample configuration cloning are outside the timed regions. It measures
one-, two-, and four-Action synthesis with 50 warmups and 1,000 samples:

```console
RAYON_NUM_THREADS=10 cargo +1.88 test --locked --release \
    -p zakura-orchard --features circuit --lib \
    circuit::benchmark::benchmark_witness_assignment \
    -- --ignored --exact --nocapture
```

Set `RAYON_NUM_THREADS=1` for a serial comparison. The benchmark backend uses
a `BTreeMap` to identify advice columns because column indices are intentionally
not public API; compare revisions with the same harness instead of treating its
absolute timings as complete-prover phase measurements.

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
4. Set `RAYON_NUM_THREADS` explicitly for every preflight and timed leg. For
   multicore prover runs, set `ORCHARD_K11_PROVER_THREADS` to the same value.
5. Qualify the host with two control runs before comparing revisions.
6. Run one balanced control/candidate/candidate/control bracket.
7. Retain raw samples, binary and corpus hashes, source commits, feature sets,
   and pre/post host telemetry.

Do not generate proofs, compile code, or load the fixture file inside a timed
sample.
