# Ironwood proving and verification benchmarks

The workload-bearing harnesses use deterministic Ironwood V3 payments under
the post-NU6.3 circuit. Every payment Action has a real nonzero spend and
output to a different wallet. They are intended for controlled comparisons
between two already-built revisions, not for microbenchmarking isolated
arithmetic.

The commands below pin Rust 1.97.1 for comparable performance measurements.
This does not change the workspace's minimum supported Rust version of 1.91,
which is tested separately.

## Merkle hashing

The Merkle harness measures one parent hash and construction of complete
subtrees, scalar and batched:

```console
cargo +1.97.1 bench --locked -p zakura-orchard --bench merkle
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
RAYON_NUM_THREADS=1 cargo +1.97.1 bench --locked \
    -p zakura-orchard --features circuit \
    --bench ironwood_k11_prover
```

The `ironwood-k11` group measures steady-state throughput for one-, two-, and
four-Action proofs. The new ID is deliberate: these real Ironwood-payment
results are not comparable with the old Orchard V2 output-only workload. Key
generation, proving-key preparation, and a two-proof verification preflight
occur before its timed routines. The two preflight proofs per Action count use
distinct deterministic seeds on the same prepared key, exercising retained
state under different transcript challenges. The preflight and Criterion
warmup mean that every proving-key cache is populated before these samples; do
not interpret them as first-proof latency.

The `ironwood-k11-first-after-build-and-prepare` group measures one- and
four-Action semantic-cold proofs. Every iteration builds a fresh proving key,
successfully prepares its commitment tables, and then creates exactly one
proof with that key. Key generation, preparation, and destruction of the key
and its prepared tables are outside the reported duration. This makes lazy
per-key prover work visible even though Criterion's process, allocator, Rayon
pool, code pages, and operating-system caches remain warm. The group is not a
process-startup or cold-page-cache benchmark. It requires a build with either
the `multicore` or `orbits` feature and fails instead of silently measuring an
unprepared key when commitment-table preparation is unavailable.

Both groups use deterministic but varying proof RNG seeds, so consecutive
proofs have different transcript challenges and bytes. Seed construction and
RNG initialization happen outside the timed routines.

Both groups use ten flat samples, a two-second warmup, and a 15-second
measurement interval. The semantic-cold group is much more expensive in wall
time because it repeats key generation and roughly 25 MiB of commitment-table
preparation for every warmup and measured iteration, even though Criterion
excludes that setup from each reported proof duration.

For a multicore run, set both thread-count variables to the same value:

```console
RAYON_NUM_THREADS=10 IRONWOOD_K11_PROVER_THREADS=10 \
    cargo +1.97.1 bench --locked \
    -p zakura-orchard --features circuit \
    --bench ironwood_k11_prover
```

## Proving-key generation

The proving-key benchmark uses the post-NU6.3 circuit shared by the Orchard
and Ironwood V3 pools, and the same Criterion timing configuration:

```console
RAYON_NUM_THREADS=10 cargo +1.97.1 bench --locked \
    -p zakura-orchard --features circuit \
    --bench post_nu6_3_k11_keygen
```

## Note decryption

The decryption harness uses [`IronwoodDomain`] and genuine V3 ciphertexts. Its
batch rows contain 100 distinct Actions from 50 two-Action payments, rather
than cloning one ciphertext:

```console
cargo +1.97.1 bench --locked -p zakura-orchard --features circuit \
    --bench note_decryption
```

[`IronwoodDomain`]: ../src/note_encryption.rs

## Witness assignment

The ignored witness-assignment benchmark uses the production post-NU6.3
circuit with deterministic Ironwood payments. Every Action has a real V3 spend
and a nonzero output, and all spend witnesses share one valid anchor. The
benchmark reuses its V1 floor plan and writes every generated advice value to
benchmark storage. Circuit configuration, fixture generation, floor planning,
and per-sample configuration cloning are outside the timed regions. It measures
one-, two-, and four-Action synthesis with 50 warmups and 1,000 samples:

```console
RAYON_NUM_THREADS=10 cargo +1.97.1 test --locked --release \
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
cargo +1.97.1 test --locked --release \
    -p zakura-orchard --features circuit --lib --no-run
```

Cargo prints the test executable path. Copy that executable to a stable path
before timing. Build both revisions before starting any benchmark leg.

Generate one corpus from the control binary:

```console
RAYON_NUM_THREADS=1 \
IRONWOOD_BATCH_FIXTURE_CORPUS=/absolute/path/ironwood-batch-v2.bin \
IRONWOOD_BATCH_FIXTURE_GENERATE=1 \
./orchard-test-control --ignored --exact \
    circuit::benchmark::benchmark_ironwood_batch_verifier \
    --test-threads=1 --nocapture
```

The corpus contains 64 deterministic, distinct, valid two-Action Ironwood
payment proofs. Every Action has a real V3 spend and a nonzero output. The
output path must not already exist. Record its SHA-256 hash and reuse the same
bytes for every binary:

```console
RAYON_NUM_THREADS=1 \
IRONWOOD_BATCH_FIXTURE_CORPUS=/absolute/path/ironwood-batch-v2.bin \
./orchard-test-candidate --ignored --exact \
    circuit::benchmark::benchmark_ironwood_batch_verifier \
    --test-threads=1 --nocapture
```

Before timing, every invocation checks the corpus encoding, proof count,
proof uniqueness, and a complete 64-proof batch verification. Corpus loading
and this validation are outside the timed region.

The standard run measures batch sizes 1, 2, 16, and 64 with three warmups and
15 samples per size. Set `IRONWOOD_BATCH_SCREEN=1` only for diagnostic screens;
that mode measures batch sizes 1 and 64 with one warmup and seven samples.

## End-to-end batch validation

The ignored integration harness creates 64 distinct two-Action payments with
real proofs and RedPallas spend signatures, then measures [`BatchValidator`]
at several proof-batch and worker counts:

```console
cargo +1.97.1 test --locked --release -p zakura-orchard \
    --features circuit --test ironwood_batch_timings -- --ignored --nocapture
```

Set `IRONWOOD_ARM=1` to prepare the verifying key before validation. Fixture
construction, proving, and signing are outside every timed sample.

[`BatchValidator`]: ../src/bundle/batch.rs

## Comparison protocol

For final comparisons:

1. Build and hash both source revisions and all binaries before timing.
2. Generate and hash the fixture corpus once, then reuse it byte-for-byte.
3. Keep the machine on external power and free of competing build or benchmark
   processes.
4. Set `RAYON_NUM_THREADS` explicitly for every preflight and timed leg. For
   multicore prover runs, set `IRONWOOD_K11_PROVER_THREADS` to the same value.
5. Qualify the host with two control runs before comparing revisions.
6. Run one balanced control/candidate/candidate/control bracket.
7. Retain raw samples, binary and corpus hashes, source commits, feature sets,
   and pre/post host telemetry.

Do not generate proofs, compile code, or load the fixture file inside a timed
sample.
