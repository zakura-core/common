# Ironwood proving and verification benchmarks

The workload-bearing harnesses use deterministic Ironwood V3 payments under
the post-NU6.3 circuit. Every payment Action has a real nonzero spend and
output to a different wallet. They are intended for controlled comparisons
between two already-built revisions, not for microbenchmarking isolated
arithmetic.

The commands below pin Rust 1.97.1 for comparable performance measurements.
This does not change the workspace's minimum supported Rust version of 1.97,
which is tested separately.

Every Criterion target requires `test-dependencies` for its fixture generators.
The commands below use the default Halo2 backend. For the public Criterion
targets, select Sensei with `--no-default-features` and replace the feature list
with `backend-sensei,circuit,multicore,zip32-addresses,test-dependencies`. The
library-internal witness-assignment and batch-verifier corpus harnesses are
Halo2-only.

## Merkle hashing

The Merkle harness measures one parent hash and construction of complete
subtrees, scalar and batched:

```console
cargo +1.97.1 bench --locked -p zakura-orchard --bench merkle \
    --features test-dependencies
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
    -p zakura-orchard --features circuit,test-dependencies \
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
time because it repeats key generation and roughly 29 MiB of commitment-table
preparation under the default no-orbits build (roughly 25 MiB with `orbits`)
for every warmup and measured iteration, even though Criterion excludes that
setup from each reported proof duration.

For a multicore run, set both thread-count variables to the same value:

```console
RAYON_NUM_THREADS=10 IRONWOOD_K11_PROVER_THREADS=10 \
    cargo +1.97.1 bench --locked \
    -p zakura-orchard --features circuit,test-dependencies \
    --bench ironwood_k11_prover
```

## Native versus Sensei comparison

The `sensei_compare` harness compares the two compiled Orchard backends:
`backend-halo2` (reported as **native**) and `backend-sensei`. Choose exactly
one of `--prover` or `--verifier`. From the workspace root, run:

```console
./scripts/sensei-bench --prover
./scripts/sensei-bench --prover --asm
./scripts/sensei-bench --prover --thorough
./scripts/sensei-bench --prover --asm --thorough
./scripts/sensei-bench --prover --workers 4
./scripts/sensei-bench --verifier
./scripts/sensei-bench --verifier --batch-sizes 2 16
```

The default is a quick comparison: two measured rounds, five samples per leg,
and at least one second of warmup per process. In prover mode this collects
twenty proofs per backend per Action count and typically takes about 30–45
seconds after compilation on a fast multicore machine. Slower machines and
unstable warmup take longer. Quick results are marked provisional; use
`--thorough` for the longer sampling and drift checks described below.
Explicit `--rounds`, `--samples-per-leg`, and `--warmup-seconds` values
override either preset.

### Builds and arithmetic parity

The Python 3.10+ driver builds the same `sensei_compare` Rust benchmark twice
in separate target directories: the native build uses Cargo defaults
(`backend-halo2`) plus `sensei-bench`, `test-dependencies`, and `portable`;
the Sensei build disables defaults and selects
`backend-sensei,circuit,multicore,std,zip32-addresses,test-dependencies,sensei-bench`
plus `portable`. Compilation finishes before any timing. Each binary links
only its own backend's cryptographic stack — the native build contains no
Sensei or Udon code, and the Sensei build contains no Pasta, Halo2, legacy
facade, or Sinsemilla code — and the driver rejects a build plan containing
the other backend's crates.

By default, both builds disable **all handwritten Pasta and Udon assembly on
every platform**, including AArch64 field arithmetic that target-specific
dependencies otherwise force on, and the x86-64 assembly both crates select
from the compiler's target features. Orchard's `portable` feature reaches
Pasta through the legacy facade and Udon through Sensei. The driver checks
Cargo's resolved features and the Pasta and Udon build-script configuration,
which records the backend each build actually selected, and rejects any
assembly-enabled build.

`--asm` enables the host architecture's handwritten assembly in **both**
backends: Orchard's `aarch64-asm` or `x86_64-asm` feature forwards to Pasta
for the native Halo2 prover and to Udon for Sensei's arithmetic. The host
must be AArch64, or x86-64 with the BMI2 and ADX extensions the assembly
requires; the driver refuses other hosts before building. It rejects a build
unless the selected Pasta assembly is active in every Pasta build (native) and
Sensei's runtime Udon dependency both enables its assembly feature and reports
the matching backend (Sensei). It also rejects an unexpected `portable`
override. Build metadata and the summary identify the selected mode and
architecture. `--asm` works with the quick default, `--thorough`, and all
budget/worker overrides.

Compiler optimizations remain enabled in both modes; Sensei retains its
default `sqrt-table-large` arithmetic feature. The benchmark-only
`sensei-bench` feature exposes the proof-only `circuit::ProofBatch` adapter
and Sensei's unstable worker controls; it does not select a backend.

Without `--workers`, each backend chooses its usual worker count, preserving
inherited settings such as `RAYON_NUM_THREADS`. Sensei normally chooses its
own private pool size and does not use that environment variable.
`--workers N` configures both backends to exactly N workers; unavailable or
mismatched counts fail the run. The report shows actual counts. Native
proving runs on the calling thread, preserving its usual
preprocessing/scheduling behavior. In verifier mode the worker initializes
only Sensei's verifier runtime, never its prover state.

### Prover mode

The workloads are an unpadded one-Action payment and a two-Action payment with
**two real spends**, recipient and change outputs. Each sample times
`bundle.authorization().create_proof(...)` with precomputed instances. Bundle,
witness, instance, key, and RNG preparation are outside the timer; Sensei's
Orchard-to-Sensei translation, request validation, and interface overhead are
inside it. Backend work derived from those inputs remains timed. Logging and
proof destruction are excluded. This harness performs no proof verification or
correctness preflight; correctness is covered by the test suites.

Each leg starts a fresh process, builds and prepares the key
(`ProvingKey::build` plus `prepare_proving()`, both untimed), and warms the
exact workload for at least ten proofs and one second of proving (five seconds
with `--thorough`). The last two five-proof windows must have medians within
5%. Warming continues for up to 30 seconds (or the requested minimum, if
longer); unresolved instability makes the result provisional. Both backends
receive matched deterministic seed sequences, with distinct domains for warmup
and measurement. Because every leg is a fresh process, Sensei's process-global
warm state and Halo2's per-key caches are both rebuilt inside the untimed
preparation and warmup, never inside a measured sample.

One settling round covering both workloads is discarded. Measured rounds
alternate ABBA and BAAB, where A is native and B is Sensei, and reverse
workload order each round. With `--thorough`, ten measured rounds each collect
twenty individually timed proofs in each of the four legs: **400 proofs per
backend per Action count**, 1,600 measured proofs total. This mode takes
several minutes after compilation, including at least 440 seconds of
per-process warmup; the quick default requires at least 24 seconds of warmup.
The driver performs no concurrent builds or proving legs. Keep other machine
activity representative of the environment you want to measure.

### Verifier mode

`--verifier` compares individual proofs and batches of **2, 16, and 64
distinct proofs**, each with either one Action or two real spends.
`--batch-sizes` replaces the batch sizes; passing it with no sizes measures
only individual proofs. Reported batch times are for the **whole batch**, not
per proof.

Before measurement, the native binary creates and verifies a shared corpus for
each Action count. Its size is the maximum of ten, the samples per leg, and
the largest batch. These proofs use the same deterministic payment instances
with distinct proving randomness, and the two backends produce byte-identical
proofs for identical inputs, so the Sensei legs verify the identical native
bytes. Corpus files and their BLAKE2b-256 hashes are retained in the run
directory; every worker reports the corpus hash and count, which the driver
checks. Paired legs use the same corpus entries in the same order, cycling
through them across samples. Every proof in a batch is distinct.

Each worker loads the corpus, reconstructs the public instances, builds its
verifying key, calls `prepare_batch_validation()` (a no-op for Halo2 without
`orbits`, matching production defaults), and verifies every corpus proof
before warming the workload. Individual samples time `Proof::verify`,
including instance translation, request validation, and backend verification.
Batch samples time `ProofBatch` construction, proof/instance copies and
queueing, translation, random weights, verification, and destruction of the
consumed batch. Corpus generation/loading, key preparation, and benchmark RNG
initialization are outside both timers. Sensei batch RNG seeds are
deterministic and independent of the corpus seeds; native Halo2 continues to
obtain its batch randomness internally. This measures proof verification
only; RedPallas signature checks are excluded, because the two backends ship
different RedPallas implementations.

Each Action count and batch size gets the full sampling budget. Defaults
therefore run eight cases and 96 fresh processes, with at least 96 seconds of
warmup plus setup. `--thorough` runs 352 processes and at least 1,760 seconds
of warmup, plus setup and samples. A quick verifier smoke run with smaller
batches is:

```console
./scripts/sensei-bench --verifier --batch-sizes 2 --rounds 2 \
    --samples-per-leg 2 --warmup-seconds 0 --workers 1
```

### Interpreting the report

The table reports observed warm minimum and pooled median milliseconds, with
round-bootstrap 95% confidence intervals for medians. Percentage time savings
are `100 × (native − Sensei) / native`: a drop from 100 ms to 75 ms is **25%
less time**, while 125 ms is **25% more time**. These are latency percentages,
not throughput multipliers. A separate paired comparison takes the median of
each round's percentage savings, with 10,000 deterministic bootstrap resamples
of complete paired rounds. This preserves within-round correlation. An
interval spanning zero is inconclusive. Intervals reflect this run's sampled
rounds; they cannot rule out systematic workload bias or all forms of machine
noise.

No outliers are trimmed. The minimum is the **observed** minimum, not a proven
lower bound; its range across rounds shows repeatability. A run is provisional
if warmup remains unstable, the first versus last three rounds drift by over
5%, a median confidence bound is over 5% from its estimate, or worker counts
change. Quick results, budgets below the thorough preset, and odd round counts
are provisional.

`--warmup-seconds 0` still requires ten calls and the stability check. Use
`--help` for all options. Each run creates a unique directory under
`target/sensei-bench/` (or the `--output` parent) containing preserved
binaries and SHA-256 hashes, compiler logs, JSONL leg output, `samples.csv`,
`summary.txt`, `summary.json`, and checkpointed `run.json`. Metadata records
the revision and dirty state, compiler, build commands, resolved arithmetic
features and cfgs, relevant environment, seeds, workers, timestamps, and
available load/power/thermal observations. Telemetry is best effort and does
not require privileges. Interruptions preserve completed legs and partial
worker logs; proving errors or incomplete output fail the run.

The seed domains, workloads, timed boundaries, and statistics are fixed
properties of the harness, so pooled per-backend medians from runs of the two
revisions on the same host are directly comparable under the
[comparison protocol](#comparison-protocol).

## Proving-key generation

The proving-key benchmark uses the post-NU6.3 circuit shared by the Orchard
and Ironwood V3 pools, and the same Criterion timing configuration:

```console
RAYON_NUM_THREADS=10 cargo +1.97.1 bench --locked \
    -p zakura-orchard --features circuit,test-dependencies \
    --bench post_nu6_3_k11_keygen
```

## Note decryption

The decryption harness uses [`IronwoodDomain`] and genuine V3 ciphertexts. Its
batch rows contain 100 distinct Actions from 50 two-Action payments, rather
than cloning one ciphertext:

```console
cargo +1.97.1 bench --locked -p zakura-orchard --features circuit,test-dependencies \
    --bench note_decryption
```

[`IronwoodDomain`]: ../src/note_encryption.rs

## Witness assignment (Halo2)

The ignored witness-assignment benchmark uses the production post-NU6.3
circuit with deterministic Ironwood payments. Every Action has a real V3 spend
and a nonzero output, and all spend witnesses share one valid anchor. The
benchmark reuses its V1 floor plan and writes every generated advice value to
benchmark storage. Circuit configuration, fixture generation, floor planning,
and per-sample configuration cloning are outside the timed regions. It measures
one-, two-, and four-Action synthesis with 50 warmups and 1,000 samples:

```console
RAYON_NUM_THREADS=10 cargo +1.97.1 test --locked --release \
    -p zakura-orchard --features circuit,test-dependencies --lib \
    circuit::halo2::benchmark::benchmark_witness_assignment \
    -- --ignored --exact --nocapture
```

Set `RAYON_NUM_THREADS=1` for a serial comparison. The benchmark backend uses
a `BTreeMap` to identify advice columns because column indices are intentionally
not public API; compare revisions with the same harness instead of treating its
absolute timings as complete-prover phase measurements.

## Batch verifier fixture corpus (Halo2)

The batch-verifier harness is an ignored library test because it needs access
to Orchard's internal Halo 2 instance representation. Build the test binary
without running it:

```console
cargo +1.97.1 test --locked --release \
    -p zakura-orchard --features circuit,test-dependencies --lib --no-run
```

Cargo prints the test executable path. Copy that executable to a stable path
before timing. Build both revisions before starting any benchmark leg.

Generate one corpus from the control binary:

```console
RAYON_NUM_THREADS=1 \
IRONWOOD_BATCH_FIXTURE_CORPUS=/absolute/path/ironwood-batch-v2.bin \
IRONWOOD_BATCH_FIXTURE_GENERATE=1 \
./orchard-test-control --ignored --exact \
    circuit::halo2::benchmark::benchmark_ironwood_batch_verifier \
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
    circuit::halo2::benchmark::benchmark_ironwood_batch_verifier \
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
    --features circuit,test-dependencies --test ironwood_batch_timings -- --ignored --nocapture
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

## Historical sweeps

When a sweep crosses the backend-selection change, read `required-features` from
each revision's benchmark target in `Cargo.toml`. Current targets need
`test-dependencies`; payment/proof targets also need `circuit` and
`zip32-addresses`. With defaults disabled, select `backend-halo2` or
`backend-sensei` explicitly. Older revisions may not recognize those selectors.
Record the resolved features alongside each binary and result.

Private Halo2 test harness names moved from `circuit::benchmark::...` to
`circuit::halo2::benchmark::...`; confirm an exact test filter actually runs one
test instead of reporting a successful zero-test run.

The `first-after-build-and-prepare` group's cache-reset interpretation applies to
Halo2's per-key state. Sensei uses shared process state, so constructing another
key does not reset its caches. Cross-backend cold-start comparisons need fresh
processes and an appropriate timing harness.
