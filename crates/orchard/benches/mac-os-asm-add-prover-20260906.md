# Full Ironwood prover: Apple AArch64 assembly addition

These measurements predate the PR's transplant to main at `5033f91c`.
Paths and commands below describe the archived benchmark snapshots, before
the repository moved its packages under `crates/`. For the independent
current-main comparison using real payments, see
[the latest-main report](mac-os-asm-add-main-prover-20260906.md).

This compares the new inline assembly field addition against portable field
addition inside complete Ironwood proofs. Both variants retain the existing
assembly multiplication/squaring backend and the pre-existing working-tree
prover optimizations. This is an incremental comparison, not a comparison
against a clean commit or an entirely portable field backend.

## Results

The assembly-addition candidate reduced full proof-creation time by about 3%
on this four-worker M4 configuration. Both builds, both qualification runs,
and all four comparison runs completed successfully. Every fixture's
proof-verification preflight passed.

The summary averages the two run means for each variant. The final column
is `100 * (candidate / control - 1)`.

| Actions | Control | Assembly addition | Proof-time change |
| ---: | ---: | ---: | ---: |
| 1 | 86.265 ms | 83.645 ms | -3.04% |
| 2 | 136.895 ms | 132.955 ms | -2.88% |
| 4 | 229.567 ms | 222.766 ms | -2.96% |

Individual run means and Criterion 95% confidence intervals, in milliseconds:

| Run | 1 Action | 2 Actions | 4 Actions |
| --- | --- | --- | --- |
| Control 1 | 86.217 [86.170, 86.267] | 136.711 [136.617, 136.801] | 229.364 [229.245, 229.474] |
| Candidate 1 | 83.480 [83.406, 83.551] | 132.862 [132.786, 132.939] | 222.753 [222.649, 222.864] |
| Candidate 2 | 83.810 [83.495, 84.393] | 133.047 [132.916, 133.258] | 222.779 [222.635, 222.919] |
| Control 2 | 86.314 [86.236, 86.396] | 137.079 [137.027, 137.126] | 229.771 [229.687, 229.888] |

The closing control differs from the opening control by 0.11%, 0.27%, and
0.18% for one, two, and four Actions, respectively. Both candidate runs are
faster than both controls for every Action count. The raw sample means were
independently checked against Criterion's estimates.

There are ten samples per case per run. One-Action cases execute 180 timed
proofs per run; two-Action controls execute 110 and candidates 120; four-Action
cases execute 70. These measurements establish a gain for the specified
fixture, feature set, worker count, and machine, not all prover workloads.

## Workload and method

The existing `orchard_k11_prover` harness creates Ironwood v3 output-only
coinbase bundles using the post-NU6.3 circuit, at k = 11. The measured region
is the full `create_proof` call, including witness synthesis and the Halo 2
proving work. It measures one-, two-, and four-Action bundles, with four
Rayon workers and prepared MSM tables (`orbits`).

Key generation, table preparation, fixture construction, and RNG setup occur
outside timing. Each invocation also creates and genuinely verifies a proof
for each fixture before measuring it. Fixtures use identical deterministic
seeds in both variants. This is not a spend-enabled transaction fixture,
wallet transaction construction, or a cold-start/key-generation measurement.

Both binaries were built before measurement in separate target directories,
copied to stable paths, and hashed. Source comparison confirmed that only
`pasta_curves/src/fields/{aarch64_asm,fp,fq}.rs` differ. The benchmark and
every other source file are identical between variants.

Two two-Action control qualification runs measured 136.81 ms and 136.90 ms,
less than 0.1% apart. The final sequence is control/candidate/candidate/control,
each measuring all three Action counts. Each case uses a two-second warmup,
ten flat samples, and a 15-second target measurement interval. Criterion
chooses an integral proof count per sample, so actual intervals can be longer.
No build or other benchmark workload overlapped the timed runs.

## Host

The `benchmark-servers` skill was used on one macOS server:

- Alias: `mac-os-3`; hostname: `val-aus-zecnode03.local`.
- Apple M4, native `arm64`, four performance and six efficiency cores.
- `rustc 1.97.1 (8bab26f4f 2026-07-14)`.
- `cargo 1.97.1 (c980f4866 2026-06-30)`.
- AC power; initial load averages `1.86 1.70 1.67`.
- Initial process checks found no competing build or benchmark. WindowServer
  used about 9% of one CPU. Post-qualification load was `7.19 5.84 3.54`,
  following compilation and the four-worker prover runs, with no competing
  compute process visible.
- `pmset -g therm` reported no recorded thermal or performance warning before
  measurement and after qualification. Per-leg telemetry is retained.
- After the final bracket: load averages `4.66 4.94 3.73`, AC power, no
  recorded thermal/performance warning, and no remaining build or benchmark
  process. WindowServer used about 6% of one CPU.

## Reproduction and artifacts

Source base: `659611eadd6102c918f35e2a49b7078c08bb85c7`, including the
pre-existing tracked working-tree changes and the generated Orchard k11
parameter file. The control removes only the assembly-addition change.
No production source or API was changed during this benchmarking task.

Build each source snapshot into its own target directory:

```sh
CARGO_TARGET_DIR=/absolute/variant-target cargo bench --locked \
  -p zakura-orchard --features circuit,orbits \
  --bench orchard_k11_prover --no-run
```

For each saved executable, run:

```sh
RAYON_NUM_THREADS=4 ORCHARD_K11_PROVER_THREADS=4 \
ORCHARD_K11_PROVER_IRONWOOD=1 \
CRITERION_HOME=/absolute/criterion \
./bin/control --bench --save-baseline control-1
```

Repeat as `bin/candidate` with `candidate-1` and `candidate-2`, then
`bin/control` with `control-2`. Qualification uses the additional filter
`prove-2-actions` and names `qualify-1` and `qualify-2`.

Remote artifact directory:
`/tmp/asm-full-prover-mac-os-3-20260906.WNQUW3/`.
It contains source archives, build logs, executable hashes, stable binaries,
the build/measurement scripts, raw logs, per-leg telemetry, and Criterion
samples under `criterion/ironwood-k11/`.

Local analysis and downloaded results:
`/private/tmp/asm-full-prover-mac-os-3-20260906.XrsH8j/`.

SHA-256 hashes:

| Artifact | SHA-256 |
| --- | --- |
| Candidate source archive | `7460b522d3e9bd5a16f0681bdd31bdaa03ddb7dc3e60ccd17c0572a5c05bd7ae` |
| Control source archive | `bb1de8c6a7ad04fdeb30f5f29a82c078c5a6d401164696d4b9ff777fbf4fa4b8` |
| Control executable | `11235784c6fbd8c08b8ebaa3ba8954d117757f64e8e02c7144f3def7779a06b8` |
| Candidate executable | `44853c5e9e7da99a206225ae6951d76e50a639bc1e104af2b869633dc084b6b4` |
| Shared k11 parameter file | `1eab6f93a080ce41b908d935c04bd2e3ed1ac23f277c15d11c499d56d28fa0f7` |
