# Apple AArch64 addition: full prover against current main

This comparison measures the PR on a clean current-main base, independently
of the older output-only working-tree measurements in
[the initial report](mac-os-asm-add-prover-20260906.md).

## Results

The clean `mac-os-4` comparison reduced full steady-state proof time by
2.8–3.0% for all four cases. Both candidate runs were faster than both
controls in every case. All runs completed and every distinct-proof
verification preflight passed.

The summary averages the two run means for each variant. Time change is
`100 * (candidate / control - 1)`; no samples or outliers are removed.

| Case | Main | Candidate | Proof-time change |
| --- | ---: | ---: | ---: |
| 1 Action | 67.476 ms | 65.585 ms | -2.80% |
| 2 Actions, padded payment | 105.570 ms | 102.480 ms | -2.93% |
| 2 Actions, two real spends | 105.457 ms | 102.503 ms | -2.80% |
| 4 Actions | 183.413 ms | 177.962 ms | -2.97% |

Individual run means and Criterion 95% intervals, in milliseconds:

| Case | Control 1 | Candidate 1 | Candidate 2 | Control 2 |
| --- | --- | --- | --- | --- |
| 1 Action | 67.518 [67.448, 67.596] | 65.660 [65.587, 65.737] | 65.511 [65.453, 65.565] | 67.435 [67.367, 67.506] |
| 2, padded | 105.742 [105.487, 106.185] | 102.539 [102.466, 102.616] | 102.421 [102.341, 102.499] | 105.399 [105.319, 105.485] |
| 2, real spends | 105.534 [105.459, 105.605] | 102.543 [102.455, 102.627] | 102.464 [102.416, 102.515] | 105.381 [105.301, 105.453] |
| 4 Actions | 183.587 [183.478, 183.725] | 178.171 [177.772, 178.848] | 177.753 [177.667, 177.840] | 183.239 [183.108, 183.363] |

The closing controls differed from the opening controls by at most 0.33%.
Raw sample means were independently checked against Criterion estimates.
Each run measured 230 one-Action proofs, 150 proofs for each two-Action case,
and 90 four-Action proofs, divided into ten flat samples per case.

This result applies to the specified steady-state workload, feature set,
four-worker configuration, and M4 host. It does not measure first-proof
latency, key generation, other thread counts, or phone performance.

## Revisions and workload

- Control: main at `5033f91cef505514b39c64ebcc28aae7a2806868`.
- Candidate: `7a31e76b768e44387a758ed9216b8f818c862eeb`, adding only the
  Apple AArch64 field-addition optimization, tests, microbenchmarks, and docs.
- Both snapshots are clean Git archives. Both use Rust 1.97.1, their identical
  locked dependencies, and `--features circuit,orbits`.
- The unmodified `ironwood_k11_prover` harness measures current Ironwood V3
  payments under the post-NU6.3 circuit: one Action, a padded two-Action
  payment, two Actions with two real spends, and four Actions.
- Four workers: `RAYON_NUM_THREADS=4` and `IRONWOOD_K11_PROVER_THREADS=4`.
- Only the steady-state `ironwood-k11/` group is measured. The separate
  first-proof-after-key-preparation group is excluded.

The timed work is complete `create_proof`, including circuit synthesis and
the Halo 2 prover. Fixtures, keys, prepared MSM tables, and RNG initialization
are outside the timed region. Proof seeds vary across iterations. Every
invocation first creates and verifies two distinct proofs per fixture using
the same prepared key, checking both correctness and retained state across
different transcript challenges. No benchmark source was modified.

## Method and host

The `benchmark-servers` skill was used to build on `mac-os-3` and run the
final comparison on `mac-os-4`, hostname `val-aus-zecnode04.local`, native
`arm64`, Apple M4 with ten cores. Build toolchain on `mac-os-3`:

- `rustc 1.97.1 (8bab26f4f 2026-07-14)`.
- `cargo 1.97.1 (c980f4866 2026-06-30)`.

Both binaries were built before timing in separate target directories,
copied to stable paths, and hashed. The exact same binaries were transferred
to `mac-os-4` with matching hashes. That host has no Rust toolchain; no
installation was needed. Both executables depend only on the macOS system
libraries `libSystem` and `libiconv`.

Initial `mac-os-4` telemetry showed AC power, load averages
`4.31 3.18 2.60`, no recorded thermal/performance warning, and no competing
compiler or benchmark. WindowServer used approximately 12% of one CPU.

The first two-real-spend qualification run had two slow outliers and a
110.02 ms mean. Two subsequent controls were tight at 105.86 ms and
105.52 ms (0.32% apart), so the final bracket began after those checks.
All qualification logs, including the noisy first run, are retained.

The clean bracket ended with load averages `4.75 4.04 3.21`, AC power,
no recorded thermal/performance warning, and no competing compiler or
benchmark visible. WindowServer used approximately 11% of one CPU.

The comparison order is control/candidate/candidate/control. Each case uses
ten flat samples, a two-second warmup, and a 15-second target measurement
interval, with Criterion choosing an integral number of proofs per sample.
Per-leg process/load/power/thermal telemetry and all raw samples are retained.

### Excluded host attempts

The first attempt ran on `mac-os-3`. Its two qualification runs were stable
(105.51 ms and 105.39 ms). An unrelated Rust build began during the closing
control and inflated its four-Action mean to 357.28 ms. After that build
finished, another benchmark overlapped the repeated closing control. Neither
closing control is used, and no `mac-os-3` timings are pooled into the final
comparison. The first three legs and their telemetry remain archived.

`mac-os-1` was checked as a replacement but its SSH connection timed out.
`mac-os-4` was then selected because it was reachable and had no visible
competing workload. It was independently qualified before comparison.

## Reproduction and artifacts

Build each source snapshot into its own absolute target directory:

```sh
CARGO_TARGET_DIR=/absolute/variant-target cargo +1.97.1 bench --locked \
  -p zakura-orchard --features circuit,orbits \
  --bench ironwood_k11_prover --no-run
```

Copy the resulting executables to `bin/control` and `bin/candidate`. Run:

```sh
RAYON_NUM_THREADS=4 IRONWOOD_K11_PROVER_THREADS=4 \
CRITERION_HOME=/absolute/criterion \
./bin/control --bench '^ironwood-k11/' --save-baseline control-1
```

Repeat with `bin/candidate` and labels `candidate-1`, `candidate-2`, then
`bin/control` with `control-2`. The two qualification runs use filter
`^ironwood-k11/prove-2-actions-two-real-spends$` and labels `qualify-1`,
`qualify-2`. The fixture implementation and deterministic seed schedule are
identical between the two source archives; no external fixture corpus is
used by this prover harness.

Build artifacts and the excluded attempt on `mac-os-3`:
`/tmp/asm-add-main-mac-os-3-20260906.jIdBG2/`.
Final measurement artifacts on `mac-os-4`:
`/tmp/asm-add-main-mac-os-4-20260906.xuCI5I/`.
Local downloads and analysis:
`/private/tmp/asm-add-main-mac-os-3-20260906.MH759G/`.
These include source archives, binaries, build/measurement scripts, logs,
telemetry, and raw Criterion samples under `criterion/ironwood-k11/`.

SHA-256 hashes:

| Artifact | SHA-256 |
| --- | --- |
| Control source archive | `2997357c4bb45bdfa64d26fe309f49fd13c457ff973deb10b277499c28b3aaed` |
| Candidate source archive | `834fee9934dc870c74b37a98bcbe410bdde5a3f7132bf14dae66f77f955c297a` |
| Control executable | `074c4045e8f749488142874bcb63229841bf59d4c3dbd69b7b1bc75d7e18415c` |
| Candidate executable | `705da44280a1225c7ce4e80bc64351a10a4fafecbb33ad2fceb47ac653246904` |

The subsequent report-only commit does not change the measured Rust code.
