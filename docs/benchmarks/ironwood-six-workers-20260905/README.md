# Six-worker Ironwood transaction experiments

Status: completed on both selected servers, 2026-09-05 UTC.
[Draft PR #375](https://github.com/zakura-core/common/pull/375).
**No meaningful, consistently beneficial six-worker speedup demonstrated.**
Do not merge the witness-caching candidate as a performance improvement on
the strength of these results.

## Workload and decision

The primary workload is one regular-backend Ironwood V3 transaction proof
with 2, 3, 4, or 5 real payment Actions and six Rayon workers. These are not
concurrent transaction proofs. The two-Action case has two real spends;
the padded-payment case is excluded from the reported comparisons.
Every fixture has real nonzero spends and outputs. Each binary verifies two
differently seeded preflight proofs for every fixture before measurement.

The final candidate retains circuit configuration in the Orchard proving key,
compiles constant-placement ranges during floor planning, and shares region
starts through an Arc. It removes the parallel-inversion and lazy-FFT
experiments. Those unsuccessful prototypes remain reproducible in PR history.

M4 changes are below 0.4% and mixed. Linux has visible run-to-run drift and
regressions, including roughly 2% for two and five Actions. The first proof
after key preparation does not establish a benefit either. The added public
API and maintenance cost are not justified by a useful transaction speedup
yet; this PR remains an experiment, not a merge recommendation.

No physical phone was measured. M4 results are ARM desktop evidence, not
iPhone/Android results. Peak memory, power, startup, key-generation latency,
and end-to-end wallet transaction construction were not measured.

## Primary result: six workers

Mean milliseconds per proof. Control and candidate each average their two
invocation means from control/candidate/candidate/control (ABBA).
Time change is candidate / control - 1; negative is faster.
No samples or outliers were removed.

| Host | Actions | Control ms | Witness cache ms | Time change |
| --- | ---: | ---: | ---: | ---: |
| mac-os-1 | 2 | 90.72 | 90.45 | -0.30% |
| mac-os-1 | 3 | 124.02 | 123.70 | -0.26% |
| mac-os-1 | 4 | 155.81 | 156.03 | +0.14% |
| mac-os-1 | 5 | 196.09 | 195.96 | -0.07% |
| linux-2 | 2 | 188.65 | 192.52 | +2.05% |
| linux-2 | 3 | 269.74 | 269.89 | +0.05% |
| linux-2 | 4 | 336.06 | 336.59 | +0.16% |
| linux-2 | 5 | 431.41 | 441.43 | +2.32% |

Per-invocation means preserve the drift and outlier effects that aggregation
can conceal:

| Host | Actions | Control 1 | Candidate 2 | Candidate 3 | Control 4 |
| --- | ---: | ---: | ---: | ---: | ---: |
| mac-os-1 | 2 | 90.62 | 90.49 | 90.41 | 90.83 |
| mac-os-1 | 3 | 123.98 | 123.67 | 123.73 | 124.07 |
| mac-os-1 | 4 | 155.85 | 156.41 | 155.65 | 155.77 |
| mac-os-1 | 5 | 196.06 | 196.05 | 195.86 | 196.12 |
| linux-2 | 2 | 188.84 | 191.40 | 193.64 | 188.46 |
| linux-2 | 3 | 270.62 | 269.32 | 270.45 | 268.86 |
| linux-2 | 4 | 336.90 | 337.43 | 335.74 | 335.21 |
| linux-2 | 5 | 424.00 | 441.76 | 441.11 | 438.81 |

These are descriptive comparisons, not independent repeated experiments for
each individual proof. Each invocation has ten flat Criterion samples.
The raw file retains per-invocation confidence intervals and individual
sample iteration counts/times. We do not construct a pooled confidence
interval or claim significance from the average of two invocation means.

## First proof after building and preparing a fresh key

Endpoint checks at two and five Actions; one control/candidate pair per host.
Every timed proof uses a newly built and successfully prepared key. Key
generation, preparation, and destruction are outside the reported duration.
Process, code, OS caches, allocator, and Rayon pool remain warm. This is
semantic per-key cold latency, not process-startup latency.

| Host | Actions | Control ms | Witness cache ms | Time change |
| --- | ---: | ---: | ---: | ---: |
| mac-os-1 | 2 | 90.63 | 90.57 | -0.07% |
| mac-os-1 | 5 | 196.23 | 196.34 | +0.06% |
| linux-2 | 2 | 186.86 | 186.39 | -0.25% |
| linux-2 | 5 | 416.95 | 420.67 | +0.89% |

These single-pair checks are screening evidence, not a confirmed cold-path
speedup. The harness now supports all one- through five-Action cases; only
the two/five endpoints were measured in this final first-proof check.

## Six-worker ablation screen

One invocation per candidate, bracketed by controls. Variants are cumulative
until the isolated `final` candidate. Do not interpret a single faster
Linux invocation as a confirmed optimization: its controls also drift.

### mac-os-1: mean milliseconds

| Variant / leg | 2 Actions | 3 Actions | 4 Actions | 5 Actions |
| --- | ---: | ---: | ---: | ---: |
| control (screen1) | 90.63 | 124.15 | 155.97 | 196.06 |
| inversion (screen2) | 90.58 | 123.89 | 155.82 | 196.07 |
| lazy (screen3) | 91.47 | 124.74 | 156.87 | 197.23 |
| planned (screen4) | 91.02 | 124.69 | 157.27 | 197.13 |
| configured (screen5) | 90.88 | 124.39 | 156.64 | 197.10 |
| streamed (screen6) | 90.51 | 123.92 | 155.99 | 196.26 |
| control (screen7) | 91.19 | 123.97 | 155.79 | 196.10 |

### linux-2: mean milliseconds

| Variant / leg | 2 Actions | 3 Actions | 4 Actions | 5 Actions |
| --- | ---: | ---: | ---: | ---: |
| control (screen1) | 187.12 | 266.05 | 328.98 | 426.76 |
| inversion (screen2) | 188.92 | 273.91 | 336.14 | 431.78 |
| lazy (screen3) | 191.52 | 274.43 | 329.48 | 429.56 |
| planned (screen4) | 188.00 | 270.60 | 332.52 | 428.21 |
| configured (screen5) | 186.26 | 262.06 | 326.07 | 418.87 |
| streamed (screen6) | 188.95 | 265.44 | 339.60 | 442.23 |
| control (screen7) | 191.69 | 269.67 | 338.58 | 440.56 |

Parallel rational inversion produced no clear gain. The initial lazy
reduction implementation regressed on M4. Streaming its products separately
recovered much of that loss but did not establish a useful win over control.
Neither arithmetic experiment is present in the final tree.

Earlier four-worker inversion and lazy-FFT runs are retained in the raw data
for completeness; they are not the primary result. In particular, the Linux
four-worker starting telemetry records another `sorted_u10_pair` process at
100% CPU. Treat that earlier Linux series as potentially contaminated.
The six-worker before/after snapshots no longer show that process or another
heavy competing workload. We did not expand to additional hosts.

## Phase diagnostic: why witness work had little headroom

A separate instrumented control binary on mac-os-1, six workers, reported
the following individual first-after-prepare samples:

| Actions | Synthesis interval ms | Advice evaluation ms |
| --- | ---: | ---: |
| 2 | 1.399 | 0.221 |
| 3 | 1.668 | 0.243 |
| 4 | 2.010 | 0.248 |
| 5 | 2.240 | 0.422 |

These are diagnostic samples, not phase medians. The synthesis interval
includes witness allocation and overlapped instance-polynomial preparation;
it excludes earlier circuit configuration. Advice evaluation includes the
batch inversion and sparse writeback. There are 7,007 recorded denominators
per real Action. The patch and complete six-worker diagnostic output are
retained in [profile.patch](profile.patch) and the raw data.

Inference: these measured intervals are already small relative to the
90–196 ms M4 proof. Further work on these particular witness phases has
little end-to-end headroom. A subsequent optimization should profile the
remaining commitment/MSM and polynomial work at six workers before choosing
another algorithm; this diagnostic alone does not apportion that remainder.

## Revisions

Upstream base: `9f1785da1f4fc3d68b25fae926b36dd81adfa44e`.
All benchmark source archives were made from committed trees. Builds used
separate target directories, then copied executables to stable paths.
No source builds ran concurrently with measurements on the same host.

| Label | Commit | Meaning |
| --- | --- | --- |
| control | `d6f63f3a427c00670c20a24f64023bbc2ee392bb` | Base plus 3/5-Action benchmark coverage |
| inversion | `00c2985429a34868bd9abdb2fb33d89a281623d5` | Parallel chunks for rational inversion |
| lazy | `aeb895333528ee50924760d5ae1c17aac57a6ba0` | Inversion plus bounded lazy serial Pasta FFT |
| planned | `7d932227bc844ce10cb7b51aab12297fb7e19d01` | Lazy plus compiled constant ranges/shared regions |
| configured | `8df0b96b7f5ecfeb3f10972073040a38a91f6b08` | Planned plus retained circuit configuration |
| streamed | `e05e5fa5dafd811175662fd78976616097b0878d` | Configured plus split product/combination loops |
| final | `cfa82a6e5122aff57cefc29cd1eb448cf3cb5bd3` | Only layout/configuration caching, no FFT/inversion changes |

Subsequent PR changes add documentation, benchmark artifacts, and a
Send + Sync assertion; they do not change the measured production code.

## Hosts and environment

Only one Mac and one Linux server were used for this series.

- `mac-os-1`: `valars-Mac-mini.localdomain`, Darwin arm64, Apple M4,
  10 cores. Six-worker starting load averages: 3.69 / 3.04 / 3.02;
  final load: 5.71 / 5.48 / 4.76. Process snapshots showed no heavy competing
  workload during the six-worker series. `pmset -g therm` recorded no thermal
  or performance warning and no CPU power status. This is not a temperature
  measurement or a guarantee against throttling.
- `linux-2`: `val-aus-zecnode02`, Linux x86_64, VMware VM with 8 vCPUs,
  AMD engineering sample `100-000000894-04`. Six-worker starting load:
  3.56 / 2.41 / 2.30; final load: 5.20 / 5.15 / 4.35. The six-worker snapshots
  showed no heavy competing guest process. Hypervisor contention is not
  excluded. Linux timings are visibly noisier than M4.
- Both: `rustc 1.97.1 (8bab26f4f 2026-07-14)`,
  `cargo 1.97.1 (c980f4866 2026-06-30)`; locked dependencies,
  default release bench profile, `--features circuit`, no `orbits`,
  and `RUSTFLAGS` / `CARGO_ENCODED_RUSTFLAGS` unset for builds.

[results.json](results.json) contains all 160 saved case/invocation results
across the exploratory and final series, complete Criterion estimates,
raw sample times/iteration counts, host telemetry, executable SHA-256 hashes,
and the diagnostic log. Values in that file are nanoseconds, not milliseconds.
Both hosts completed every scheduled six-worker case successfully.

## Reproduction

Create a fresh, host-labeled directory on each selected host. Archive each
listed source revision as `<variant>.tar.gz` using `git archive`, and copy the
archives and the accompanying scripts there. Use canonical SSH aliases and
check host identity/load before running anything.

The exact build command in [build.sh](build.sh) is:

```sh
env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS \
    CARGO_TARGET_DIR="$transaction_root/target/$transaction_variant" \
    cargo +1.97.1 bench --locked -j 4 -p zakura-orchard --features circuit \
    --bench ironwood_k11_prover --no-run --message-format=json
```

Build all selected binaries before timing. [run-six.sh](run-six.sh) reproduces
the ablation screen. [run-final.sh](run-final.sh) reproduces ABBA and the
first-proof endpoint checks. Both require the host directory and host alias
as arguments. For example, after populating a new host directory:

```sh
bash build.sh /tmp/ironwood-six-reproduction-mac-os-1 control
bash build.sh /tmp/ironwood-six-reproduction-mac-os-1 final
bash run-final.sh /tmp/ironwood-six-reproduction-mac-os-1 mac-os-1
```

The primary timed command, executed from that host directory, is:

```sh
env RAYON_NUM_THREADS=6 IRONWOOD_K11_PROVER_THREADS=6 \
    "$transaction_root/bin/$transaction_variant" --bench \
    '^ironwood-k11/prove-(2-actions-two-real-spends|[345]-actions)$' \
    --save-baseline "$transaction_label"
```

Each case uses ten flat samples, a two-second warmup, and a 15-second
measurement target. Preflight proofs and key preparation precede the timed
region. Distinct deterministic proof seeds prevent identical transcript
challenges across successive proofs.

The first-proof filter is:

```text
^ironwood-k11-first-after-build-and-prepare/prove-(2-actions-two-real-spends|5-actions)$
```

The diagnostic uses control plus `profile.patch`, the same build flags,
six-worker environment, and the executable's `--test` mode.

Historical [run-inversion.sh](run-inversion.sh) and
[run-lazy.sh](run-lazy.sh) preserve the exploratory four-worker ordering.
After collecting each host's `results/`, `target/criterion/`, and diagnostic
log into directories named `mac-os-1` and `linux-2`,
`python3 collect.py <collection-directory>` emits the raw JSON to stdout.

## Correctness and API review

- Isolated candidate: 209 Halo 2 library tests and 169 Orchard library tests
  passed, with three existing Orchard tests ignored.
- Added Orchard proving-key Send + Sync assertion passed separately.
- Halo 2 without default features: 174 library tests passed; existing unused
  import/dead-code warnings remain.
- Cached and uncached configurations produce identical seeded proof bytes
  for one/four circuits at 1, 2, 6, and 10 workers.
- The discarded lazy FFT passed boundary/random equivalence checks for both
  Pasta fields, including completed-prefix cases.
- Rust 1.91.1 check, formatting, whitespace, and changelog checks passed.

Net API change: one new public
`halo2_proofs::plonk::create_proof_with_config` function, consuming a typed
configuration that callers must explicitly clone if retaining it. Existing
`create_proof` signatures and bounds are preserved. No `pub(crate)` API
changes remain. Orchard's configuration field and floor-plan changes are
private. Temporary lazy-FFT public bridges were removed with that experiment.
