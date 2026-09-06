# Apple AArch64 field addition experiment, 2026-09-06

These measurements predate the PR's transplant to main at `5033f91c`.
Paths below refer to the archived snapshots before the move to `crates/`;
these timing results have not been remeasured on the PR base.

The transplanted PR was validated locally on Apple AArch64 with Rust 1.97.1:
258 all-features release tests and one doc test passed (three existing tests
ignored); both debug differential tests passed; 77 no-default-features
release tests passed; all point benchmark smoke cases passed. The portable
configuration emitted existing unused-import/dead-code warnings. Changed
Rust files passed rustfmt, and the diff passed whitespace checks.

The retained candidate routes `Fp` and `Fq` addition operators through one
register-only assembly block under the existing `aarch64-asm` feature on
Apple AArch64. This also covers the `a + a` doublings in the Pallas/Vesta
projective formulas. Inherent `const` methods retain their portable bodies.

The only added internal interface is
`aarch64_asm::add(&Limbs, &Limbs, &Limbs) -> Limbs`, with `pub(super)`
visibility inside the private field backend. No public or `pub(crate)` API,
trait signature, feature, or constant was added or changed by this experiment.

## Why the generated code is shorter

A standalone optimized `Fp` wrapper was compiled with the server's
`rustc 1.97.1 (8bab26f4f 2026-07-14)`. Local rustc 1.98.0 produced the same
instruction counts. Counts include actual instructions, not directives.

| Component | Portable addition | Assembly addition |
| --- | ---: | ---: |
| Initial four-limb addition | 4 | 4 |
| Conditional reduction | 22 | 8 |
| Constant materialization | 15 | 8 |
| Loads, stores, return | 7 | 7 |
| Total | 48 | 27 |

LLVM already recognizes the initial `adds; adcs; adcs; adc` chain. The
portable reduction, however, materializes borrow values with `adc`, `asr`,
and `cinc`, then masks and adds the modulus back. Assembly uses
`subs; sbcs; sbcs; sbcs` followed by four `csel` instructions. It also needs
only the positive modulus constants. Constants can be shared in an inlined
caller, so the standalone instruction count is not a point-operation speedup
prediction. Register allocation and surrounding arithmetic still matter.

Both inputs are canonical, so their sum is below `2p < 2^256`. One
conditional subtraction suffices. The backend uses the existing Pasta
modulus shape (`modulus[2] == 0`), supplied shared modulus constants, and no
data-dependent branches or memory accesses inside the assembly block.

## Host and reproduction

- Skill: `benchmark-servers`; only `mac-os-3` was used.
- Hostname: `val-aus-zecnode03.local`; architecture: `arm64`.
- CPU: Apple M4, 10 cores.
- Rust: `rustc 1.97.1 (8bab26f4f 2026-07-14)`.
- Cargo: `cargo 1.97.1 (c980f4866 2026-06-30)`.
- Base commit: `659611eadd6102c918f35e2a49b7078c08bb85c7` plus the user's
  pre-existing tracked working-tree changes, captured before this experiment.
- Remote artifacts: `/tmp/pasta-asm-mac-os-3-20260906.P4FzR8`.
- `baseline.tar.gz` preserves that starting source snapshot. `control/`
  contains that source with the new benchmark cases; `baseline/` contains
  the candidate. Despite its name, `baseline/` is the candidate source.
- Final measurements use separate `control-target/` and `candidate-target/`
  build directories and a shared absolute `CRITERION_HOME` at
  `isolated-criterion/`.

Run from each respective source directory, setting `CARGO_TARGET_DIR` to
its own absolute build directory and `CRITERION_HOME` as above:

```sh
cargo bench -p zakura-pasta-curves --features aarch64-asm --bench point -- \
  'point (doubling|addition|subtraction)' \
  --warm-up-time 2 --measurement-time 5 --sample-size 80 \
  --save-baseline isolated-control
```

For the candidate, replace the final option with
`--baseline isolated-control`. Both use the same benchmark source, including
dependent serial additions/doublings with black-boxed changing coordinates.

Before measurement, the load averages were `3.20 3.26 2.72`. Process checks
showed no competing benchmark/compiler workload; WindowServer used about
9–13% of one CPU. During measurement the benchmark used one CPU. An
intermediate load check read `2.51 3.67 3.38`. `pmset -g therm` reported no
recorded thermal or performance warning at both checks.

After the final repeat, load averages were `2.19 2.50 2.76`, with no recorded
thermal/performance warning and no remaining benchmark/compiler process.

## Experimental exclusions

The initial short control run was noisy and is not used for conclusions.
An additional repeat (`final-control.log`/`final-candidate.log`) accidentally
reused a stale executable through a shared Cargo target directory; it was
stopped and discarded. The final `isolated-*` measurements use distinct
build directories to prevent that problem.

A separate assembly subtraction candidate passed the correctness suite and
improved serial point addition further, but lost much of the Pallas doubling
gain compared with addition alone. That production change was removed.
`add-sub-candidate.log` preserves the exploratory timings. No fused
sum-of-products or lazy point-coordinate representation was introduced.

The instruction-count probe is in remote `probe/`; its generated assembly
is under `probe/target/release/deps/`. Local copies are in
`/private/tmp/pasta-asm-probe-20260906/`.

## Isolated results

All final benchmark commands completed successfully. Times below are
Criterion central time estimates in nanoseconds; changes are Criterion's
reported relative estimates (which need not equal the ratio of the central
time estimates). All ten comparisons reported significant improvement.

| Operation | Control (ns) | Addition ASM (ns) | Time change |
| --- | ---: | ---: | ---: |
| Pallas doubling | 75.648 | 68.567 | -9.16% |
| Pallas addition | 153.12 | 149.60 | -2.48% |
| Pallas subtraction | 154.35 | 150.79 | -2.04% |
| Pallas doubling, serial | 85.876 | 78.626 | -7.97% |
| Pallas addition, serial | 160.96 | 156.84 | -2.13% |
| Vesta doubling | 75.621 | 67.667 | -10.95% |
| Vesta addition | 152.96 | 148.04 | -3.16% |
| Vesta subtraction | 154.29 | 149.39 | -3.62% |
| Vesta doubling, serial | 85.831 | 78.001 | -9.19% |
| Vesta addition, serial | 160.92 | 156.10 | -3.03% |

These are point microbenchmarks on one M4 server, not prover or MSM timings.
Raw confidence intervals and outlier counts are in `isolated-control.log`
and `isolated-candidate.log` in the remote artifact directory.

A reverse-order repeat ran the candidate and then the control with filter
`serial`, otherwise identical timing flags, and the same separate build
directories. Neither executable was rebuilt. Central estimates were:

| Serial operation | Repeated control (ns) | Repeated candidate (ns) |
| --- | ---: | ---: |
| Pallas doubling | 85.889 | 77.562 |
| Pallas addition | 160.68 | 155.15 |
| Vesta doubling | 85.935 | 77.566 |
| Vesta addition | 160.69 | 155.77 |

This confirms approximately 9.7% less time for serial doubling and 3.1–3.4%
less time for serial addition using ratios of the repeated central estimates.
Raw logs are `repeat-candidate.log` and `repeat-control.log`.

## Correctness and hygiene

- Apple AArch64 debug suite: 103 tests passed and one doc test passed.
- Final all-features release suite on `mac-os-3`:
  `cargo test -p zakura-pasta-curves --release --all-features`;
  239 tests passed, three existing tests ignored, one doc test passed.
- Portable fallback on the local Mac:
  `cargo test -p zakura-pasta-curves --lib --no-default-features`;
  74 tests passed (existing unused-import/dead-code warnings).
- The addition differential checks cover both fields, random canonical
  residues, boundary values, carries at each bit position, sums just below
  and exactly at the modulus, and equal-input doubling. The oracle uses
  the inherent portable methods and compares the internal representations.
- Final targeted differential tests, rustfmt checks, and `git diff --check`
  passed. The shared modulus constants are used directly; no protocol
  literals or terminology were introduced.
