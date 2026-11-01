## Measuring runtime assembly selection

`scripts/bench_x86_dispatch.py` compares three builds of the same revision:

| Mode | Cargo features | Purpose |
| --- | --- | --- |
| automatic | defaults | Cached runtime CPU check followed by assembly |
| forced | defaults plus `x86_64-asm` | Assembly without runtime selection |
| portable | defaults plus `portable` | Portable arithmetic baseline |

The runner reuses the existing Criterion benchmarks in Pasta's `fp` and `fq`
targets and Udon's `field` target. It selects 24 workloads: addition,
multiplication, squaring, dependent multiplication and squaring chains, inversion,
independent multiplication batches, and finishing a product accumulator.
The last workload exercises the reduction discussed in PR #657.

Use a reserved Linux x86-64 machine with BMI2 and ADX available on every CPU.
Do not use emulation or a shared worker for performance conclusions. Check for
competing work before and during the run; discard results if the host becomes
busy. The script verifies CPU flags, but `--isolated` is the operator's statement
that the machine is reserved, not an automatic isolation mechanism.

From a clean checkout, with an output directory that does not already exist:

```bash
python3 scripts/bench_x86_dispatch.py --isolated --output /tmp/x86-dispatch-results
```

All builds use the native host triple, a baseline `x86-64` CPU target,
optimization level 3, one codegen unit, no LTO, and no debug assertions. The runner
builds every mode before measuring. It runs three rounds in automatic/forced/
portable, forced/portable/automatic, then portable/automatic/forced order. Each
workload gets one second of warm-up and a two-second measurement with 30 samples
per round. This measures warmed dispatch, excluding first-use CPU detection.
The experiment stops after one hour, including compilation.

Results stay outside the repository. `metadata.json` records source revision,
dirty state, host, CPU information, compiler, settings, and run order.
`samples.json` contains each round's Criterion median in nanoseconds.
`summary.csv` reports the median and min/max of those three medians, and the
percentage difference between automatic selection and each alternative.
Times are per workload invocation; a 128-element batch is not reported as a
single multiplication. Positive percentages mean automatic selection is slower.
Raw Criterion data and
command logs remain alongside those files. Missing workloads fail the run.

Automatic versus forced estimates the cost of dispatch, including any resulting
code-layout and optimizer differences. Automatic versus portable measures the
net benefit of enabling assembly by default. Individual operations, dependent
chains, and larger batches distinguish latency from throughput. An observed
difference smaller than the run-to-run spread is inconclusive. These workloads
do not measure full proof-generation performance or establish machine-code
equivalence.

For a portable workload smoke test on a developer machine, without timing claims:

```bash
python3 scripts/bench_x86_dispatch.py --smoke --output /tmp/x86-dispatch-smoke
```
