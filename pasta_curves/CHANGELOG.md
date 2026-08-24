# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- The GLV multiscalar multiplication now plans between two bucket backends:
  the existing Signed-Booth windows over the two decomposition halves, and a
  new Eisenstein-orbit backend (`glv::orbit`) that recodes the joint value
  $k_1 + k_2\omega$ in radix $2^c$ directly over $\mathbf{Z}[\omega]$ and
  quotients every digit by the six units. Each window then holds one bucket
  per unit *orbit* — $(4^c + 2)/6$ buckets drawn from a canonical hexagonal
  wedge, against $2^{c-1}$ per half — and visits every scalar once instead of
  twice; the unit acts on the stored point through one of three precomputed
  $\zeta$-rotations of x and a y negation. Window sums are integrated by a
  spanning-tree reducer on the wedge whose edges differ by $1$ or
  $1 + \omega$, so the two-dimensional weighted sum telescopes to
  $A - \phi^2(H)$ in $2m - 2$ additions. Widths 4–6 are planned by a
  calibrated cost model (width 3 is implemented and tested but never
  modeled ahead). Measured on 32-core x86-64 (portable backend) against the
  Booth backend at its own planned width: +2..6% serially from 512 to
  16,384 terms, +19..38% on 8 workers and +13..65% on 32 workers at
  mid-to-large sizes — the orbit's 22–26 windows keep workers fed that
  Booth's 10–16 cannot — while Booth is kept for small parallel MSMs.
- The MSM planner now prices both GLV bucket backends from the input's
  *magnitude profile* (suffix counts of the decomposition halves' bit
  lengths) rather than the term count alone, and the orbit backend caps its
  window walk at the highest window any scalar's recoding reaches. Real
  proving MSMs are not uniformly full-width — halo2 witness commitments mix
  boolean columns, byte-scale values, and zero padding rows, and an early
  count-only planner sent such MSMs to the orbit backend (whose joint
  radix-$2^c$ recoding spreads a small magnitude over ~$2c/w$ as many
  windows as $w$-bit Booth halves), measurably regressing serial Orchard
  proving; profiled planning keeps Booth on the sparse commitment shapes
  and the orbit's wins on the full-width quotient/multiopen MSMs. With the
  window capping the orbit backend in fact wins witness-shaped MSMs
  outright too (+16..20% serial at 2,048–8,192 terms). End to end,
  interleaved A/B runs of Orchard proving measured the finished planner
  ~2.6% faster serially (k = 11, one action; faster in 3 of 3 matched
  rounds) and ~8% faster on the default 32-thread pool (one-action bundle
  449 ms → 415 ms).
- The MSM bucket reduction is now a multi-window primitive
  (`reduce_affine_buckets_multi`) that can share one Montgomery inversion
  per tree level across a whole group of windows. Cross-window sharing
  itself *measured as a net loss* and is disabled (the group size is one
  window): with divstep inversion at I/M ≈ 77 the saved inversions are
  worth microseconds per MSM, while staging many windows at once grows the
  working set from a few hundred KiB (in L2) to several MiB swept per
  reduction level — interleaved A/B runs of the serial Orchard k = 11
  prover measured 32 MiB groups ~5% slower end-to-end. The group size
  remains a documented knob for platforms with different memory
  hierarchies.
- The GLV multiscalar multiplication backend now plans its own window width.
  It evaluates the GLV ladder at the generic default width and one bit wider,
  runs at the cheaper, and is selected only when that beats the generic
  estimate. The 127-bit GLV components have half as many windows as the
  generic ladder, so the parallel wave count is more sensitive to the width;
  comparing both backends at the generic width alone left the slower backend
  selected in 13 of 46 measured (terms, workers) cells on Apple M4 and EPYC.
- Fixed the crate manifest: the `multicore` feature was declared twice after
  two independent changes each introduced it, which made the workspace fail
  to load. The single declaration implies `glv` and enables Rayon.
- Added the `multicore` feature and [`CurveExt::fft_vartime`] specialization
  hook. The Pasta implementation keeps public curve FFTs affine, decomposes
  their twiddles once with GLV, and batches each ladder column's inversions.
- The Pasta curve FFT now replaces its bottom radix-2 layers with fused 8- and
  16-point codelets. The 16-point transform uses 14 scalar multiplications
  instead of 17 and shares repeated scalar schedules and affine inversion
  stages across its subtransforms.
- The GLV batch-affine ladder now interleaves its nonzero Montgomery batch
  inversion across even- and odd-indexed accumulator lanes. The three fixed
  extra multiplications per ladder column expose independent multiplication
  chains to out-of-order execution.
- Prepared the `1.0.0-rc.3` release.
- `Curve::batch_normalize` now runs its Montgomery batch inversion as two
  interleaved even/odd accumulator lanes for batches of 32 or more points
  (three extra multiplications per batch, one shared inversion), preserving the
  identity-skipping semantics; smaller batches keep the single chain. Measured
  about 21% less per element on Apple aarch64 with the assembly backend and 6%
  on x86-64 portable at large sizes; neutral on the Orchard Merkle workloads,
  where normalization is a small share of each combine.
- Prepared the `1.0.0-rc.2` release.
- Updated the curve traits to `ff 0.14`, `group 0.14`, and `rand_core 0.10`.
- `Fp`/`Fq` field inversion is now a variable-time 62-divstep safegcd (a
  Montgomery-native port of libsecp256k1's `modinv64`, exploiting both Pasta moduli's
  sparse `[m0, m1, 2, 0, 64]` radix-2^62 shape), replacing the Fermat exponentiation:
  measured 7.2x faster (4.83 µs → 0.67 µs, I/M ≈ 572 → ≈ 77 on Apple aarch64 with the
  assembly backend). **`Field::invert` is no longer constant-time in its input**: every
  inversion-bearing path (`to_affine`, `batch_normalize`, `ff` batch inversions, the
  GLV ladder, downstream Orchard/halo2 users) inherits variable-time inversion. This
  fork's inversion call sites operate on values whose timing is acceptable to leak;
  the previous data-oblivious behavior remains expressible via `pow_vartime(m - 2)`.
  The cheaper inversion, together with the ladder's batched inversions now skipping
  `ff::BatchInverter`'s per-element zero handling (the denominators are provably
  nonzero), re-tunes the GLV batch-affine threshold `BATCH_AFFINE_MIN_POINTS` from
  512 down to 32 live points (its measured break-even; ~5% per point better at 64
  and ~10% at 128 versus the per-point ladders).
- The GLV path now recodes the two halves of the scalar decomposition as a single
  width-3 NAF over the Eisenstein integers instead of two independent width-4 wNAFs,
  cutting the shared-doubling ladder from ~51 to ~39 mixed additions. `glv::Table`
  now stores the eight digit-orbit points with the x-coordinate in all three
  endomorphism rotations, deriving the third from $\zeta^2 = -\zeta - 1$ (1 KiB
  per table, previously 512 B). The public `glv` API and the native constant-time
  `Mul` are unchanged.
- Added `glv::Table::mul_decomposed_batch`, which multiplies many points by one
  scalar on affine accumulators, batching each ladder column's field inversions
  across the batch and fusing nonzero-digit columns as affine `2P+Q`. Batches under
  32 live points, and the scalar-dependent exceptional schedules (checked exactly
  per call), fall back to the per-point ladder.
  `CurveExt::batch_mul_same_scalar_vartime` now routes through it.
- Forked from upstream `pasta_curves` and renamed to `zakura-pasta-curves`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.5.2); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.

### Added

- Added `raw_coordinates` to the Pasta affine point types for callers that
  deliberately need the stored `(0, 0)` representation of the identity.
- Added the hidden `pallas::add_mixed_pair_unchecked` helper for downstream
  batched arithmetic that can expose instruction-level parallelism across
  two incomplete mixed additions.
- `CurveExt::try_multiexp_vartime`, with a GLV Signed-Booth backend for
  large Pallas and Vesta multiscalar multiplications.
- A non-default `multicore` feature parallelizes independent GLV multiscalar
  windows.
- The `aarch64-asm` backend's exponentiation chains (`invert`, `pow_vartime`,
  and the square-root chains) use a fused "square `n` times, then multiply"
  assembly routine that keeps the accumulator in registers for the whole run.

### Changed

- Parallel GLV multiscalar multiplication now combines adjacent window sums
  before shifting their independent pair roots. For the 16-window Orchard
  commitment schedule, this cuts projective window-shift doublings from 960 to
  512 while retaining one schedulable task per window.
- Hash-to-curve now avoids redundant release-mode curve-equation checks after
  the simplified SWU and isogeny formulas, while retaining debug assertions.
  Vesta hash-to-curve is about 5% faster on Apple aarch64.
- The GLV Signed-Booth MSM now finishes batched affine additions while walking
  inversion products backward, avoiding a separate pass over its pending
  addition records.
- The GLV Signed-Booth multiscalar backend stores each pending affine
  addition's left operand in its eventual output slot, avoiding duplicate
  coordinates in the batch-inversion workspace.
- The GLV Signed-Booth multiscalar backend caches each base's affine
  coordinates, endomorphism x-coordinate, and identity flag once per MSM
  instead of extracting them again for every window.
- `Fp` and `Fq` square-root table lookups now hash their normalized
  Montgomery representations directly with generated multiply-and-shift
  perfect hashes. This removes four Montgomery reductions and four integer
  remainders per square root, improving `Fp::sqrt` by 2.3% and `Fq::sqrt` by
  1.8% on Apple AArch64 with the assembly backend.
- GLV affine bucket reductions interleave two independent multiplication
  lanes through their shared inversion and post-inversion chord arithmetic.
- The GLV Signed-Booth multiscalar backend caches each current window's
  nonzero assignments so it does not recode the same components twice.
- The GLV Signed-Booth multiscalar backend reduces bucket trees with batched
  affine additions, variable-time inversion of their denominators, and the
  curve's native projective operations. This backend is already variable-time
  with respect to scalar digits and does not provide a constant-time guarantee.
- The `aarch64-asm` backend now implements runtime multiplication and
  squaring as inline assembly with register operands instead of calls into
  the assembly file. This removes the per-operation call and memory
  round-trip, which speeds up all composed arithmetic — notably curve point
  operations (`double`, mixed addition) and everything built on them.
- The `aarch64-asm` Montgomery multiplication no longer captures and compares
  a provably-zero fifth output limb. Direct `Fp` and `Fq` multiplication
  benchmarks are approximately 1.7% faster on Apple M4. The bound that makes
  the limb provably zero needs a canonical `rhs` (which every caller already
  supplies); the assembly wrappers now debug-assert it, since a violation
  would yield an incorrect residue rather than a merely non-canonical one.
- `Fp::pow_vartime` and `Fq::pow_vartime` now fuse each run of squarings with
  the following multiplication. The sequence of field operations (and thus
  the variable-time profile, which depends only on the exponent) is
  unchanged.
