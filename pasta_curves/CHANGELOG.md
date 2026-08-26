# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Added an `x86_64-asm` feature: MULX/ADCX/ADOX Montgomery multiplication
  and a dedicated squaring for the Pasta fields on x86-64, a
  transcription of the `aarch64-asm` backend's five-limb CIOS rounds with
  the same canonicity contract. Requires BMI2 and ADX (Intel Broadwell /
  AMD Zen or newer; enabling it on an older CPU faults at runtime), and is
  a no-op on other architectures. Measured on Skylake-X: field
  multiplication ~1.25x faster than the portable path and a dedicated
  assembly squaring ~1.05-1.10x (2-5% ahead of squaring through the
  multiplication, mirroring the AArch64 backend's own square-over-mul
  margin). Two slower schedulings are pinned in the module docs so they
  are not retried: squaring routed through the multiplication, and
  interleaved-ADCX/ADOX Montgomery reduction sweeps (~10% slower than the
  two short sequential sweeps on Skylake-X).
- Fixed the `fp`/`fq` benches' `square` cell to call `Field::square`
  explicitly: the inherent (always-portable) `square` shadowed the
  runtime-dispatched trait method, so the cell measured the portable path
  even under the assembly features and once mis-sized an assembly squaring
  decision.
- All of this release's new MSM machinery — the Eisenstein-orbit backend
  (`glv::orbit`), the magnitude-profiled backend planner, the prepared
  zero-checks (`glv::zero`), and the `arithmetic::PreparedZeroCheck` /
  `CurveExt::try_prepare_zero_check` hooks — sits behind a new `orbits`
  feature (implying `glv`), so it can be disabled, refactored, or removed
  wholesale. Without it the arbitrary-scalar MSM plans the Signed-Booth
  backend against the generic estimate exactly as before. halo2 enables
  `orbits` by default.
- Added `glv::zero`: prepared fixed-base multiscalar **zero-checks** for the
  verifier-shaped workload where almost all bases are fixed across many
  checks (an SRS) and only the identity outcome is needed.
  `PreparedZeroMsm::prepare[_with_mode]` precomputes, per fixed base, one
  transformed point per $U_6$-coset of a subgroup
  $G = \langle U_6, \alpha, \beta^k \rangle$ of the residue units of
  $\mathbf{Z}[\omega]/2^c$ ($\alpha = 1 - \omega$, $\beta = 2 - \omega$),
  so a radix-$2^c$ digit factors as $d = u\eta\delta$ through a static
  residue codebook and a window needs one bucket per $G$-orbit instead of
  the $(4^c + 2)/6$ unit orbits — letting the prepared radix widen until
  per-window point visits, not bucket integration, set the cost. Recoding
  is fixed-length with an exactly bounded residual finished by the
  unprepared orbit machinery, per-check extra terms (a proof's own
  commitments) run as their own multiscalar multiplication — the planned
  GLV backends above a small count, a width-matched Signed-Booth pass
  below it — concurrent with the prepared windows under parallelism, and
  every structural property of a codebook (subgroup closure, coset and
  orbit counts, minimal exact lifts, full residue coverage) is re-derived
  and asserted at construction. Preparation also merges bases related by
  exact $u$/$u\alpha$/$u\beta$ relations, found with batched degree-3
  isogeny evaluation. `PreparedZeroMsm::prepare` plans its mode within a
  64 MiB prepared-table budget and returns `None` (and the
  `try_prepare_zero_check` hook declines) when even the smallest mode
  exceeds it — very large base sets — instead of silently allocating
  past the budget; `prepare_with_mode` stays explicit and infallible.
  Measured on 32-core x86-64 (portable backend, Vesta,
  interleaved medians on true zero relations, 2,048 fixed bases): the
  check runs ~1.6x faster than the planned unprepared MSM serially
  (13.4 → 8.4 ms best mode) and up to ~2.4x on 8–16 workers, winning
  every swept cell from 512 to 8,192 terms with no regression at 32
  workers; the classical subset-table baseline (implemented, test-gated),
  given the same batched-affine reduction, stays 18–31% behind at
  comparable-or-larger memory. Preparation costs ~0.1 s and ~10–50 MiB at
  2,048 bases depending on mode (break-even after ~9–20 checks).
- Several same-bases zero-checks batch probabilistically:
  `is_zero_batch_vartime` derives its combining challenge by hashing a
  preparation-time digest of the bases together with every equation, so
  the challenge cannot precede the equations; an explicit-challenge
  variant exists for protocols whose transcript owns the challenge, with
  the $(m-1)/r$ soundness obligation documented. Both variants accept an
  empty batch vacuously.
- Added `arithmetic::PreparedZeroCheck` and
  `CurveExt::try_prepare_zero_check`, an object-safe hook through which
  generic downstream code (halo2's verifier) obtains a prepared zero-check
  without naming the backend; curves without one return `None`.
- The zero-check's coefficient-integration programs recode each fixed
  bucket coefficient in a minimal-weight radix-2 form over the digit set
  $\{0\} \cup U_6$ (exact minimality via 0-1 BFS over the recoding
  recurrence), and orbit representatives are chosen weight-first: 26–31%
  fewer program additions than per-coordinate NAF at every mode, with the
  full-unit mode's program collapsing to the plain valuation reducer.
- The zero-check's recoding emits window-major codes and per-window bucket
  histograms, so each window's staging is one contiguous placement pass
  (the counting pass and the strided matrix walk drop out; parallel window
  tasks stop striding the shared matrix), and the coefficient programs are
  stored position-major: wide modes (over ~112 program additions) sum each
  binary position through the shared batched-affine reduction tree and
  Horner-fold the position sums, while small programs keep the cheaper
  straight-line projective form.
- `CodebookMode` is now an enum, adding `ExponentBox`: a non-subgroup
  residue cover whose prepared variants are a rectangular
  $\alpha^i\beta^j$ box in the unit quotient and whose coefficients tile
  the rest per 2-adic valuation, derived and asserted entirely by
  enumeration (the naive $\langle\bar\alpha\rangle \times
  \langle\bar\beta\rangle$ coordinatization is provably wrong — the two
  generators share a $C_2$ — so the box uses coset coordinates). The
  16×16 box at $c = 8$ reaches 256 variants with only 47 buckets, a
  point the subgroup lattice cannot express; measured, it ties the best
  same-memory subgroup mode within noise without beating it (the lean
  cover's exact digits are larger, costing one extra tail window), so it
  ships as a searchable mode, not a planner default.
- The orbit backend's parallel schedule and the zero-check's parallel
  drivers pair adjacent windows per task as joined subtasks (the schedule
  the Signed-Booth backend already uses), sharing one Horner shift chain
  per pair while keeping every window independently stealable.
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
  Booth backend at its own planned width, with interleaved samples (an
  earlier sequential sweep read +2..6% serially through a harness
  warm-up artifact; see `msm_backend_timings`): serial parity within ±2%
  from 512 to 8,192 terms and +4..5% at 16,384, +19..38% on 8 workers
  and +13..65% on 32 workers at mid-to-large sizes — the orbit's 22–26
  windows keep workers fed that Booth's 10–16 cannot — while Booth is
  kept for small parallel MSMs.
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
  window capping the orbit backend also measured ahead on witness-shaped
  MSMs (+16..20% serial at 2,048–8,192 terms — a pre-correction sweep;
  re-confirm with the interleaved `msm_backend_timings` before leaning on
  the exact figure). End to end,
  interleaved A/B runs of Orchard proving measured the finished planner
  ~2.6% faster serially (k = 11, one action; faster in 3 of 3 matched
  rounds) and ~8% faster on the default 32-thread pool (one-action bundle
  449 ms → 415 ms).
- Every backend (Booth, orbit, and the prepared zero-check below) reduces
  its buckets through the shared fused batched-affine reduction, one window
  at a time. A multi-window variant sharing one Montgomery inversion per
  tree level across window groups was built and *measured as a net loss*
  at every group size above one window — with divstep inversion at
  I/M ≈ 77 the saved inversions are worth microseconds per MSM, while
  staging several windows at once grows the working set from a few hundred
  KiB (in L2) to several MiB swept per reduction level; interleaved A/B
  runs of the serial Orchard k = 11 prover measured 32 MiB groups ~5%
  slower end-to-end — so the single-window primitive is the only shape
  kept. A second experiment replacing the reduction's pending-addition
  records with denominator-only staging and a completion re-walk measured
  within a few percent of the landed fused pass (the records are
  L2-resident within a level), and was likewise not kept.
- Deferred `Fp` and `Fq` product accumulation now fuses the portable
  schoolbook multiplication into the wide accumulator, avoiding a temporary
  eight-limb product and a second carry pass. Deferred inner products measured
  3–5% faster on Apple arm64 and 8–12% faster on x86-64.
- The `sqrt-table` feature now uses `once_cell` (with an exactly-once
  initialization wrapper) instead of `lazy_static` with `spin_no_std`,
  removing the `lazy_static` and `spin` dependencies.

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
