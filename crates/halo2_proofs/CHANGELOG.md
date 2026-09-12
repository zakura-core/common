# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

### Added

- Added an opt-in `x86_64-asm` Cargo feature that forwards to Pasta's
  BMI2/ADX field-arithmetic backend. Enabling it on an x86-64 CPU without
  BMI2 and ADX support can fault; generic binaries should leave it disabled.

## [1.2.0] - 2026-09-08

### Added

- Added `Circuit::CACHE_CONFIGURATION`, `Circuit::cache_configuration`,
  `Circuit::configuration_from_cache`, and the opaque `CircuitConfigCache`
  type, letting circuits opt into retaining their key-generation
  configuration in the proving key for reuse by `create_proof`. All trait
  items are defaulted, so existing `Circuit` implementations are unaffected.
  The Orchard Action circuits opt in because their configuration contains
  immutable circuit-structure handles
  ([#385](https://github.com/zakura-core/common/pull/385)).

### Changed

- Reused the retained coefficient-basis commitment table for both generator
  MSMs in the first IPA round. At `k = 11`, each MSM has 1,024 active
  coefficients; zero-padding the other half keeps the existing prepared-table
  API while skipping its prepared-point fetches and bucket insertions. Across
  100 paired `k = 11` openings with ten workers on Apple M4, the change reduced
  the opening proof from 11.573 ms to 11.316 ms, a 0.257 ms (2.22%) speedup with
  a paired bootstrap 95% confidence interval of 0.213 to 0.300 ms. Preparation
  cost and retained memory are unchanged
  ([#313](https://github.com/zakura-core/common/pull/313)).

- The IPA opening prover now normalizes each round's two transcript points as
  one batch, replacing two base-field inversions with one. This removes one
  inversion per opening round, or 11 inversions at `k = 11`, without changing
  preparation or retained memory. Across 100 paired `k = 11` openings with ten
  workers on Apple M4, the change reduced the opening proof from 11.6027 ms to
  11.5452 ms, a 0.0575 ms speedup
  ([#339](https://github.com/zakura-core/common/pull/339)).
- Parallelized rational advice evaluation across circuits while retaining
  circuit-ordered blinding and transcript work. Across 100 paired prepared-key
  Ironwood proofs on AMD Linux with six workers, this reduced two-Action
  proving time from 199.629 ms to 198.463 ms and four-Action proving time from
  351.730 ms to 349.318 ms. Preparation, keygen, retained key memory, proof
  bytes, and public APIs are unchanged; the measured four-Action shape can use
  up to roughly 657 KiB more transient batch-inversion scratch
  ([#346](https://github.com/zakura-core/common/pull/346)).
- Reduced cold four-Action Orchard proof generation by 0.759 ms (0.56%) in a
  24-pair, 10-worker arm64 macOS benchmark by avoiding 364 full-domain
  polynomial-leaf copy passes in the quotient evaluator. The underlying
  quotient phase improved by 0.112 ms for one Action and 0.685 ms for four
  Actions on macOS, and by 0.207 ms and 0.426 ms with six workers on x86_64
  Linux. One-Action macOS and both Linux whole-proof intervals crossed zero.
  Proof bytes, scratch and retained memory, and public APIs are unchanged
  ([#351](https://github.com/zakura-core/common/pull/351)).
- Reduced quotient-evaluation latency by consuming retained cache entries
  directly instead of copying them through scratch storage
  ([#354](https://github.com/zakura-core/common/pull/354)).
- Reduced prover latency for circuits with lookup and permutation grand
  products by building quotient prefixes without materializing every
  denominator inverse. This removes 12,765 scalar-field multiplications per
  Action in Orchard's k=11 circuit and reduced four-Action proof time by
  0.269 ms on Apple M4 with 10 workers and 1.283 ms on AMD EPYC Linux with
  6 workers ([#356](https://github.com/zakura-core/common/pull/356)).
- Reduced four-circuit proof-generation latency by preparing independent
  permutation column sets concurrently across circuits. The permutation phase
  improved by 8.6% on Apple arm64 with 10 workers and 6.0% on x86_64 Linux
  with 6 workers; the single-circuit path is unchanged
  ([#357](https://github.com/zakura-core/common/pull/357)).
- Reduced cold Orchard proof generation by 0.668 ms (1.27%) for one Action and
  1.340 ms (1.00%) for four Actions in a 20-pair, 10-worker Apple M4 benchmark
  by reusing each lookup table commitment for its corresponding input
  commitment. Preparation and retained memory are unchanged; the prover uses
  one additional 64 KiB transient buffer per in-flight `k = 11` lookup
  ([#358](https://github.com/zakura-core/common/pull/358)).
- Reduced permutation-product commitment work by committing constant-prefix
  products from their constant coefficient, blinded-tail deltas, and
  commitment blind. In real post-NU6.3 two-Action Ironwood payment proofs,
  this route hits once per Action. At k=11, each hit replaces a 2,049-term
  Lagrange commitment with a prefix scan and at most seven terms.
  In 64 candidate-minus-control pairs on an Apple M4 with 10 workers, the sum
  of the six permutation-product commitment closure times changed by
  -1.4592 ms (-10.43%, 95% CI [-2.0230, -0.8955] ms), while the full prover
  was neutral at -0.0167 ms (-0.0226%, 95% CI [-0.2701, +0.2368] ms). In 192
  single-worker AMD Linux pairs, the same closure-time sum changed by
  -1.4763 ms (-4.770%, 95% CI [-1.6171, -1.3354] ms); the full-prover result
  was -1.2097 ms (-0.1248%, 95% CI [-2.4638, +0.0444] ms) and statistically
  unresolved
  ([#359](https://github.com/zakura-core/common/pull/359)).
- Reduced named floor-planner witness-assignment latency by using dense
  occurrence counters and bounded compact name lookup
  ([#360](https://github.com/zakura-core/common/pull/360)).
- Reduced Orchard prover latency by reusing the prepared coefficient SRS for
  the first four IPA rounds and materializing their folded generators once.
  At `k = 11`, the default multicore no-orbits preparation retains another
  3.75 MiB. This reduced one-Action proof time by 2.323 ms on Apple M4 with
  10 workers, and by 3.309 ms on x86_64 Linux with 6 workers; four-Action
  Linux proofs improved by 4.302 ms
  ([#361](https://github.com/zakura-core/common/pull/361)).
- Reduced deferred IPA generator-fold materialization work by replacing its
  width-six signed-radix table with a width-seven wNAF table. The prepared
  payload remains exactly 3.75 MiB, with no measurable added preparation cost
  and no public API change. On Apple M4 with 10 workers, one- and four-Action
  proofs improved by 0.447 ms and 0.411 ms. On x86_64 Linux with 6 workers,
  four-Action proofs improved by 2.617 ms; the one-Action result was unresolved
  with no measured regression
  ([#363](https://github.com/zakura-core/common/pull/363)).
- Reduced quotient-evaluation latency by combining cached left addends with
  simple right addends in one pass. This eliminates 96 domain-sized cache-copy
  passes from the retained four-circuit plan
  ([#365](https://github.com/zakura-core/common/pull/365)).
- Reduced transient allocation churn while preparing sorted lookup
  permutations. For Post-NU6.3 Orchard proofs at `k = 11`, this removes 6
  reallocations, 782,976 bytes of requested allocation traffic, and 390,912
  bytes of peak retained lookup-vector capacity for one Action; for four
  Actions, it removes 24 reallocations, 3,131,904 bytes of requested
  allocation traffic, and 1,563,648 bytes of peak retained lookup-vector
  capacity. Ten-worker Apple M4 proof latency was neutral, while proof bytes
  and public APIs are unchanged
  ([#366](https://github.com/zakura-core/common/pull/366)).
- Reduced prepared Post-NU6.3 two-Action Orchard proof generation by 1.23% on
  an Apple M4 and 1.17% on x86_64 Linux by factoring the 1,019 repeated `q_0`
  terms out of each Sinsemilla permuted-table commitment. Other lookup tables,
  non-`q_0` coefficients, and random blind-tail coefficients are unchanged;
  the route adds no retained memory
  ([#367](https://github.com/zakura-core/common/pull/367)).
- Enabled the assembly-accelerated Pasta field backend on Unix AArch64 targets,
  extending the existing automatic Apple AArch64 configuration to Android and
  other Unix targets
  ([#370](https://github.com/zakura-core/common/pull/370)).
- Reduced multi-opening prover work by deriving the q-prime evaluation from
  synthetic-division remainders instead of evaluating another domain-sized
  polynomial. In a focused `k = 11` benchmark using Orchard's point-set shape,
  this reduced the replaced work from 20.851 to 2.015 microseconds on x86-64
  and from 7.371 to 1.017 microseconds on Apple M4
  ([#373](https://github.com/zakura-core/common/pull/373)).
- Reduced proving-key generation time by parallelizing independent
  verification-key commitments
  ([#374](https://github.com/zakura-core/common/pull/374)).
- Reduced retained quotient-evaluation latency by accumulating cached weighted
  terms directly instead of copying them through the reusable fold buffer. This
  eliminates 40, 86, and 172 full-domain copies for one-, two-, and four-Action
  proofs: 40, 86, and 172 MiB of logical memory traffic at the current Orchard
  domain size. On Apple M4 with 10 workers, the four-Action retained evaluator
  improved by 0.200 ms; the one-Action result was neutral. On x86-64 Linux with
  6 workers, the exact four-Action cache-consumer kernel improved by 0.778 ms
  ([#377](https://github.com/zakura-core/common/pull/377)).
- Overlapped remainder-derived q-prime evaluation preparation with the
  domain-sized multi-opening evaluations. For Orchard's `k = 11` shape, this
  reduced their combined one-proof latency by 8.63% with six workers on
  x86-64 Linux and by 7.34% with six workers on Apple M4, while saturated
  five-proof throughput was unchanged within measurement uncertainty
  ([#380](https://github.com/zakura-core/common/pull/380)).
- Reduced the sorted 10-bit range-check input-commitment work in prepared
  Post-NU6.3 Orchard proofs by about 54% on Apple M4 and 57% on x86_64 Linux
  for real two-Action payments. One-worker full-proof means were lower by
  0.195% and 0.074%, respectively, but statistically unresolved. At `k = 11`,
  preparation retains another 384 KiB and uses 576 KiB of projective
  construction scratch
  ([#381](https://github.com/zakura-core/common/pull/381)).
- Reduced reusable weighted quotient folds directly into their output buffer.
  This removes 48, 58, and 60 MiB of logical copy traffic from one-, two-, and
  four-Action proofs, respectively, plus 512 KiB of transient field storage.
  On Apple M4 with 10 workers, the retained evaluator improved by 0.044 ms for
  one Action and 0.105 ms for four Actions. On x86-64 Linux with 6 workers, the
  one-Action retained evaluator improved by 0.047 ms; the four-Action result
  was neutral with a 0.093 ms point improvement
  ([#382](https://github.com/zakura-core/common/pull/382)).
- Avoided 2,042 GLV decompositions per Action when committing the permuted
  10-bit range-check table in prepared Post-NU6.3 Orchard proofs. This reduced
  the isolated one-worker kernel by 9.88% on x86-64 Linux; the measured
  two-Action full-proof change was statistically unresolved
  ([#384](https://github.com/zakura-core/common/pull/384)).
- Overlapped instance polynomial transforms with advice preparation after
  witness synthesis. This reduced two-Action Orchard proving latency with six
  workers by 0.33 ms on Apple M4 and 0.63 ms on x86-64 Linux
  ([#386](https://github.com/zakura-core/common/pull/386)).
- Reduced retained quotient-evaluation latency by folding scaled constraint
  addends into the existing deferred-product accumulation. In cold Orchard
  proofs with 10 workers on Apple M4, the quotient evaluator improved by
  0.051 ms for one Action and 0.286 ms for four Actions across 52 paired
  samples. With six workers on AMD Linux, it improved by 0.402 ms (1.06%) and
  2.030 ms (1.55%), respectively, across 16 paired samples. Proof bytes,
  retained-plan payload, and public APIs are unchanged
  ([#388](https://github.com/zakura-core/common/pull/388)).
- Parallelized preparation of the sorted 10-bit range-check commitment's
  cached Lagrange suffix multiples. With six workers on Apple M4, the cache
  construction was 36.9% faster and prepared Orchard key setup was 2.25%
  faster. With eight workers on x86-64 Linux, they were 60.6% and 3.45%
  faster, respectively
  ([#389](https://github.com/zakura-core/common/pull/389)).
- Pruned inverse FFTs for zero-padded instance columns, skipping butterflies
  whose inputs are known to be zero
  ([#390](https://github.com/zakura-core/common/pull/390)).
- Reduced Orchard instance polynomial transform work by factoring out a
  proving-key-cached support polynomial
  ([#391](https://github.com/zakura-core/common/pull/391)).
- Reduced permutation-product preparation time by directly transforming
  constant-prefix products with short blinded tails. In 200 paired real
  post-NU6.3 two-Action Ironwood payment proofs on an Apple M4 with 10 workers,
  the permutation-product phase improved by 5.81% and full proving time by
  0.58%. Proof behavior and the public API are unchanged
  ([#392](https://github.com/zakura-core/common/pull/392)).
- Reduced measured grand-product prefix-construction latency by 14–22% in
  isolated Apple M4 and x86-64 Linux benchmarks. Proof behavior and the public
  API are unchanged
  ([#394](https://github.com/zakura-core/common/pull/394)).
- Reduced retained quotient-evaluation latency for the constant scale factor
  4 by replacing a general field multiplication with two field doublings in
  fused evaluator paths. Across 240 interleaved paired blocks of 12 real
  post-NU6.3 two-Action Ironwood proofs per arm, whole-proof latency improved
  by 0.106 ms (0.145%) with 10 workers on Apple M4 and by 0.173 ms (0.124%)
  with 8 workers on x86_64 Linux. Proof bytes, evaluator memory, and public
  APIs are unchanged
  ([#395](https://github.com/zakura-core/common/pull/395)).
- Skip fraction and prefix-product construction for permutation sets that
  statically leave every cell in place
  ([#396](https://github.com/zakura-core/common/pull/396)).
- Reduced Orchard permutation-product latency by cancelling the 94.20% of
  cells that the mapping leaves fixed inside its two partially active
  permutation sets. At six workers this removes 87,345 field multiplications
  per Action and avoids 3,397,888 bytes per Action of dense field-array update
  traffic. On 64-bit targets, requested fraction-buffer allocation payload
  falls from 262,144 to 64,136 bytes per Action; the proving key grows by
  3,840 payload bytes plus 384 bytes of container storage, excluding allocator
  metadata. Variable-time zero handling retains only the first cancelled-zero
  row and allocates no per-row marker buffer. Permutation sets with more than
  one-third active rows retain the existing dense path. Whole identity sets
  continue to use the existing direct construction. Proof bytes, verifier
  behavior, and public APIs are unchanged
  ([#399](https://github.com/zakura-core/common/pull/399)).
- Reduced multi-circuit rational-advice latency by deriving equal and squared
  Sinsemilla denominator batches from one retained batch. This shortens each
  circuit witness's existing inversion walk without adding an inversion.
  Combined witness synthesis and rational evaluation improved by 5.3% for six
  circuits on both Apple M4 and x86_64 Linux
  ([#401](https://github.com/zakura-core/common/pull/401)).

### Fixed

- Rejected unsupported parameter-size exponents during deserialization instead
  of constructing inconsistent parameters or panicking
  ([#379](https://github.com/zakura-core/common/pull/379)).
- Supported constant-only polynomial evaluation without panicking
  ([#379](https://github.com/zakura-core/common/pull/379)).
- Made proving-key generation reject commitment parameters whose domain does
  not match the verifying key instead of panicking
  ([#391](https://github.com/zakura-core/common/pull/391)).

## [1.1.0] - 2026-09-04

### Added

- Added the `V1Named` floor planner for assigning regions in an order that is
  independent of the cached circuit plan
  ([#340](https://github.com/zakura-core/common/pull/340)).
- Added `Region::assign_advice_batch`, with corresponding default methods on
  `RegionLayouter` and `Assignment`, for assigning a contiguous advice-column
  range without constructing unused cell handles
  ([#342](https://github.com/zakura-core/common/pull/342)).

### Changed

- Reduced warm proof-generation time by 1.9–6.5% in 1–4-action
  benchmarks by caching compressed-selector evaluations in each proving key
  for reuse during quotient construction, at a per-key cost of about 20.5 MiB
  and 13.7–19.8% additional key-generation time
  ([#145](https://github.com/zakura-core/common/pull/145)).
- Single-circuit proofs now prepare independent permutation column sets in
  parallel on multicore pools while retaining product-chain, randomness, and
  transcript order. Multi-circuit scheduling is unchanged
  ([#226](https://github.com/zakura-core/common/pull/226)).
- Polynomial evaluation now caches repeated linear terms in Lagrange and
  extended Lagrange bases within a 4 MiB incremental field-buffer budget
  ([#230](https://github.com/zakura-core/common/pull/230)).
- Concurrent and repeated `Params::prepare_zero_checks` and
  `Params::prepare_commitments` calls now share the first non-panicking cache
  result across parameter clones, avoiding duplicate prepared-table
  construction and retention. Backend declines are memoized; initialization
  panics still propagate and remain retryable
  ([#232](https://github.com/zakura-core/common/pull/232)).
- Prepared commitment setup now reports a backend decline once a Pasta SRS
  reaches the prepared-table footprint cap, beginning at `k = 13`, instead of
  building and retaining tables beyond that budget
  ([#233](https://github.com/zakura-core/common/pull/233)).
- Prepared prover commitments remain enabled through ten effective threads on
  AArch64 macOS for Orchard-sized (`k = 11`) parameter sets, where Apple M4
  measurements showed lower end-to-end prover latency. Wider pools and
  unmeasured SRS shapes retain the planned multiexp route; the verifier keeps
  its separate eight-worker bound
  ([#234](https://github.com/zakura-core/common/pull/234)).
- Quotient-piece folding now reuses its highest piece as the accumulator and
  fuses each coefficient's multiply-add, avoiding an intermediate allocation
  and parallel-pass overhead during proof generation. Proof behavior and the
  public API are unchanged
  ([#248](https://github.com/zakura-core/common/pull/248)).
- Multi-opening proof generation now performs each linear-factor synthetic
  division in existing coefficient storage, avoiding a new polynomial
  allocation for every division. The public API and proof behavior are
  unchanged
  ([#249](https://github.com/zakura-core/common/pull/249)).
- On sufficiently large multi-opening proofs, independent point-set quotient
  terms are now prepared concurrently instead of serially, while the
  simultaneously retained field-element payload is capped at 8 MiB. Ordered
  folding, proof behavior, and the public API are unchanged
  ([#250](https://github.com/zakura-core/common/pull/250)).
- Proof generation now batches all post-challenge PLONK polynomial queries
  into one evaluator worker wave, removing repeated evaluator scheduling while
  preserving transcript order and successful proof bytes. There is no
  downstream public API change
  ([#251](https://github.com/zakura-core/common/pull/251)).
- Multi-opening proof generation now evaluates independent point-set quotient
  polynomials concurrently above the existing work threshold, reuses
  accumulator storage, and fuses final scale-and-add passes. This avoids fresh
  accumulator storage and extra coefficient passes while retaining input and
  transcript order; proof behavior and the public API are unchanged
  ([#252](https://github.com/zakura-core/common/pull/252)).
- Improved quotient-polynomial construction performance during proof generation
  ([#262](https://github.com/zakura-core/common/pull/262)).
- Quotient construction now fuses inverse-transform output permutation,
  normalization, sparse vanishing division, and quotient-piece construction,
  and processes independent coefficient columns in parallel. This avoids
  reversing, dividing, and copying the full coefficient buffer in separate
  passes during proof generation
  ([#263](https://github.com/zakura-core/common/pull/263)).
- Reduced cold one- and four-Action Orchard proof generation by 1.038 ms
  (1.84%) and 1.056 ms (0.75%), respectively, in a guarded 60-pair,
  10-worker Apple M4 benchmark. The prover now commits to the linear
  quotient-evaluation mask with a three-base MSM and evaluates it with a
  multiply-add, replacing a 2,049-term commitment and 2,048-term inner
  product. Proof encoding and verification are unchanged, but deterministic
  proof bytes for a fixed RNG seed change
  ([#267](https://github.com/zakura-core/common/pull/267)).
- `Params::prepare_commitments` now builds and uses coefficient- and
  Lagrange-basis prepared tables under the default `multicore` feature,
  without requiring `orbits`
  ([#270](https://github.com/zakura-core/common/pull/270)).
- The `arithmetic` re-export now exposes `PreparedZeroCheck` and
  `CurveExt::try_prepare_zero_check` whenever either `multicore` or `orbits`
  is enabled
  ([#270](https://github.com/zakura-core/common/pull/270)).
- Prepared coefficient- and Lagrange-basis commitments now evaluate their
  blinds with a private fixed-base table and overlap blind evaluation with the
  prepared polynomial MSM
  ([#271](https://github.com/zakura-core/common/pull/271)).
- Proof generation now handles direct polynomial-leaf scales by `-1`, `1`,
  and `2` with negation, copying, and doubling instead of general field
  multiplication. Orchard quotient plans contain 19 scales by `2` per Action,
  eliminating 311,296 general multiplications for one-Action proofs and
  1,245,184 for four-Action proofs
  ([#276](https://github.com/zakura-core/common/pull/276)).
- Uses deferred inner products for polynomial evaluation and IPA proving while
  retaining parallelism at higher abstraction levels
  ([#277](https://github.com/zakura-core/common/pull/277)).
- Proof generation now defers quotient-piece fold reductions and reuses one
  challenge-power vector across multi-opening evaluations and IPA setup. Proof
  behavior and the downstream public API are unchanged
  ([#279](https://github.com/zakura-core/common/pull/279)).
- Prepared coefficient- and Lagrange-basis commitments now consume their
  polynomial scalars and fixed blind suffix without joining them in a transient
  allocation ([#281](https://github.com/zakura-core/common/pull/281)).
- Cached inverse FFT normalization now uses optimized inverse-power scaling
  for Pasta fields, and quotient construction fuses scaling into its existing
  output pass. Proof behavior and the public API are unchanged
  ([#283](https://github.com/zakura-core/common/pull/283)).
- Cached field FFTs now interleave pairs of power-of-two chunks below each
  parallel split, reducing measured transform and proof-generation latency
  without changing proof behavior or the public API
  ([#284](https://github.com/zakura-core/common/pull/284)).
- Used variable-time curve operations in multiexponentiation paths whose
  inputs are public. Proof format, transcript, and verifier behavior are
  unchanged ([#288](https://github.com/zakura-core/common/pull/288)).
- Reduced quotient-evaluator planning work in first and later `create_proof`
  calls for one-, two-, and four-circuit batches by preparing sparse cache
  schedules during key generation. Isolated 10-worker Apple M4 Max benchmarks
  saved 0.25 ms for one circuit and 1.00 ms for four circuits; isolated
  six-worker AMD EPYC benchmarks saved 0.50 ms and 1.93 ms respectively.
  Preparing all three schedules added 2.8 ms to median Orchard key generation
  on the 10-worker Apple system. The schedules retain 19 KiB in total, are
  shared by proving-key clones, and do not alter proof bytes or verification
  ([#291](https://github.com/zakura-core/common/pull/291)).
- IPA opening proof creation now tracks the folded polynomial evaluation and
  challenge-power scale symbolically, reducing scalar-field work while
  preserving proof behavior and the public API
  ([#298](https://github.com/zakura-core/common/pull/298)).
- Cold proof generation for a single-circuit batch now overlaps instance
  polynomial transforms with circuit synthesis. In the first-proof Orchard
  k = 11 benchmark, this reduced one-action latency by 0.77 ms with 10 macOS
  workers and 2.11 ms with 6 Linux workers, without changing proof bytes or
  the downstream public API
  ([#299](https://github.com/zakura-core/common/pull/299)).
- Reduced quotient-evaluator work in cold and later `create_proof` calls for
  one-, two-, and four-circuit batches by compiling a challenge-independent
  quotient plan during key generation, then binding theta, beta, gamma, and y
  for each proof. In 40-sample, fresh-process paired benchmarks, this follow-up
  to #291 saved 0.37 ms for one circuit and 2.14 ms for four circuits on a
  10-worker Apple M4; 0.53 ms and 1.68 ms on the same system with six workers;
  and 2.77 ms and 8.21 ms on a six-worker AMD Linux VM. A final direct bracket
  found no setup regression against #291: paired setup medians were +0.08 ms
  and -0.13 ms, with both confidence intervals spanning zero. The proving key
  retains 676,640 bytes of compiled-plan payload across the three batch sizes,
  shared by its clones and bounded by a 1 MiB aggregate retained-payload cap.
  This cap does not bound transient allocations while key generation prepares
  the plans in parallel; one-, two-, and four-circuit plans are retained in
  that priority order if a different circuit topology reaches the cap. Ordered
  polynomial-role, length, and compressed-selector shape validation falls back
  to fresh compilation, and proof bytes, transcripts, and verification are
  unchanged ([#300](https://github.com/zakura-core/common/pull/300)).
- Exact-shape public-instance commitments now reuse positioned fixed-base
  tables, share equal rows across a proof batch, and normalize the resulting
  commitments together. This reduced the targeted Orchard commitment stage by
  12-57% across the measured Linux worker widths while retaining the generic
  MSM for other instance shapes
  ([#301](https://github.com/zakura-core/common/pull/301)).
- Prepared public-instance commitments now use signed width-four positioned
  tables. This shrinks the prepared table from about 260 to 224 KiB and
  reduced the targeted two-Action Orchard stage by 15-18% at the measured
  worker widths
  ([#304](https://github.com/zakura-core/common/pull/304)).
- Reduced CPU used by Pasta lookup permutation preparation by caching canonical
  field encodings across input sorting and merging
  ([#305](https://github.com/zakura-core/common/pull/305)).
- Reduced cold four-Action Orchard proof generation by 0.714 ms (0.50%) in a
  100-pair, 10-worker Apple M4 benchmark by consuming quotient-evaluator
  constants without first materializing constant polynomials. The retained
  one- and four-Action plans avoid 154 and 526 constant-vector fills,
  respectively, eliminating 77 MiB and 263 MiB of logical writes; a
  constant-by-constant product also becomes one scalar multiplication instead
  of a 16,384-row scaling pass. One-Action latency was statistically neutral,
  and proof bytes and downstream public APIs are unchanged
  ([#306](https://github.com/zakura-core/common/pull/306)).
- Reduced cold one- and four-Action Orchard proof generation by 0.311 ms
  (0.46%) and 1.008 ms (0.57%), respectively, in a 100-pair, six-worker
  Apple M4 benchmark by accumulating scaled quotient-evaluator addends in
  place. Proof bytes and public APIs are unchanged
  ([#310](https://github.com/zakura-core/common/pull/310)).
- Reduced cold one- and four-Action Orchard proof generation by 0.182 ms
  (0.27%) and 0.417 ms (0.24%), respectively, in a 100-pair, six-worker
  Apple M4 benchmark by comparing cached Pasta lookup sort keys as four
  64-bit limbs instead of 32 individual bytes. Proof bytes and public
  APIs are unchanged
  ([#311](https://github.com/zakura-core/common/pull/311)).
- Reduced cold one-Action Orchard proof generation by 0.314 ms (0.55%) in a
  100-pair, 10-worker Apple M4 benchmark by preparing all columns of each
  permutation-ratio set in one parallel traversal per phase. This removes
  per-column parallel dispatches, repeated chunk-offset exponentiations, and
  30,618 net field multiplications per Action. Four-Action Apple M4 and
  six-worker AMD Linux benchmarks showed no regression. Proof bytes and
  downstream public APIs are unchanged
  ([#315](https://github.com/zakura-core/common/pull/315)).
- Reduced cold four-Action Orchard proof generation by 1.191 ms (0.85%) in a
  60-pair, 10-worker Apple M4 benchmark and by 1.516 ms (0.44%) in a 120-pair,
  six-worker AMD Linux benchmark. The prover now defers lookup-permutation
  basis transforms until after product construction, removing two base-domain
  clones per lookup and overlapping independent transform and commitment work.
  One-Action Apple M4 performance was neutral. Proof bytes and downstream
  public APIs are unchanged
  ([#318](https://github.com/zakura-core/common/pull/318)).
- Documented that proof creation and multiexponentiation, including prover
  commitments over witness- and blinding-derived scalars, are variable-time.
  Proof format, transcript, and verifier behavior are unchanged
  ([#319](https://github.com/zakura-core/common/pull/319)).
- Cached contiguous per-level FFT twiddles in proving keys. A
  component-isolated benchmark reduced first-proof latency for a prepared
  Orchard k=11 four-action proof by 0.565% on 10-worker Apple arm64; one action
  and the six-worker x86_64 Linux gates were neutral. The cache retains an
  additional 585,656 bytes per independently generated Orchard proving key on
  64-bit targets, excluding allocator and reference-count metadata, and is
  shared by clones. Proof format and verification are unchanged
  ([#324](https://github.com/zakura-core/common/pull/324)).
- Reduced cold one- and four-Action Orchard proof generation by 0.799 ms
  (1.44%) and 1.075 ms (0.77%), respectively, in a 100-pair, 10-worker
  Apple M4 benchmark, and by 1.268 ms (0.99%) and 2.662 ms (0.77%) in a
  100-pair, six-worker AMD Linux benchmark. The quotient evaluator now reuses
  each chunk's deferred weighted-fold buffers across 48 groups for one Action
  and 60 for four Actions, avoiding about 15,000 and 18,900 transient
  allocations per proof. Proof bytes, retained proving-key memory, and public
  APIs are unchanged
  ([#325](https://github.com/zakura-core/common/pull/325)).
- Retained the linear quotient-evaluation mask as its two coefficients instead
  of a domain-sized zero-padded polynomial. At Orchard k=11 this reduces the
  allocation from 2,048 field elements (64 KiB) to two (64 bytes), and avoids
  adding the zero tail during the multi-opening fold. Proof bytes and public
  APIs are unchanged
  ([#326](https://github.com/zakura-core/common/pull/326)).
- Prepared Orchard's sparse quotient and IPA masking commitments with a shared
  signed-width-four fixed-base table. The two commitments together became
  about 51, 64, and 103 microseconds faster at one, six, and ten workers on the
  measured Apple M4 system, for 416 KiB of retained affine-point payload
  ([#332](https://github.com/zakura-core/common/pull/332)).
- Changed the public-domain `x^(2^k)` calculation used by proof creation and
  verification to call Pasta's dedicated repeated-squaring implementation.
  At `k = 11`, the isolated calculation was 63.6x faster on Apple M4 and
  64.9x faster on x86_64 Linux; proof bytes and transcripts are unchanged
  ([#333](https://github.com/zakura-core/common/pull/333)).
- Prepared both fixed IPA generators for prover commitments. A signed table
  with eight-bit windows now handles the `w` blinding term and the `u` and `w`
  terms in each IPA round. In 100 paired ten-worker Apple M4 measurements, the
  isolated IPA phase fell from 11.744 to 11.615 ms, a 0.129 ms (1.10%) reduction
  with a 95% confidence interval of 0.089 to 0.169 ms. A full cold-process
  benchmark of this change with #332's earlier width-three table reduced the
  explicitly timed proof phase by 0.184 ms (0.34%) for one action. Its
  four-action estimate was 0.295 ms (0.21%) faster but unresolved. The table
  retains exactly 512 KiB of affine-point payload on Pasta, only 2 KiB more
  than the previous `w`-only table. It remains shared by parameter clones and
  is not serialized ([#336](https://github.com/zakura-core/common/pull/336)).
- Built the independent coefficient-basis, Lagrange-basis, and fixed-base pair
  commitment tables concurrently during multi-worker preparation. This reduced
  full cold preparation from about 36.4 to 18.9 ms at both six and ten workers
  on the measured Apple M4 system. In 100-pair fresh-process Linux measurements,
  preparation fell from 96.456 to 53.890 ms at two workers, 97.130 to 49.709 ms
  at four, and 97.276 to 49.780 ms at six. The one-worker path remains
  sequential. Retained memory is unchanged by this scheduling step; measured
  peak-RSS increases on Linux ranged from 204 to 936 KiB. Proof encoding and
  verification are unchanged
  ([#336](https://github.com/zakura-core/common/pull/336)).
- Clarified that the annotation and value closures passed to the advice-batch
  assignment APIs receive zero-based indices relative to the start of the
  batch
  ([#344](https://github.com/zakura-core/common/pull/344)).
- Reduced multi-circuit proof-creation latency on multi-worker pools by
  overlapping public-instance polynomial transforms with witness synthesis;
  single-circuit proving already overlapped these phases and is unchanged
  ([#345](https://github.com/zakura-core/common/pull/345),
  [#348](https://github.com/zakura-core/common/pull/348)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Added

- Added `FloorPlanner::synthesize_batch`, a default-implemented trait method
  that synthesizes several instances of the same circuit in one call, together
  with the opaque `plonk::FloorPlan` type for floor-planning data that a proving
  key retains; the built-in `V1` floor planner overrides it to plan a circuit
  once, reuse that plan across every proof made with the key, and synthesize
  independent circuit witnesses in parallel. Every circuit passed to
  `create_proof` must have the shape used to generate the proving key.
- Added the opt-in `orbits` cargo feature (off by default) together with the
  `Params::prepare_zero_checks` and `Params::prepare_commitments` methods, which
  build cached tables over the fixed commitment bases so that the verifier's
  final check and the prover's commitments evaluate faster on thread pools of up
  to eight threads; the tables cost memory and setup time amortized across uses,
  are shared by clones of the params, and are never serialized, so they must be
  built again after `Params::read`. Without the feature both methods do nothing
  and return `false`.

### Changed

- Renamed the package from `halo2_proofs` to `zakura-halo2-proofs`; the library
  target keeps its original name, so existing `use` paths compile unchanged.
- Updated `ff` and `group` from 0.13 to 0.14 and `rand_core` from 0.6 to 0.10;
  the field and group traits in this crate's API come from the new releases,
  randomness parameters such as those of `create_proof` now bound the rand_core
  0.10 `Rng` trait (previously `RngCore`), and the `batch` feature sources
  system randomness through `rand` 0.10 instead of `rand_core`'s `getrandom`
  feature.
- Replaced the `pasta_curves` dependency with `zakura-pasta-curves` 1.0.0,
  whose types appear in this crate's API.
- Replaced the `halo2_legacy_pdqsort` dependency with
  `zakura-halo2-legacy-pdqsort` 1.0.0; it remains optional behind the
  `floor-planner-v1-legacy-pdqsort` feature and its types do not appear in
  this crate's API.
- Required the circuit type passed to `create_proof` and `keygen_pk` to
  implement `Sync`, and its configuration to implement `Send`, so that witnesses
  for independent circuit instances can be synthesized in parallel.
- Changed how the prover consumes randomness: blinding values are drawn in a
  fixed circuit order before parallel work begins, and the polynomial masking
  the final commitment-opening scalar is sampled on a small fixed support
  instead of across the full degree range. Proofs generated from a seeded RNG
  therefore differ byte-for-byte from the original crate's, while the proof
  format and its verification are unchanged, and proof bytes do not depend on
  the number of threads.
- Adopted variable-time algorithms for the prover's and verifier's
  multiexponentiations and batch field inversions; proving time already
  depended on inputs in the original crate, and the timing behavior of the
  underlying field arithmetic is documented by `zakura-pasta-curves`.
- Sped up proof creation substantially; `create_proof` now scales across
  available threads and across the circuit instances proved in a single call,
  and the `multicore` feature also enables parallelism in the underlying Pasta
  curves library.
- Sped up proof verification, in both `verify_proof` and the `batch` feature's
  `BatchVerifier`.
- Sped up parameter and key generation (`Params::new`, `keygen_vk`, and
  `keygen_pk`).
- Enabled an assembly-accelerated field-arithmetic backend on Apple aarch64
  targets, speeding up proving and verification there without any configuration.
- Raised the minimum supported Rust version to 1.91 and migrated the crate to
  the 2024 edition.

### Fixed

- Fixed `verify_proof` to return an error when the supplied parameters are too
  small to accommodate the verifying key's blinding rows, instead of
  underflowing while validating instance lengths.
- Fixed the multi-opening prover and verifier in `poly::multiopen` to reject an
  empty query set with an error — the prover previously panicked — and to reject
  duplicate queries of the same commitment at the same point even when the
  supplied evaluations agree.
- Fixed the multi-opening verifier to return an error instead of panicking when
  the squeezed evaluation challenge coincides with one of the queried points.
- Fixed proving of custom-gate expressions whose rotation magnitude exceeds the
  circuit's row count; when evaluated over the extended domain, such rotations
  now wrap around the domain cyclically instead of panicking.

## Record of Fork

`zakura-halo2-proofs` began as a fork of the `halo2_proofs` crate and has been
developed independently in this repository since. This changelog starts at the
fork point: history up to that point is documented in the repository the code
was forked from, and this crate's version lineage restarted at `1.0.0` rather
than continuing the original `0.3.5` numbering.

- Forked from: `halo2_proofs 0.3.5`, published from
  [zcash/halo2](https://github.com/zcash/halo2) at commit
  [`8e22adbd`](https://github.com/zcash/halo2/commit/8e22adbdce480e5db7625df56aff9c2c8ca79f8f).
- Imported into this repository in commit `16d18d2a43d0aecdfcf9e9d02469c16ebf20e50b`.
