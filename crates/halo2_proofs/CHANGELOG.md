# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [1.1.0-rc.1] - 2026-09-03

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
- Improved witness-synthesis performance for `V1` circuits that reuse a
  proving-key floor plan by avoiding redundant fixed-table assignments
  ([#334](https://github.com/zakura-core/common/pull/334)).
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
- Reduced proof-creation latency by overlapping public-instance commitments
  and polynomial transforms with the continuous witness-to-advice preparation
  path ([#345](https://github.com/zakura-core/common/pull/345)).

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
