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

- Added a serial deferred-field inner-product operation, with a private
  AArch64 block kernel for the Pasta fields
  ([#277](https://github.com/zakura-core/common/pull/277)).
- Added `PreparedZeroCheck::multiexp_with_prefix_and_suffix`, a variable-time
  multiscalar multiplication that accepts fixed-base scalars as two consecutive
  slices and provides a compatibility-preserving default implementation
  ([#281](https://github.com/zakura-core/common/pull/281)).
- Added doc-hidden arithmetic bridges for multiplying `Fp` and `Fq` by an
  inverse power of two without a full field multiplication
  ([#282](https://github.com/zakura-core/common/pull/282)).
- Added the doc-hidden `arithmetic::{square_fp_n, square_fq_n}` cross-crate
  bridges for invoking the dedicated repeated-squaring implementation
  ([#333](https://github.com/zakura-core/common/pull/333)).

### Changed

- The default prepared zero-check planner now caps the dominant retained
  per-table payload at 13 MiB. For an Orchard-sized SRS, alpha-seven accounts
  for about 12.4 MiB per table, or 24.8 MiB for halo2's coefficient and
  Lagrange pair, instead of the previous beta pair's 96.9 MiB. These figures
  exclude small metadata and allocator overhead; they are not total heap or
  RSS. The selected mode, `prepared_bytes` accounting, and decline threshold
  can therefore change
  ([#233](https://github.com/zakura-core/common/pull/233)).
- Improved multicore Signed-Booth MSM performance by evaluating each window
  independently and combining the ordered sums with one Horner fold
  ([#245](https://github.com/zakura-core/common/pull/245)).
- GLV MSMs now skip two exceptional-case coordinate comparisons per ordinary
  affine bucket pair and reuse reduction buffers, reducing common-path
  arithmetic and allocation work. Exceptional pairs retry the unchanged level
  with complete affine formulas
  ([#246](https://github.com/zakura-core/common/pull/246)).
- AArch64 Pasta field inversion now defers the three-multiply negative-eta
  divstep formula until its branch is taken, avoiding speculative work and
  reducing measured direct-inversion latency. The algorithm and outputs are
  unchanged, and non-AArch64 machine code is unaffected
  ([#268](https://github.com/zakura-core/common/pull/268)).
- `PreparedZeroCheck` and `CurveExt::try_prepare_zero_check` are now
  available when either `multicore` or `orbits` is enabled; their signatures
  are unchanged, and single-core `glv` builds remain unaffected
  ([#270](https://github.com/zakura-core/common/pull/270)).
- Prepared affine MSM bucket reductions now compact successful incomplete
  additions into their existing point buffer and reuse level storage, while
  exceptional pairs retain the complete affine fallback
  ([#272](https://github.com/zakura-core/common/pull/272)).
- Reduced measured Apple M4 latency for 2,048-term, four-output prepared
  fixed-base evaluations by about 0.14–0.21 ms and removed a 128 KiB transient
  allocation
  ([#274](https://github.com/zakura-core/common/pull/274)).
- Processes AArch64 deferred-field inner products in 32-product blocks with
  four interleaved accumulator lanes
  ([#280](https://github.com/zakura-core/common/pull/280)).
- Changed Pallas and Vesta addition, doubling, and batch normalization to use
  variable-time identity and exceptional-case handling. This also affects
  scalar multiplication built from these group operations; callers must not
  assume secret-independent timing
  ([#319](https://github.com/zakura-core/common/pull/319)).
- Reduced cold four-Action Orchard proof generation by 0.475 ms (0.34%) in a
  100-pair, 10-worker Apple M4 benchmark by combining the 19 independently
  evaluated windows of each prepared point-returning α7 MSM with one ordered
  Horner fold. This removes 567 redundant projective doublings per full-window
  evaluation. A one-Action benchmark showed no regression. On the same commit,
  a 400-pair, six-worker AMD Linux benchmark improved four-Action proofs by
  0.970 ms (0.285%). Verifier zero checks retain their paired-window schedule;
  proof bytes and public APIs are unchanged
  ([#320](https://github.com/zakura-core/common/pull/320)).
- Changed `Fp` and `Fq` `PartialEq` comparisons to variable-time operation,
  reducing isolated equality latency by approximately 36% on Apple M4 while
  retaining `ConstantTimeEq` for callers that explicitly require
  constant-time equality
  ([#330](https://github.com/zakura-core/common/pull/330)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Added

- Added `CurveExt::try_multiexp_vartime`, an optional variable-time multiscalar
  multiplication whose default implementation returns `None`; with the `glv`
  feature, Pallas and Vesta provide an optimized implementation that declines
  (returning `None`) input sizes it does not expect to speed up, and every
  scalar must be public.
- Added `CurveExt::batch_mul_same_scalar_vartime`, which multiplies every point
  in a slice by one shared scalar; the scalar must be public, and with the `glv`
  feature the Pallas and Vesta implementations batch the work shared across the
  points.
- Added `CurveExt::fft_vartime`, an unnormalized variable-time FFT over curve
  points that writes affine outputs and reports whether a specialized
  implementation ran; the default returns `false`, and Pallas and Vesta provide
  an implementation under the `glv` feature.
- Added `glv::Table::mul_decomposed_batch`, which multiplies several precomputed
  tables by one decomposed scalar while sharing the scalar's digit schedule
  across the whole batch.
- Added a `raw_coordinates` method to the Pallas and Vesta affine point types
  (available with the `alloc` feature), returning the stored coordinate pair
  directly, with the identity encoded as `(0, 0)`.
- Added the `deferred` cargo feature, which exposes the `deferred` module: the
  `DeferredField` trait and wide `Product` accumulator let callers accumulate
  multiple unreduced Montgomery products and perform a single reduction, for
  sums of products such as inner products.
- Added the `orbits` cargo feature, which enables reusable prepared fixed-base
  multiscalar zero-checks — `CurveExt::try_prepare_zero_check`, the object-safe
  `arithmetic::PreparedZeroCheck` trait, and the `glv::zero` module with
  `PreparedZeroMsm`, `CodebookMode`, and `combine_equations` — plus an
  additional multiscalar-multiplication backend that `try_multiexp_vartime`
  selects per input; everything gated by this feature runs in variable time and
  requires public inputs.
- Added the `multicore` cargo feature (which implies `glv`), running the
  variable-time multiscalar multiplications, curve FFTs, and batched curve
  operations in parallel on a Rayon thread pool.
- Added the opt-in `aarch64-asm` cargo feature, which compiles an assembly
  field-arithmetic backend on Apple AArch64 targets for faster field and curve
  operations; it has no effect on other targets.

### Changed

- Renamed the package from `pasta_curves` to `zakura-pasta-curves`; the library
  target keeps its original name, so existing `use` paths compile unchanged.
- Updated `ff` and `group` from 0.13 to 0.14, with random sampling moving from
  `rand_core` 0.6 to `rand`/`rand_core` 0.10; consumers see the reorganized
  trait surfaces — affine-point methods now come from the new
  `group::CurveAffine` trait, `group::Curve::AffineRepr` is renamed to `Affine`,
  and `Group::random`/`Field::random` gain fallible `try_random` counterparts.
- Sped up field and curve arithmetic across all targets; scalar multiplication,
  batch normalization to affine, square roots, and hashing to the curve are
  faster with no changes to the API.
- Raised the minimum supported Rust version to 1.91 and migrated the crate to
  the 2024 edition.

## Record of Fork

`zakura-pasta-curves` began as a fork of the `pasta_curves` crate and has been
developed independently in this repository since. This changelog starts at the
fork point: history up to that point is documented in the repository the code
was forked from, and this crate's version lineage restarted at `1.0.0` rather
than continuing the original `0.5.2` numbering.

- Forked from: `pasta_curves 0.5.2`, published from
  [zcash/pasta_curves](https://github.com/zcash/pasta_curves) at commit
  [`c41c5149`](https://github.com/zcash/pasta_curves/commit/c41c5149d8e6deebada48afa5ed8fadce3ff875c).
- Imported into this repository in commit `16d18d2a43d0aecdfcf9e9d02469c16ebf20e50b`.
