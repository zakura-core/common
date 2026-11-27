# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [0.1.3] - 2026-11-13

### Added

- Added `configure_workers` and `worker_budget`, with `WorkersConfigError`,
  to bound the process-wide worker pool shared by proving, verification, and
  pooled RedPallas batch verification before it initializes
  ([#735](https://github.com/zakura-core/common/pull/735)).
- Added `warm_up_verifier_scratch`, which provisions one batch's verification
  scratch (one final-MSM workspace and its chunk equations) for an expected
  batch shape and returns a `VerificationPlan`: the provisioned capacities,
  whether they pass the idle cache's retention checks, the cache's workspace
  slot count, and the bound on idle cached scratch. The plan describes cache
  policy; it does not reserve scratch, limit concurrent verification, or
  bound active memory
  ([#735](https://github.com/zakura-core/common/pull/735)).

### Changed

- Changed the worker pool's default size: unless `configure_workers` sets it,
  a positive `RAYON_NUM_THREADS` now sizes the pool, ahead of the detected
  parallelism. A process that exports the variable for its own Rayon pools
  now gets a Sensei pool of that size as well
  ([#735](https://github.com/zakura-core/common/pull/735)).
- Batch verification now reuses per-chunk equation scratch and the final-MSM
  workspace from bounded idle pools whose slot counts follow the worker
  budget. Scratch within the per-entry capacity ceilings returns to a free
  slot after success and reported errors alike, a call that finds no idle
  entry allocates one, and the accounted capacity of idle scratch stays
  within a fixed bound for the worker budget (320 MiB at 16 workers, 640 MiB
  at 32 or more) ([#735](https://github.com/zakura-core/common/pull/735)).
- Verification parallelism now follows the work: folding cuts at most one
  chunk per two Actions and runs single-chunk batches on the calling thread,
  the final MSM requests one task per 128 terms, and the batch's transcript
  points enter the final MSM as slices of at least 1,024 points, so a
  one-bundle batch no longer fans out across the whole pool. These floors
  were tuned on a 16-core/32-thread Intel i9-7960X, and the 128-term floor
  was confirmed on an Apple M4 Max
  ([#735](https://github.com/zakura-core/common/pull/735)).

## [0.1.2] - 2026-11-10

### Changed

- Sped up batch verification: proof points decode together ahead of transcript
  reading, instance commitments walk doubling-free fixed-base tables (about
  245 KiB prepared at warmup) with a bundle's shared anchor term computed once,
  and RedPallas batch verification decodes its points together and runs its
  equation on the worker pool for larger batches
  ([#725](https://github.com/zakura-core/common/pull/725)).

## [0.1.1] - 2026-11-04

### Added

- Added `redpallas::SigningKey::negate` and
  `redpallas::SigningKey::randomize_with_verification_key`, which reuse the
  stored verification key instead of recomputing it
  ([#680](https://github.com/zakura-core/common/pull/680)).

## [0.1.0] - 2026-10-31

### Added

- Enabled crates.io publication of native Orchard primitives, Ironwood proving,
  and historical proof verification
  ([#624](https://github.com/zakura-core/common/pull/624)).

### Changed

- Removed `Fp::to_le_bits` and `Fq::to_le_bits`; read the canonical
  little-endian bits from `to_bytes` instead. The crate no longer depends on
  `bitvec` ([#637](https://github.com/zakura-core/common/pull/637)).

## Record of Fork

`zakura-sensei` is an original implementation imported into the Zakura
Common workspace in commit
[`5d4d6b82`](https://github.com/zakura-core/common/commit/5d4d6b82).
It retains an independent package version, initially `0.1.0`.
