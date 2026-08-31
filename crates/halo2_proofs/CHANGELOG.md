# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

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
