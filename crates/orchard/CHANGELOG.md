# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [1.1.0] - 2026-09-04

### Changed

- Prepared proving remains enabled through ten effective threads on AArch64
  macOS for Orchard's `k = 11` SRS, retaining the faster prepared route in
  end-to-end Apple M4 measurements while wider pools continue to use the
  planned multiexp
  ([#234](https://github.com/zakura-core/common/pull/234)).
- `ProvingKey::prepare_proving` now prepares prover commitments under the
  default multicore feature set, without requiring orbit MSMs
  ([#270](https://github.com/zakura-core/common/pull/270)).
- Default no-orbits prepared proving now retains an additional approximately
  0.5 MiB fixed-base blind table to reduce repeated proof time
  ([#271](https://github.com/zakura-core/common/pull/271)).
- Improved Orchard proof-creation latency by preparing Merkle-path arithmetic
  concurrently with independent circuit witness assignment
  ([#340](https://github.com/zakura-core/common/pull/340)).

## [1.0.1] - 2026-08-29

### Changed

- Moved the repository from zakura-core/libraries to zakura-core/common;
  crate metadata and the packaged README now point at the new URL
  ([#266](https://github.com/zakura-core/common/pull/266)).

## [1.0.0] - 2026-08-28

### Added

- Added `ProvingKey::verifying_key`, which returns the `VerifyingKey`
  corresponding to a proving key by cloning the key material it already contains
  instead of rerunning key generation.
- Added `ProvingKey::prepare_proving` and
  `VerifyingKey::prepare_batch_validation`, which build and cache
  precomputations over the key's parameters: the former speeds up subsequent
  proof creation and the latter subsequent proof verification (including
  `bundle::BatchValidator`), on thread pools of up to eight effective threads,
  with wider pools automatically keeping the unprepared paths. Both return
  whether the precomputation was actually built, and are no-ops returning
  `false` unless the opt-in `orbits` feature is enabled.
- Added `MerkleHashOrchard::combine_batch`, which combines many same-level
  Merkle node pairs in one call, producing the same digests as repeated
  `Hashable::combine` at a lower per-pair cost for large batches.
- Added `tree::testing::arb_merkle_hash`, a proptest strategy producing
  arbitrary Orchard note-commitment tree nodes, to the `test-dependencies`
  testing utilities.
- Added an opt-in `orbits` cargo feature that enables the halo2 backend
  precomputation used by `ProvingKey::prepare_proving` and
  `VerifyingKey::prepare_batch_validation`; without it those methods keep the
  unprepared proving and verification paths.
- Added a `weighted-merkle` cargo feature that computes the Orchard Merkle CRH
  through fixed-length Sinsemilla word hashing, producing identical digests; it
  also exposes `MerkleHashBatchWorkspace` and
  `MerkleHashOrchard::combine_batch_with_workspace`, which reuse allocations
  across batched Merkle hashing calls.

### Changed

- Renamed the package from `orchard` to `zakura-orchard`; the library target
  keeps its original name, so existing `use` paths compile unchanged.
- Updated `ff` and `group` from 0.13 to 0.14 and `rand`/`rand_core` from 0.8/0.6
  to 0.10; every public function that takes an RNG now bounds it by rand 0.10's
  `Rng` trait (plus `CryptoRng` where already required) in place of the old
  `RngCore`, and `MerkleHashOrchard` sampling now implements `Distribution` for
  rand's `StandardUniform`.
- Replaced the `halo2_proofs` dependency with `zakura-halo2-proofs` 1.0.0,
  whose types appear in this crate's API.
- Replaced the `halo2_gadgets` dependency with `zakura-halo2-gadgets` 1.0.0,
  whose types appear in this crate's API.
- Replaced the `pasta_curves` dependency with `zakura-pasta-curves` 1.0.0,
  whose types appear in this crate's API.
- Replaced the `reddsa` dependency with `zakura-reddsa` 1.0.0, whose types
  appear in this crate's API.
- Replaced the `sinsemilla` dependency with `zakura-sinsemilla` 1.0.0.
- Replaced the `halo2_poseidon` dependency with `zakura-halo2-poseidon` 1.0.0.
- Sped up `ProvingKey::build` and `VerifyingKey::build`, which now load
  precomputed parameters and fixed-base tables embedded in the crate instead of
  regenerating them on every call.
- Sped up batched trial decryption of Orchard notes through the
  `zcash_note_encryption` batch interfaces.
- Sped up note commitment computation and Merkle tree hashing.
- Raised the minimum supported Rust version to 1.91 and migrated the crate to
  the 2024 edition.

## Record of Fork

`zakura-orchard` began as a fork of the `orchard` crate and has been developed
independently in this repository since. This changelog starts at the fork
point: history up to that point is documented in the repository the code was
forked from, and this crate's version lineage restarted at `1.0.0` rather than
continuing the original `0.15.5` numbering.

- Forked from: `orchard 0.15.5`, published from
  [zcash/orchard](https://github.com/zcash/orchard) at commit
  [`29d1d55d`](https://github.com/zcash/orchard/commit/29d1d55db62153dcaeef8ef631c8991c53ed1248).
- Imported into this repository in commit `16d18d2a43d0aecdfcf9e9d02469c16ebf20e50b`.
