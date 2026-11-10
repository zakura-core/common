# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [5.4.0] - 2026-11-10

### Added

- Added `Action::batch_from_encodings`, with `ActionEncoding` and
  `ActionDecodeError`, which builds Actions from their wire encodings,
  decoding all of their points together and accepting exactly what
  `Action::from_parts` accepts after one-at-a-time decoding
  ([#731](https://github.com/zakura-core/common/pull/731)).

### Changed

- Batch validation with the Sensei backend now normalizes every bundle's value
  commitments together with the binding keys and encodes statements across the
  thread pool ([#725](https://github.com/zakura-core/common/pull/725)).

## [5.3.0] - 2026-11-06

### Changed

- Sped up `BatchValidator::validate` for large batches on multi-threaded
  verifiers by preparing queued bundles across the thread pool
  ([#708](https://github.com/zakura-core/common/pull/708)).
- Sped up `ValueCommitment::derive_public` and binding validating key
  derivation in the Halo 2 backend using precomputed multiples of the value
  commitment base
  ([#712](https://github.com/zakura-core/common/pull/712)).

## [5.2.0] - 2026-11-04

### Changed

- Sped up spend authorizing key derivation by about a third on average,
  Orchard bundle signing by about half per spend, `append_signatures` by one
  scalar multiplication per action, and nullifier derivation with the
  `backend-halo2` feature by about 7%
  ([#680](https://github.com/zakura-core/common/pull/680)).
- With the `backend-halo2` feature, `Note::nullifier` and spend
  authorization key randomization are now variable-time, making them about
  33% and 3.4× faster respectively
  ([#681](https://github.com/zakura-core/common/pull/681)).
- Sped up encoding proof public inputs for proving and verification by reusing
  the stored `rk` and `cv_net` points and normalizing them together, instead of
  decoding each `rk` from bytes
  ([#683](https://github.com/zakura-core/common/pull/683)).

## [5.1.0] - 2026-11-03

### Added

- Added `ValueCommitment::derive_public`, the commitment to a public value with
  a zero trapdoor. It runs in variable time with respect to the value, so it
  must only be given public values such as a bundle's value balance
  ([#672](https://github.com/zakura-core/common/pull/672)).

### Changed

- `Bundle::binding_validating_key` and the builder and PCZT IO finalizer
  binding keys derive the value-balance commitment with
  `ValueCommitment::derive_public`. This drops a multiplication by the zero
  trapdoor and, on the halo2 backend, multiplies only over the value's
  significant bits ([#672](https://github.com/zakura-core/common/pull/672)).
- On the halo2 backend, `ValueCommitment::derive` reads the value-commitment
  generators from precomputed constants instead of hashing to the curve on
  every call ([#672](https://github.com/zakura-core/common/pull/672)).
- The legacy/Halo2 backend retains computed binding-key points and already
  decoded binding and spend authorization keys through signature batching,
  avoiding redundant point decoding for Orchard and Ironwood
  ([#676](https://github.com/zakura-core/common/pull/676)).

## [5.0.0] - 2026-11-02

### Added

- Added the `backend-sensei` feature selecting the Sensei cryptographic
  implementation; select exactly one of `backend-halo2` (the default) and
  `backend-sensei`
  ([#624](https://github.com/zakura-core/common/pull/624)).

### Changed

- Removed the `bitvec` dependency ([#626](https://github.com/zakura-core/common/pull/626)).

### Security

- `keys::FullViewingKey`, `keys::IncomingViewingKey` and
  `keys::OutgoingViewingKey` overwrite their secret components when dropped:
  `nk` and `rivk`, `dk` and `ivk`, and `ovk`. Previously their memory was freed
  without being overwritten, and their private fields left no way to wipe them
  ([#651](https://github.com/zakura-core/common/pull/651)).

## [4.0.0] - 2026-10-20

### Added

- Added the default-enabled `backend-halo2` feature selecting the
  cryptographic implementation; builds with `--no-default-features` must
  enable it explicitly
  ([#591](https://github.com/zakura-core/common/pull/591)).
- Added the `prover` and `verifier` features, which independently enable
  proof creation and proof verification; `circuit` now enables both
  ([#591](https://github.com/zakura-core/common/pull/591)).
- Added `circuit::ProofError`, returned by public proof operations in place
  of `halo2_proofs::plonk::Error`
  ([#591](https://github.com/zakura-core/common/pull/591)).
- Added `primitives::redpallas::SpendAuthRandomizer` with canonical byte and
  stream encodings, used by the builder, key, and PCZT APIs
  ([#591](https://github.com/zakura-core/common/pull/591)).
- Added the `aarch64-asm` feature selecting the aarch64 assembly
  implementation in the proving dependencies
  ([#591](https://github.com/zakura-core/common/pull/591)).
- Added the default-enabled `wallet` feature gating the ZIP 32 wallet
  derivation APIs; builds with `--no-default-features` keep the
  verification and direct-address APIs without the derivation dependency
  ([#587](https://github.com/zakura-core/common/pull/587)).
- Added the default-off `circuit-composition` feature and a curated
  `circuit::composition` interface for composing external proofs from the existing
  Halo2 address-ownership, note-commitment, and nullifier gadgets. Typed witness
  adapters in `circuit::composition::witness` keep derivations and canonical
  encodings owned by Orchard while the
  payment circuit and unrelated implementation details remain private
  ([#613](https://github.com/zakura-core/common/pull/613)).

### Changed

- Updated the indexed-address derivation backend to AES 0.9 and FPE 0.7,
  sharing cipher 0.5 with note encryption while preserving address formats
  and public interfaces
  ([#565](https://github.com/zakura-core/common/pull/565)).
- `primitives::redpallas` now defines Orchard-owned signature domain, key,
  signature, and error types instead of reexporting `reddsa` types
  ([#591](https://github.com/zakura-core/common/pull/591)).
- `circuit::ProvingKey` and `circuit::VerifyingKey` are now opaque; circuit
  synthesis, raw arithmetic conversions, and scalar generators are private
  implementation details
  ([#591](https://github.com/zakura-core/common/pull/591)).
- Proof creation now compiles the halo2 prover once inside `zakura-orchard`
  instead of in every crate that creates proofs, once per RNG type. Public
  signatures and proof bytes are unchanged; a downstream caller's LLVM IR for
  proof creation drops from about 1M lines to about 8k
  ([#596](https://github.com/zakura-core/common/pull/596)).

### Removed

- Removed `memuse::DynamicUsage` implementations for bundles, actions, proofs, nullifiers, rho values, note-encryption domains and prepared incoming viewing keys, together with the `memuse` dependency. Code that measured these types with `dynamic_usage()` or required `T: DynamicUsage` no longer compiles and must estimate sizes itself
  ([#589](https://github.com/zakura-core/common/pull/589)).
- Removed the `unstable-voting-circuits` feature and the public visibility
  of the circuit, gadget, constant, and specification internals it exposed
  ([#591](https://github.com/zakura-core/common/pull/591)).

## [3.0.0] - 2026-10-13

### Added

- Added `circuit::VerifyingKey::capture_verifier_fingerprint` behind the
  `verifier-fingerprint` feature, assembling the verifier equation for a proof
  as an MSM without deciding validity so it can be compared against an
  independent verifier's equation
  ([#559](https://github.com/zakura-core/common/pull/559)).

### Changed

- Changed note-encryption aliases, byte-wrapper signatures, and Domain,
  BatchDomain, and ShieldedOutput implementations to use
  `zakura-note-encryption`. Existing import spelling is preserved, but
  upstream and fork traits and types are not interchangeable
  ([#540](https://github.com/zakura-core/common/pull/540)).
- Generate dummy note addresses without indexed ZIP 32 derivation. Seeded dummy
  generation consumes additional randomness
  ([#551](https://github.com/zakura-core/common/pull/551)).
- Gate indexed ZIP 32 address generation and diversifier-index recovery behind
  the default-enabled `zip32-addresses` feature. Consumers disabling default
  features must opt in to retain these APIs; direct address construction and
  note decryption remain available without FF1
  ([#552](https://github.com/zakura-core/common/pull/552)).
- `circuit::ProvingKey::build` and `circuit::Circuit::from_action_context` are
  now fallible, rejecting every circuit version except
  `OrchardCircuitVersion::PostNu6_3`
  ([#553](https://github.com/zakura-core/common/pull/553)).
- Bundle construction and PCZT proving reject historical bundle versions with
  the new `builder::BuildError::UnsupportedProtocolVersion` and
  `pczt::ProverError::UnsupportedProtocolVersion` errors
  ([#553](https://github.com/zakura-core/common/pull/553)).
- Raised the minimum supported Rust version from 1.91 to 1.97
  ([#567](https://github.com/zakura-core/common/pull/567)).

### Removed

- Removed support for creating proofs under the historical (pre-NU6.3) circuit
  versions, including through raw Halo2 witness synthesis. Verification of
  historical proofs and reconstruction of their verifying keys are unchanged
  ([#553](https://github.com/zakura-core/common/pull/553)).

### Fixed

- Fixed the `unstable-frost` feature failing to compile unless
  `unstable-voting-circuits` was also enabled; it now activates its
  `visibility` dependency itself
  ([#546](https://github.com/zakura-core/common/pull/546)).
- Fixed generated test bundles so their value balances fit the builder's
  signed range ([#567](https://github.com/zakura-core/common/pull/567)).

## [2.1.0] - 2026-09-29

### Added

- Added the `portable` feature to forward portable Pasta field arithmetic
  selection through the proving dependencies
  ([#505](https://github.com/zakura-core/common/pull/505)).

## [2.0.0] - 2026-09-23

### Added

- Added the `prover-fingerprint` feature with complete synthetic prover Lean fixture
  drivers isolated in test tooling, independently of `verifier-fingerprint` and
  without changing `Proof::create`. The tests pin complete proof bytes and input
  RNG tapes for one- and two-Action executions
  ([#415](https://github.com/zakura-core/common/pull/415)).
- Added the opt-in `circuit-fixtures` feature for regenerating Ironwood Action
  circuit and key-generation layout fixtures
  ([#423](https://github.com/zakura-core/common/pull/423)).
- Added an opt-in `x86_64-asm` Cargo feature that forwards through the direct
  Pasta dependency and, when enabled, the optional Halo 2 dependency. Enabling
  it on an x86-64 CPU without BMI2 and ADX support can fault; generic binaries
  should leave it disabled
  ([#432](https://github.com/zakura-core/common/pull/432)).

### Changed

- Updated `verifier-fingerprint` exports to include the validated proof bytes
  and pinned verifying-key description
  ([#423](https://github.com/zakura-core/common/pull/423)).

## [1.2.0] - 2026-09-08

### Added

- Added `circuit::VerifyingKey::pinned_description` and
  `circuit::VerifyingKey::fingerprint`: the pinned circuit description of a
  verifying key as text, and a BLAKE2b-256 digest of it, so consumers can pin
  the verifying key they were built against
  ([#362](https://github.com/zakura-core/common/pull/362)).

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
