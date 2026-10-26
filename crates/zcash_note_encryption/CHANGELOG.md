# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

### Changed

- **Breaking:** `NoteEncryption::encrypt_outgoing_plaintext` now requires
  `CryptoRng` in addition to `Rng`, including when an outgoing viewing key is
  supplied. Callers must use a securely seeded cryptographic RNG.

## [4.0.0] - 2026-10-20

### Changed

- **Breaking:** `NoteEncryption::encrypt_outgoing_plaintext` now takes a
  `rand_core` 0.10 `Rng` instead of a `rand_core` 0.6 `RngCore`, so callers
  pass the same generators they use with the rest of Common. Without an
  outgoing viewing key it still fills the random outgoing cipher key and then
  the outgoing plaintext from that generator, and ciphertexts are unchanged
  ([#573](https://github.com/zakura-core/common/pull/573)).

## [3.0.0] - 2026-10-13

### Added

- Added the complete `zcash_note_encryption 0.4.2` implementation as the
  `zakura-note-encryption` package, retaining the `zcash_note_encryption`
  library target, note-encryption and recovery APIs, features, and no-std
  support. The package inherits Common's edition 2024 and MSRV 1.91
  ([#540](https://github.com/zakura-core/common/pull/540)).

### Changed

- Updated the ChaCha20/Poly1305 backend to share ChaCha20 0.10 with Rand,
  preserving key and cached keystream zeroization, ciphertext formats, and
  public interfaces
  ([#545](https://github.com/zakura-core/common/pull/545)).
- Raised the minimum supported Rust version from 1.91 to 1.97
  ([#567](https://github.com/zakura-core/common/pull/567)).

## Record of Fork

Forked from [`zcash_note_encryption 0.4.2`](https://crates.io/crates/zcash_note_encryption/0.4.2),
from [upstream commit a8c90d1](https://github.com/zcash/zcash_note_encryption/commit/a8c90d1ce3737cc5898e0bf232ea325a5a61ec9f).
The published artifact's SHA-256 is
`e1cb1b9170c94370e3d66c5cc0877661db743337588b64de7711239eed462198`.
Imported in Common commit [a00286a0](https://github.com/zakura-core/common/commit/a00286a0).
The ownership migration imports the complete implementation without changing
cryptographic behavior, using Common's coordinated package version, edition,
and MSRV. Upstream authors and the MIT and Apache-2.0 licenses are retained.
