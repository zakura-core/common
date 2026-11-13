# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [0.0.2] - 2026-11-13

### Changed

- Replaced the `hex` dependency with `const-hex`; script ASM and descriptor
  key rendering now hex-encode without per-byte string formatting
  ([#742](https://github.com/zakura-core/common/pull/742)).

## [0.0.1] - 2026-10-31

### Added

- Added the complete `zcash_script 0.6.0` implementation as the
  `zakura-zcash-script` package, retaining the `zcash_script` library target,
  the script, interpreter, solver, descriptor, and signature APIs, features,
  and no-std support. The package keeps upstream's Apache-2.0 license,
  inherits Common's edition 2024 and MSRV, and starts at its own version,
  `0.0.1`
  ([#634](https://github.com/zakura-core/common/pull/634)).

### Changed

- Changed `pattern::pay_to_script_hash` and `descriptor::sh` to return a
  `Result`, failing for redeem scripts longer than 520 bytes, which a P2SH
  spend cannot push. Added the `pattern::Error::RedeemScriptTooLarge` and
  `descriptor::Error::RedeemScriptTooLarge` variants
  ([#641](https://github.com/zakura-core/common/pull/641)).
- Changed `pattern::push_pubkey`, and the builders that use it, to reject
  public keys that are not 33 bytes starting with `0x02` or `0x03`, or 65
  bytes starting with `0x04`, with the new `pattern::Error::InvalidPubKey`
  ([#641](https://github.com/zakura-core/common/pull/641)).
- Changed `pattern::check_multisig` to reject thresholds of 0 or above the
  number of keys, with the new `pattern::Error::InvalidThreshold`, and more
  than 20 keys ([#641](https://github.com/zakura-core/common/pull/641)).

### Fixed

- Fixed `descriptor::multi` and `descriptor::sortedmulti` accepting a
  threshold of 0, which produces an output that anyone can spend
  ([#641](https://github.com/zakura-core/common/pull/641)).
- Fixed the encoding of `OP_PUSHDATA1`, `OP_PUSHDATA2`, and `OP_PUSHDATA4`
  lengths, which were written as script numbers instead of fixed-width
  unsigned fields. Pushes of 128–255 bytes gained an extra byte that the
  parser read as data, so P2SH multisig spends with 4–7 keys were invalid.
  Script parsing and evaluation are unchanged
  ([#647](https://github.com/zakura-core/common/pull/647)).

### Security

- Fixed `pattern::sha256_htlc_with_unconditional` omitting `OP_DUP` in its
  unconditional branch, which let anyone who knew the hashed public key
  spend with their own key
  ([#641](https://github.com/zakura-core/common/pull/641)).

## Record of Fork

Forked from [`zcash_script 0.6.0`](https://crates.io/crates/zcash_script/0.6.0),
from [upstream commit 8d2fc24](https://github.com/ZcashFoundation/zcash_script/commit/8d2fc24b63a3f38fab25517e223e421b8f07aa68)
(`zcash_script/` in that repository). The published artifact's SHA-256 is
`10106859d08a2a4119af8a0fa8db72afe35647768b562f94b7a2124adad41275`, and its
sources are byte-identical to that commit's. The import keeps the script,
interpreter, solver, descriptor, and signature code unchanged, and uses
Common's edition 2024 and MSRV. It retains an independent package version,
initially `0.0.1`, until it joins Common's coordinated version. The other
changes are `rustfmt` for edition 2024, which only reorders imports and
rewraps lines, and two test-only fixes so the tests compile in every feature
combination: the crate tests gate their signature-validation imports, and the
descriptor tests import `ToString` from `alloc` instead of `std`. The
`libfuzzer-sys` development dependency, which only upstream's fuzz workspace
used, is dropped. Upstream authors and the Apache-2.0 license are retained.
