# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## [5.0.0] - 2026-11-02

### Changed

- Sped up `Script::read` by reading script bytes in bulk
  ([#631](https://github.com/zakura-core/common/pull/631)).
- Changed the script types in public signatures, such as `address::Script`
  and `TransparentAddress::script`, from the `zcash_script` package to
  `zakura-zcash-script`. Import paths are unchanged, but upstream
  `zcash_script` types cannot be mixed with the fork's
  ([#634](https://github.com/zakura-core/common/pull/634)).

### Fixed

- Fixed signing P2SH multisig inputs whose redeem script contains an
  uncompressed public key. `Bundle::apply_signatures` now signs for keys in
  either encoding, and the PCZT spend finalizer uses the signatures for the
  compressed keys, returning `UncompressedPubkeyInScript` only when they do not
  meet the threshold
  ([#641](https://github.com/zakura-core/common/pull/641)).
- Fixed signed P2SH multisig spends with 4–7 keys, whose redeem script
  pushes the previous encoding broke
  ([#647](https://github.com/zakura-core/common/pull/647)).

### Security

- Changed `zip48::FullViewingKey::standard` to reject repeated public keys
  with the new `FullViewingKeyError::DuplicatePubKeys`. A repeated key let
  its holder count once per occurrence toward the multisig threshold
  ([#641](https://github.com/zakura-core/common/pull/641)).

## [4.0.0] - 2026-10-20

### Added

- Added the default `pczt` feature, which gates the `pczt` module and
  `builder::TransparentBuilder::build_for_pczt`, and the `bip32` feature, which
  gates the conversions between `keys::TransparentKeyScope` /
  `keys::NonHardenedChildIndex` and `bip32::ChildNumber`
  ([#580](https://github.com/zakura-core/common/pull/580)).
- Added the default-enabled `wallet` feature gating the ZIP 32 wallet
  derivation APIs; builds with `--no-default-features` keep the
  verification and direct-address APIs without the derivation dependency
  ([#587](https://github.com/zakura-core/common/pull/587)).
- Added `coinbase::Error::InvalidBuilderConfiguration`, returned when a
  coinbase builder is given a standard transaction configuration, so
  that case is reported separately from `coinbase::Error::UnexpectedInputs`
  ([#587](https://github.com/zakura-core/common/pull/587)).

### Changed

- The `bip32` dependency is now optional and the `zcash_script` descriptor
  feature is requested only by `transparent-inputs`, so builds without default
  features and without `transparent-inputs` no longer compile BIP 32. Such
  builds that use the PCZT types or the `ChildNumber` conversions must enable
  `pczt` or `bip32`; `transparent-inputs` now implies `pczt`
  ([#580](https://github.com/zakura-core/common/pull/580)).

## [3.0.0] - 2026-10-13

### Changed

- Updated to stable `bip32` 0.6, `secp256k1` 0.33, and `zcash_script` 0.6 as
  required by the cipher backend migration. `TransparentSignatureContext` no
  longer has lifetime/type parameters; `prepare_transparent_signatures` and
  PCZT input signing/signature methods no longer accept a secp256k1 context
  ([#545](https://github.com/zakura-core/common/pull/545)).
- Raised the minimum supported Rust version from 1.91 to 1.97
  ([#567](https://github.com/zakura-core/common/pull/567)).

## [2.0.0] - 2026-09-23

### Added

- Added the `zakura-transparent` package as a source-compatible fork of
  `zcash_transparent 0.10.0`, preserving the `zcash_transparent` library target
  and public API ([#471](https://github.com/zakura-core/common/pull/471)).

### Changed

- Renamed the package from `zcash_transparent` to `zakura-transparent`; the
  library target keeps its original name, so existing `use` paths compile
  unchanged.
- Replaced `zcash_protocol` with the `zakura-protocol` package while preserving
  the `zcash_protocol` dependency key and public type paths.
- Raised the minimum supported Rust version from 1.88 to 1.91.

## Record of Fork

`zakura-transparent` began as a fork of the `zcash_transparent` crate and has
been developed independently in this repository since. This changelog starts
at the fork point: history up to that point is documented in the repository
the code was forked from, and this crate's version lineage follows the Zakura
Common workspace rather than continuing the original `0.10.0` numbering.

- Forked from: `zcash_transparent 0.10.0`, published from
  [zcash/librustzcash](https://github.com/zcash/librustzcash) at commit
  [`97aefdc3`](https://github.com/zcash/librustzcash/commit/97aefdc39a037da9c4f19a0e8a450d2c7932f53e).
