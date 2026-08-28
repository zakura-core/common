# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Added experimental NuTachyon and V7 transaction support from upstream
  librustzcash, gated by `zcash_unstable="nutachyon"`.
- Prepared the `1.0.0-rc.4` release.
- Documented that the pinned `block-buffer` and `crypto-common`
  dependencies are version pins for the pre-release RustCrypto stack pulled
  in via `bip32`, not direct dependencies of this crate.

- Prepared the `1.0.0-rc.3` release.
- Prepared the `1.0.0-rc.2` release.
- Updated the shielded-protocol dependencies to their `ff 0.14`-compatible
  Zakura versions.
- Forked from upstream `zcash_primitives` and renamed to `zakura-primitives`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.30.0); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
