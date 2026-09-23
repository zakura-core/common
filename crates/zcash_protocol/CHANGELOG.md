# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

### Changed

- Renamed the package from `zcash_protocol` to `zakura-protocol`; the library
  target keeps its original name, so existing `use` paths compile unchanged.
- Raised the minimum supported Rust version from 1.88 to 1.91.

## Record of Fork

`zakura-protocol` began as a fork of the `zcash_protocol` crate and has been
developed independently in this repository since. This changelog starts at the
fork point: history up to that point is documented in the repository the code
was forked from, and this crate's version lineage follows the Zakura Common
workspace rather than continuing the original `0.10.5` numbering.

- Forked from: `zcash_protocol 0.10.5`, published from
  [zcash/librustzcash](https://github.com/zcash/librustzcash) at commit
  [`97aefdc3`](https://github.com/zcash/librustzcash/commit/97aefdc39a037da9c4f19a0e8a450d2c7932f53e).
- Imported into this repository in commit `80583d0e88b8550b621c59fd1c2db8bf8c1d7e79`.
