# Changelog

All notable public API changes to this support crate will be documented here.

## [Unreleased]

## [4.0.0] - 2026-10-20

### Added

- Added this support crate holding the dependency closure of Orchard's
  legacy backend, selected through `zakura-orchard`'s `backend-halo2`
  feature; depend on `zakura-orchard` rather than on this crate
  ([#591](https://github.com/zakura-core/common/pull/591)).

## Record of Fork

This crate was introduced in Common to hold Orchard's optional legacy dependency
closure. It contains no independent fork of cryptographic code. The reexported
workspace crates retain their own licensing and provenance records. Orchard
consumers select this implementation through `zakura-orchard`'s `backend-halo2`
feature.
