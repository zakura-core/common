# Changelog

All notable public API changes to this support crate will be documented here.

## [Unreleased]

## Record of Fork

This crate was introduced in Common to hold Orchard's optional legacy dependency
closure. It contains no independent fork of cryptographic code. The reexported
workspace crates retain their own licensing and provenance records. Orchard
consumers select this implementation through `zakura-orchard`'s `backend-halo2`
feature.
