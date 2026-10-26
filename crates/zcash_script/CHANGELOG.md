# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html). Entries describe
the crate's public API and observable behavior from a consumer's perspective;
internal implementation details are not tracked here.

## [Unreleased]

## Record of Fork

Forked from [`zcash_script 0.6.0`](https://crates.io/crates/zcash_script/0.6.0),
from [upstream commit 8d2fc24](https://github.com/ZcashFoundation/zcash_script/commit/8d2fc24b63a3f38fab25517e223e421b8f07aa68)
(`zcash_script/` in that repository). The published artifact's SHA-256 is
`10106859d08a2a4119af8a0fa8db72afe35647768b562f94b7a2124adad41275`, and its
sources are byte-identical to that commit's. The import keeps the script,
interpreter, solver, descriptor, and signature code unchanged, and uses
Common's coordinated package version, edition 2024, and MSRV. Two changes
come with it: `rustfmt` for edition 2024, which only reorders imports and
rewraps lines, and gating the test module's signature-validation imports so
its tests compile with `--no-default-features`. The `libfuzzer-sys`
development dependency, which only upstream's fuzz workspace used, is
dropped. Upstream authors and the Apache-2.0 license are retained.
