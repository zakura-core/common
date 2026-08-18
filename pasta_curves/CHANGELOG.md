# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Prepared the `1.0.0-rc.2` release.
- Updated the curve traits to `ff 0.14`, `group 0.14`, and `rand_core 0.10`.
- Added explicit `Fp::invert_vartime` and `Fq::invert_vartime` APIs backed by a
  Montgomery-native 62-divstep safegcd port of libsecp256k1's `modinv64`, exploiting
  both Pasta moduli's sparse `[m0, m1, 2, 0, 64]` radix-2^62 shape. The existing
  data-oblivious `Field::invert` implementation remains unchanged; callers must opt
  into the variable-time API where timing leakage is acceptable. The new kernel was
  measured 7.2x faster (4.83 µs → 0.67 µs, I/M ≈ 572 → ≈ 77 on Apple aarch64 with the
  assembly backend).
- Forked from upstream `pasta_curves` and renamed to `zakura-pasta-curves`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.5.2); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.

### Added
- The `aarch64-asm` backend's exponentiation chains (`invert`, `pow_vartime`,
  and the square-root chains) use a fused "square `n` times, then multiply"
  assembly routine that keeps the accumulator in registers for the whole run.

### Changed

- The `aarch64-asm` backend now implements runtime multiplication and
  squaring as inline assembly with register operands instead of calls into
  the assembly file. This removes the per-operation call and memory
  round-trip, which speeds up all composed arithmetic — notably curve point
  operations (`double`, mixed addition) and everything built on them.
- `Fp::pow_vartime` and `Fq::pow_vartime` now fuse each run of squarings with
  the following multiplication. The sequence of field operations (and thus
  the variable-time profile, which depends only on the exponent) is
  unchanged.
