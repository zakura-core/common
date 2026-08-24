# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Sinsemilla witness generation now uses the configured field backend for
  projective squares and reuses precomputed first-word witnesses for Orchard
  MerkleCRH hashing.
- Fixed-base multiplication witness generation now accumulates incomplete
  additions in mixed Jacobian coordinates, deferring affine inversions through
  the existing rational advice representation.
- Poseidon Pow5 witness generation now caches fixed-size raw round states,
  eliminating per-round temporary vector allocations.
- Fixed-base witness interpolation now specializes its Horner multiplication
  for each three-bit window digit, replacing full field multiplications with
  short doubling and addition chains.
- Public-initialized Sinsemilla hashing now derives its existing affine
  witnesses from an in-place Jacobian accumulator that caches its squared
  projective denominator, reducing witness-generation arithmetic and memory
  traffic without changing the circuit layout.
- Field-element bit-range witnesses are reconstructed in 64-bit chunks instead
  of one bit at a time.
- Internal proof-test helpers and benchmarks satisfy the `Sync` circuit /
  `Send` configuration bounds that `zakura-halo2-proofs`'s `create_proof` now
  requires; public gadget APIs are unchanged.
- Removed the `bitvec` (unused), `lazy_static` (replaced by
  `std::sync::LazyLock`), and `uint` (replaced by explicit unreduced limb
  arithmetic in variable-base scalar decomposition) dependencies, and moved
  the test-only `rand` dependency to dev-dependencies.

- Poseidon, Sinsemilla, and ECC witness generation now use direct small-power,
  doubling, and word-extraction paths instead of generic exponentiation,
  multiplication by two, and intermediate allocations.
- Fixed-base multiplication witness generation now reconstructs window points
  from precomputed interpolation and coordinate constants instead of repeating
  curve arithmetic and batch normalization.
- Prepared the `1.0.0-rc.3` release.
- Prepared the `1.0.0-rc.2` release.
- Updated the circuit stack to `ff 0.14`, `group 0.14`, and `rand 0.10`.
- Forked from upstream `halo2_gadgets` and renamed to `zakura-halo2-gadgets`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.5.0); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
