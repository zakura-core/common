# Orchard implementation and proof capabilities

Orchard selects its cryptographic implementation at compile time. The
`backend-halo2` feature selects the Halo2/Pasta implementation and is enabled by
default. Builds that disable default features must select it explicitly:

```sh
cargo build -p zakura-orchard --no-default-features \
  --features backend-halo2,circuit,multicore,zip32-addresses
```

`prover` enables bundle and PCZT proof creation; `verifier` enables standalone,
bundle, and batch proof verification. The `circuit` feature enables both roles.
Protocol primitives work without `std`. Assembly and diagnostic features use
weak forwarding and do not activate an implementation themselves.

`zakura-keys` and `zakura-primitives` forward `backend-halo2` and retain it in
their defaults. Selecting it in the keys crate does not enable that crate's
optional Orchard dependency. Standalone `zakura-reddsa` and
`zakura-reddsa-frost` select Pallas with the default-enabled `pallas-pasta`
feature; disabling it leaves their Jubjub support available.

## Public API migration

These are intentional breaking changes for a coordinated major release.

- Use opaque `ProvingKey` and `VerifyingKey`, protocol versions, semantic
  `Instance`, key fingerprints and preparation methods, bundle/PCZT workflows,
  standalone `Proof::verify`, and `BatchValidator`.
- Circuit synthesis, `Config`, raw `Proof::create`, gadgets, voting-circuit
  exports, pinned descriptions, and transcript/equation capture are private.
  Use the bundle or PCZT workflows for proof construction. The existing
  `InProgress<Unproven, _>::create_proof` accepts semantic instances.
- Use `SpendAuthRandomizer` in public key randomization and PCZT getters. It
  owns canonical `from_bytes`/`to_bytes` and `corez::io` `read`/`write` codecs.
  Signature domains, keys, signatures, and errors belong to Orchard.
- Handle `circuit::ProofError` in proof operations, builder errors, and PCZT
  errors. Its categories describe input, statement, witness, proof,
  randomness, and internal failures without exposing implementation types.
- Raw arithmetic conversion traits and scalar test generators are private;
  use the semantic testing strategies for their domain types.

Canonical protocol encodings and verifying-key fingerprints are preserved.
Historical proofs remain verifiable. Bare verification consumes the historical
proof prefix; modern bundle constructors enforce exact proof length, while
historical bundles preserve suffix bytes for serialization and hashing.

## Validation

Run the capability and consumer matrix and the separate-process proof fixture
exchange with:

```sh
python3 .github/scripts/check_orchard_backends.py
```

The harness discovers the available implementation selectors from Cargo
metadata. Use `test-dependencies` for the full internal test suite. The optional
`orchard-legacy` support crate holds implementation dependencies; applications
should depend on Orchard's public API.

The private table generator remains an ignored maintenance test:

```sh
ORCHARD_LAGRANGE_OUTPUT=/tmp/lagrange_coeffs.rs cargo test --release \
  -p zakura-orchard --features test-dependencies \
  generate_lagrange_coeffs -- --ignored --nocapture
```
