# Pinned Orchard prover outputs

These files pin the one- and two-Action PostNu6_3 executions checked by the
Ironwood Lean prover replay. The `.proof` files contain the complete serialized
proof bytes. Each `.rng-u64s-le` file contains the ordered `next_u64` outputs,
encoded as little-endian words, supplied during that proof call. Witness inputs
are constructed by `build_unproven_fixture_bundle` using the existing public
single-Action and two-Action seeds.

The bytes were extracted without regeneration from `capturedProof` and the
`.rng64` entries of `capturedEvents` in these pinned fixtures:

- [SingleAction.lean](https://github.com/zakura-core/ironwood-formal-verification/blob/6e36616dda3a49bfe504e9c1364a7f49a8cd41e5/Zcash/Snark/Fixtures/Prover/SingleAction.lean)
- [MultiAction.lean](https://github.com/zakura-core/ironwood-formal-verification/blob/6e36616dda3a49bfe504e9c1364a7f49a8cd41e5/Zcash/Snark/Fixtures/Prover/MultiAction.lean)

Their authenticated Common producer is
`51a7364f3d1b86fd5a0be4653e8f412d1a90c453`. The complete tape sizes are 1,552 and
2,736 words; the corresponding proofs contain 4,992 and 7,264 bytes.

The gated `circuit::prover_fingerprint` tests replay each tape, require its exact
consumption and RNG call method, and compare the production Orchard prover's
output with the committed proof bytes. They also retain the recorded/uncaptured
proof and RNG-position comparison. Common CI runs these tests with one Rayon
worker and with the serial prover. Run them locally with:

```sh
RAYON_NUM_THREADS=1 cargo test --locked --release -p zakura-orchard \
  --features prover-fingerprint --lib circuit::prover_fingerprint::
```

Exporting Lean fixtures never updates these expectations. A mismatch requires
review of the prover change and its correspondence with the Lean model before
changing these files and the independently pinned Ironwood fixtures together.
These finite executions detect changes to the selected proofs and blinding
schedule; they do not establish distributional equivalence for every input.
