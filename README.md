# zakura-libraries

This workspace contains libraries used in [zakura](https://github.com/zakura-core/zakura), originally forked from the ZCash proving stack and librustzcash, for maintenance and further development by the Zakura project. Zakura never pull in any of the originally-forked dependencies.

## From librustzcash

The [librustzcash](https://github.com/zcash/librustzcash) members consumed by Zakura:

- `equihash` — proof-of-work verification and an optional Tromp CPU solver
- `zcash_primitives` — transaction structure, builders, txids, and sighashes
- `zcash_keys` — key derivation and address encoding
- `zcash_proofs` — the Sapling Groth16 prover and proving-parameter handling

## Core Crypto Libraries

- `pasta_curves` — the Pallas/Vesta curve cycle underlying Orchard and halo2
- `sinsemilla` — the Sinsemilla hash function (Pallas-based)
- `reddsa` — RedDSA signatures: RedPallas (Orchard) and RedJubjub (Sapling)

## The Orchard Proving Stack

- `halo2_proofs` — the halo2 proving system
- `halo2_gadgets` — circuit gadgets built on halo2_proofs
- `halo2_poseidon` — the Poseidon hash gadget
- `halo2_legacy_pdqsort` — pinned sort behavior for the legacy V1 floor planner
- `orchard` — the Orchard shielded protocol and circuit

## The Sapling Proving Stack

Due to Sapling's redjubjub crate being a wrapper around reddsa, these crates also had to be forked:

- `redjubjub` — RedJubjub signature wrapper over reddsa
- `sapling-crypto` — the Sapling shielded protocol
