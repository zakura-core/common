# `zakura-core/common` <img src="https://zakura.com/zakura-flower-v1.svg" alt="Zakura logo" height="32">

This repository contains the Zakura Common libraries: the foundational Rust crates used in [Zakura](https://github.com/zakura-core/zakura) and made available for the Zcash ecosystem. Use this stack in your wallets or in other tools for better performance.

## Transactions and keys

- [`zakura-primitives`](crates/zcash_primitives) (forked from [`zcash_primitives 0.30.0`](https://github.com/zcash/librustzcash/tree/57b844dc00bf1f25254b5859b8d5faa8e5730f98/zcash_primitives))
- [`zakura-keys`](crates/zcash_keys) (forked from [`zcash_keys 0.16.1`](https://github.com/zcash/librustzcash/tree/cb356a7def26d0bd8e1f21709951aeea137f58fa/zcash_keys))

## Chain history

- [`zakura-history`](crates/zcash_history) (forked from [`zcash_history 0.6.0`](https://github.com/zcash/librustzcash/tree/b74429f9e4e3600c27492f1d936fb3b9c818c224/zcash_history))

## Shielded protocols

- [`zakura-orchard`](crates/orchard) (forked from [`orchard 0.15.5`](https://github.com/zcash/orchard/tree/29d1d55db62153dcaeef8ef631c8991c53ed1248))
- [`zakura-sapling-crypto`](crates/sapling-crypto) (forked from [`sapling-crypto 0.7.0`](https://github.com/zcash/sapling-crypto/tree/8186b407b47b595a2ea4f04c73d59fdd83bd401f))
- [`zakura-proofs`](crates/zcash_proofs) (forked from [`zcash_proofs 0.30.0`](https://github.com/zcash/librustzcash/tree/57b844dc00bf1f25254b5859b8d5faa8e5730f98/zcash_proofs))

## The halo2 proving system

- [`zakura-halo2-proofs`](crates/halo2_proofs) (forked from [`halo2_proofs 0.3.5`](https://github.com/zcash/halo2/tree/8e22adbdce480e5db7625df56aff9c2c8ca79f8f/halo2_proofs))
- [`zakura-halo2-gadgets`](crates/halo2_gadgets) (forked from [`halo2_gadgets 0.5.0`](https://github.com/zcash/halo2/tree/d751768afe0d2105b349dd93f73fde7f2eade088/halo2_gadgets))
- [`zakura-halo2-poseidon`](crates/halo2_poseidon) (forked from [`halo2_poseidon 0.1.0`](https://github.com/zcash/halo2/tree/f066ace1f234d7fe1908851ed86b1801e0b1ffea/halo2_poseidon))
- [`zakura-halo2-legacy-pdqsort`](crates/halo2_legacy_pdqsort) (forked from [`halo2_legacy_pdqsort 0.1.0`](https://github.com/zcash/halo2_legacy_pdqsort/tree/c3b69083adcc5ab63d02ffbbc716ee19bdcdc81f))

## Curves, hashes, and signatures

- [`zakura-pairing`](crates/pairing) (forked from [`pairing 0.23.0`](https://github.com/zkcrypto/pairing/tree/11eff5b3680a08b09c61cbe75eaa803a1e85d80b))
- [`zakura-bls12-381`](crates/bls12_381) (forked from [`bls12_381 0.8.0`](https://github.com/zkcrypto/bls12_381/tree/7de7b9d9c509b9973b35a3241b74bbbea95e700a))
- [`zakura-jubjub`](crates/jubjub) (forked from [`jubjub 0.10.0`](https://github.com/zkcrypto/jubjub/tree/47dfe5181ccf39166c0c479c35c0644d708f4294))
- [`zakura-bellman`](crates/bellman) (forked from [`bellman 0.14.0`](https://github.com/zkcrypto/bellman/tree/e137775023a647716793a362ace008e058679b2a))
- [`zakura-pasta-curves`](crates/pasta_curves) (forked from [`pasta_curves 0.5.2`](https://github.com/zcash/pasta_curves/tree/c41c5149d8e6deebada48afa5ed8fadce3ff875c))
- [`zakura-sinsemilla`](crates/sinsemilla) (forked from [`sinsemilla 0.1.0`](https://github.com/zcash/sinsemilla/tree/206f7a960c55222a138a85447f1ddc666822cac0))
- [`zakura-reddsa`](crates/reddsa) (forked from [`reddsa 0.5.2`](https://github.com/ZcashFoundation/reddsa/tree/3792daa95e588c1af6bd4805105bfb6ea7e9ad49))
- [`zakura-redjubjub`](crates/redjubjub) (forked from [`redjubjub 0.8.0`](https://github.com/ZcashFoundation/redjubjub/tree/2f618e9b47617ae9d4112913391a5c3fbb8106f0))

`zakura-redjubjub` is a thin wrapper over `zakura-reddsa`, so the two are maintained together.

## License

All code in this repository is licensed under either of

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
  [apache.org/licenses/LICENSE-2.0](http://www.apache.org/licenses/LICENSE-2.0))
- MIT license ([LICENSE-MIT](LICENSE-MIT) or
  [opensource.org/licenses/MIT](http://opensource.org/licenses/MIT))

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
