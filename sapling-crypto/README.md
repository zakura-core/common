# zakura-sapling-crypto

`zakura-sapling-crypto` is the [Zakura](https://github.com/zakura-core/zakura)
fork of the upstream
[`sapling-crypto`](https://crates.io/crates/sapling-crypto) crate from
[zcash/sapling-crypto](https://github.com/zcash/sapling-crypto), maintained in
[zakura-core/libraries](https://github.com/zakura-core/libraries). The library
target keeps the upstream name, so `use sapling_crypto::…` paths are unchanged.
Use it as a drop-in replacement by renaming the dependency:

```toml
[dependencies]
sapling-crypto = { package = "zakura-sapling-crypto", version = "0.7" }
```

This crate contains an implementation of Zcash's "Sapling" cryptography.

## Sapling Pedersen hashing

The optional `fused-pedersen` feature caches fused chunk-block lookup tables
(about 6.2 MiB) to speed up non-circuit Pedersen hashing.
It is opt-in so that full-node applications can enable the higher-throughput
evaluator, while wallets and other memory-sensitive applications keep the
original 8-bit exp-window tables by default. Enable it on the dependency with
`features = ["fused-pedersen"]`.

Both evaluators return the same prime-order point; only the lookup tables and
online arithmetic differ.

## `no_std` compatibility

In order to take advantage of `no_std` builds, downstream users of this crate
must enable:

* the `spin_no_std` feature of the `lazy_static` crate; and

This is needed because the `--no-default-features` builds of these crates still
rely on `std`.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
