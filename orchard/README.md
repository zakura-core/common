# zakura-orchard [![Crates.io](https://img.shields.io/crates/v/zakura-orchard.svg)](https://crates.io/crates/zakura-orchard) #

`zakura-orchard` is the [Zakura](https://github.com/zakura-core/zakura) fork of
the upstream [`orchard`](https://crates.io/crates/orchard) crate from
[zcash/orchard](https://github.com/zcash/orchard), maintained in
[zakura-core/libraries](https://github.com/zakura-core/libraries). The library
target keeps the upstream name, so `use orchard::…` paths are unchanged. Use it
as a drop-in replacement by renaming the dependency:

```toml
[dependencies]
orchard = { package = "zakura-orchard", version = "0.15" }
```

Requires Rust 1.88+.

## Documentation

- [The Orchard Book](https://zcash.github.io/orchard/)
- [Crate documentation](https://docs.rs/zakura-orchard)

## `no_std` compatibility

In order to take advantage of `no_std` builds, downstream users of this crate
must enable the `spin_no_std` feature of the `lazy_static` crate. This is
needed because the `--no-default-features` build of `lazy_static` still relies
on `std`.

## Orchard Merkle hashing ##

The optional `weighted-merkle` feature caches a roughly 4.88 MiB table to speed
up Orchard Merkle hashing. It is opt-in so that full-node applications can
enable the higher-throughput evaluator, while wallets and other
memory-sensitive applications use the generic fused Sinsemilla evaluator by
default. Enable it on the dependency with `features = ["weighted-merkle"]`.

## License

Copyright 2020-2023 The Electric Coin Company.

All code in this workspace is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
