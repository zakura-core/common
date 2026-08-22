This crate, `zakura-pairing`, is the Zakura fork of upstream
[`pairing`](https://crates.io/crates/pairing), maintained in
[`zakura-core/libraries`](https://github.com/zakura-core/libraries). The library
target remains `pairing`, so source imports are unchanged. Use it as a drop-in
replacement by renaming the dependency:

```toml
[dependencies]
pairing = { package = "zakura-pairing", version = "1.0.0-rc.3" }
```

# pairing

`pairing` is a crate for using pairing-friendly elliptic curves.

`pairing` provides basic traits for pairing-friendly elliptic curve constructions.
Specific curves are implemented in separate crates:

- [`bls12_381`](https://crates.io/crates/bls12_381) - the BLS12-381 curve.

## [Documentation](https://docs.rs/pairing/)

Bring the `pairing` crate into your project just as you normally would.

## Security Warnings

This library does not make any guarantees about constant-time operations, memory
access patterns, or resistance to side-channel attacks.

## Minimum Supported Rust Version

Requires Rust **1.88** or higher.

Minimum supported Rust version can be changed in the future, but it will be done with a
minor version bump.

## License

Licensed under either of

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
