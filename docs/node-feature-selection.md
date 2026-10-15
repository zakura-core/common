# Selecting features for standard and no_std clients

The Common crates that serialize data select their I/O types through their
`std` feature. Standard builds use `std::io` directly and do not activate the
optional `corez` dependency. This preserves the standard-library I/O types and
serialization format.

Clients that disable default features and need a build without the standard
library must enable `no-std-io` on each directly consumed serialization crate.
The feature forwards the selection through that crate's Common dependencies.
For example:

```toml
zcash_protocol = { package = "zakura-protocol", version = "3", default-features = false, features = ["no-std-io"] }
```

The affected crates are `zakura-equihash`, `zakura-address`, `zakura-keys`,
`zakura-primitives`, `zakura-protocol`, `zakura-transparent`,
`zakura-sapling-crypto`, and `zakura-orchard`.

Enabling both features is supported: `std::io` takes precedence, and Cargo may
still compile the explicitly requested optional `corez` dependency. Consumers
seeking to exclude `corez` should enable `std` without `no-std-io` throughout
their dependency graph. The circuit implementations require the standard
library; `zakura-primitives/circuits` therefore implies `std` explicitly.
