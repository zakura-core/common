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

## Wallet derivation and coinbase construction

The `zip32` feature is enabled by default in Orchard, Sapling, transparent keys,
key management, and transaction primitives. It preserves the existing wallet
APIs, including PCZT construction. Indexed-address and wallet-input features
imply it. Clients selecting features explicitly must enable `zip32` for those
APIs.

Nodes that verify transactions and build coinbase rewards can use primitives
with `default-features = false` and `std,circuits,multicore`, and the other
Common crates with their required standard and verification features. The
`Builder::build_coinbase` entry point accepts no wallet spending keys or fee
rule. It enforces coinbase configuration and shares version, expiry, proof,
signature, and serialization code with the default wallet builder.

With `zip32` enabled, Orchard's `keys::Scope` remains the re-exported ZIP 32
type. Without it, the same receiving/change variants use an Orchard-owned
scope type and carry no dependency on wallet derivation.

## Memory accounting

The Common crates do not implement `memuse::DynamicUsage` and have no
memory-accounting feature. They do not depend on `memuse` or select
`group/wnaf-memuse`. Clients that measured Common types with that trait must
estimate those sizes themselves.

The external ZIP 32 crate depends on `memuse`, so builds that enable `zip32`
still contain the package. Node clients that omit wallet derivation throughout
the graph do not need it for Common.
