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

## Optional memory accounting

The default-enabled `memory-usage` feature provides the `memuse::DynamicUsage`
implementations and forwards the necessary accounting support through Common.
Clients that disable defaults and use those traits must select it explicitly.
`std` alone does not select memory accounting or `group/wnaf-memuse`.

To exclude the external `memuse` package, node clients must omit both memory
accounting and wallet derivation throughout the graph. The external ZIP 32
crate itself depends on `memuse`, so omitting accounting alone does not prove a
package reduction when wallet derivation is still enabled. Default wallet
builds retain both capabilities.
