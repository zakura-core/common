# Selecting features for node clients

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
