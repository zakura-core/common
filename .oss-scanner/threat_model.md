# Threat model for the OSS Scanner

This repository holds the Zakura Common libraries: Zakura's forks of the Zcash
ecosystem's cryptography and protocol crates (halo2, Orchard, Sapling,
`pasta_curves`, `bls12_381`, `jubjub`, `bellman`, RedDSA, Equihash, note
encryption, transaction and address encoding, ZIP 321), plus two unpublished
experimental members: `zakura-udon` (Pasta field and curve arithmetic with
allocation-free FFTs, not yet used by Zakura) and the `zakura-bento*` crates
(compile-time arithmetic that derives Udon's constants). The library crates
are published to crates.io. Their most important consumer is the
[Zakura](https://github.com/zakura-core/zakura) full node, which uses them to
verify every proof, signature, Equihash solution and transaction on the Zcash
chain. Wallets and other Zcash tools use them too.
The repository's security policy is
[`.github/SECURITY.md`](../.github/SECURITY.md).

## Where untrusted input enters

Everything that comes from the blockchain or the network is attacker-chosen:

- **Proofs** given to the halo2 verifier (`zakura-halo2-proofs`), the Groth16
  verifier (`zakura-bellman`), and the Orchard and Sapling verification APIs
  built on them (`zakura-orchard`, `zakura-sapling-crypto`, `zakura-proofs`).
- **Encoded group elements and field elements**: every `from_bytes`,
  `from_repr` or point decompression in `zakura-pasta-curves`,
  `zakura-bls12-381`, `zakura-jubjub` and `zakura-udon`, and the value
  commitments, nullifiers, anchors and keys built from them.
- **Signatures** verified by `zakura-reddsa`, `zakura-redjubjub` and
  `zakura-reddsa-frost`, and the messages and public keys they are checked
  against.
- **Equihash solutions** in block headers, checked by `zakura-equihash`.
- **Serialized transactions, scripts, addresses and payment URIs** parsed by
  `zakura-primitives`, `zakura-transparent`, `zakura-protocol`,
  `zakura-address`, `zakura-keys` and `zakura-zip321`.
- **Note ciphertexts** that wallets trial-decrypt with `zakura-note-encryption`
  and the Orchard and Sapling note encryption built on it.

Trusted: the caller's own keys and randomness, circuit descriptions written
by the caller, and documented preconditions on arguments.

## What matters most

1. **Soundness and completeness of verification as Zakura uses it.** The
   Orchard Action circuit and its verifier, the Sapling Spend and Output
   circuits and the Groth16 verifier, the Orchard signature hash, RedPallas
   and RedJubjub signature verification, and Equihash verification. Accepting
   an invalid proof, signature or solution lets money be counterfeited or
   stolen; rejecting a valid one splits the chain for every node running
   Zakura. Both are critical. The verifier in
   [`valargroup/voting-circuits`](https://github.com/valargroup/voting-circuits)
   is the other verifier whose soundness is in scope.
2. **Arithmetic.** Field and curve operations in `zakura-pasta-curves`,
   `zakura-bls12-381`, `zakura-jubjub`, `zakura-udon` and the polynomial and
   multi-scalar code in `zakura-halo2-proofs` and `zakura-bellman`. A wrong
   result for any input, including non-canonical encodings, points not on the
   curve or not in the prime-order subgroup, and the identity, is a consensus
   bug upstream of everything else. The `x86_64-asm` paths in
   `zakura-pasta-curves` and `zakura-udon` must agree with the portable code.
3. **Decoding.** Parsers that panic, loop, or allocate without bound on
   malformed input let a peer attack any node or wallet that uses them.
4. **Secret-key operations in wallets.** Signing, key derivation, note
   decryption and the FROST protocol in `zakura-reddsa-frost` must not leak
   secrets through their outputs or through secret-dependent timing or
   memory access, and signing must never reuse a nonce.

`zakura-udon` and the `zakura-bento*` crates matter less until Zakura uses
them. A bug in `bento`'s compile-time arithmetic would surface as a wrong
constant in Udon, so test it through Udon's vectors.

Less important: proving performance, `no_std` and bare-metal build
configurations, benchmarks, the `dev-graph`, `test-dependencies` and
`cost-estimator` development features, and examples. Code that only runs in
tests is out of scope.

## How to exercise it

- The image compiled the test binaries of every crate in the configurations
  CI uses; `.oss-scanner/Dockerfile` lists the exact `cargo test` arguments
  for each group. Reuse them, or the group recompiles. `CARGO_NET_OFFLINE`
  keeps Cargo off the network.
- Proof-system tests are slow in the test profile; CI runs the halo2 crates
  with `--release`, as the Dockerfile does. `Cargo.toml` already optimizes
  the arithmetic crates in the test profile.
- Test vectors from the Zcash specification and from `zcashd` are under
  `src/test_vectors` in `orchard`, `sapling-crypto`, `equihash` and
  `zcash_transparent`; other crates embed theirs in their test modules.
  Equality with them, and with the upstream crates each one was forked from
  (see `README.md`), is the oracle for arithmetic and encoding bugs.
- `zakura-orchard`'s `tests/builder.rs` (`bundle_chain`) builds a bundle,
  proves it and verifies it; it is the quickest way to confirm a
  verification finding. `zakura-sapling-crypto` tests its Spend and Output
  circuits in `src/circuit.rs`.

## How we rate severity

- **Critical:** a verifier accepts an invalid proof, signature or Equihash
  solution, or rejects a valid one; wrong field, curve, hash or commitment
  arithmetic reachable from chain data; recovery of a spending or signing key;
  nonce reuse in signing.
- **High:** a panic, unbounded allocation, or non-terminating loop on
  attacker-supplied bytes in a decoder or verifier; a non-canonical encoding
  accepted where the protocol requires canonical bytes; a secret-dependent
  timing or memory-access pattern in signing, key derivation or decryption
  with a demonstrated leak.
- **Medium:** a theoretical side channel without a demonstrated leak;
  incorrect results on inputs that violate a documented precondition but are
  cheap for a caller to pass by mistake; API that makes a secure use harder
  than an insecure one.
- **Low:** issues in tests, benchmarks, examples, development-only features
  and documentation; performance.

## Leave alone

As `.github/SECURITY.md` says: the ability to write a malformed,
underconstrained or otherwise insecure circuit with the halo2 API is not a
vulnerability here, and neither are example circuits, downstream circuits
other than Orchard as Zakura uses it and the voting-circuits verifier, misuse
of an API, or violation of a documented precondition, unless one of them
leads to one of the impacts above. The upstream crates each fork came from
are maintained by their own projects; a bug that is also present upstream is
still in scope here, and we would like to know so we can coordinate.

## Reports and patches

A report is most useful with a failing test we can run offline: the concrete
input, the function it is given to, the wrong output or crash, and which
specification clause, protocol rule or documented invariant it violates. For
soundness findings, show the invalid proof, signature or solution that is
accepted, or the valid one that is rejected. A patch should be a diff against
`main` that keeps the existing tests and vectors passing and adds the failing
case as a test.
