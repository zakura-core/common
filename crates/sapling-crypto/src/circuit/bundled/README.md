# Sapling verification keys

These are the Groth16 verification-key prefixes of the canonical Sapling
parameter files. They contain no proving-query points. The
`pinned-vk-only` feature loads only these keys for Sapling proof
verification. It adds no dependency on `zakura-proofs` or any Wagyu parameter
package. It does not disable proving features enabled independently elsewhere;
a verification-only consumer must omit `zakura-proofs/bundled-prover`.

The files were extracted from `wagyu-zcash-parameters` 0.2.0, previously bundled
by `zakura-proofs` 2.2.0. Before extraction, the reconstructed parameter files
were checked against the BLAKE2b-512 hashes in that version's
[`zcash_proofs::parse_parameters`](https://github.com/zakura-core/common/blob/v2.2.0/crates/zcash_proofs/src/lib.rs).
The spend file concatenates the five `sapling-spend-N.params` segments from
`wagyu-zcash-parameters-1` through `-5`. The output file is
`sapling-output-1.params` from `wagyu-zcash-parameters-6`.

The Bellman encoding begins with six uncompressed group elements: three G1
elements of 96 bytes each and three G2 elements of 192 bytes each. At byte 864,
a four-byte big-endian length precedes the public-input G1 elements. Extract
the first `868 + 96 * length` bytes. The spend key has eight public-input
elements, and the output key has six.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `spend.vk` | 1,636 | `e0e847a3937ce78989e3416e908439a1d853287863645095d5e2bbadeeec9869` |
| `output.vk` | 1,444 | `d7a655f6f58745f17bf5344682d25d15967e39b575d072335e14ace0a871bd0c` |

`pinned_verifying_keys()` uses the checked verification-key readers and
initializes both keys once. The shared keys retain their batch-verification
precomputations across calls. No parameter reader or proving-query vectors are
needed.
