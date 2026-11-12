# Native SLH-DSA transparent scripts

The optional `pq` feature provides native outputs whose bodies use the existing
transparent script language. Public keys appear directly in the output body.
These library APIs do not activate consensus rules or provide an address format.

## Encoding and verification

An output is exactly `50 03 53 4c 48 01 vv <body>`:
`OP_RESERVED PUSH3("SLH") PUSH1(version) <body>`. The header is interpreted by
`native::parse_output`, not executed. All signature operations receive the complete
original output as their signing script. An unrelated output returns `None`;
recognized malformed headers and unsupported versions return errors.

| Version | Parameter set | Public key | Signature | Pure signing context |
| --- | --- | --- | --- | --- |
| 1 | SLH-DSA-SHA2-128f | 32 bytes | 17,088 bytes | `ZCASH/PQ/NATIVE` followed by `01` |
| 2 | SLH-DSA-SHA2-192s | 48 bytes | 16,224 bytes | `ZCASH/PQ/NATIVE` followed by `02` |

Every PQ key in an output uses that output's parameter set. Separate inputs in a
transaction may spend different versions. A signature argument appends one strict
transparent sighash selector: ALL, NONE, SINGLE, or any of those with ANYONECANPAY.
The caller supplies the existing transaction signature digest. Pure SLH-DSA signs
those 32 bytes with the version's context; there is no additional application hash.

| Byte | Operation |
| --- | --- |
| `ba` | `OP_CHECKSIG_PQ` |
| `bb` | `OP_CHECKSIGVERIFY_PQ` |
| `bc` | `OP_CHECKMULTISIG_PQ` |
| `bd` | `OP_CHECKMULTISIGVERIFY_PQ` |

The interpreter shares the ordinary signature operations' stack behavior,
multisig matching order, dummy argument, and VERIFY behavior. Ordinary ECDSA
operations still check ECDSA signatures. Branches and absolute timelocks use the
existing interpreter; CHECKLOCKTIMEVERIFY is always enforced in native execution.
Minimal-data, null-dummy and clean-stack flags remain caller choices.

A single-key output body is `<public key> OP_CHECKSIG_PQ`. A threshold body is
`2 <key A> <key B> <key C> 3 OP_CHECKMULTISIG_PQ`; its arguments are the empty dummy
and two signatures in matching key order. Timelock recovery can use
`IF <normal key> CHECKSIG_PQ ELSE <deadline> CHECKLOCKTIMEVERIFY DROP <recovery key>
CHECKSIG_PQ ENDIF` with a signature and branch selector in the input.

## API boundaries and trust requirements

`sha2_128f` and `sha2_192s` expose seeded signing and exact-encoding verification.
`native` constructs and parses outputs and combines the selected version with the
private transaction checker. `zcash_script::pq` provides bounded push-only argument
decoding and invokes the shared interpreter; it does not choose a cryptographic
algorithm or authenticate an output.

The node must retrieve the actual previous output and amount, check network
activation, and supply a transaction checker bound to that same previous output.
It must reject invalid transaction structure, including SINGLE without a matching
output, before returning a digest. Parsing an output is not evidence of ownership
or activation. Never select the version from input arguments, signature length,
or a failed verification attempt. Never retry a rejected native spend as ECDSA.

The legacy evaluator rejects executed PQ operations before reading operands unless
trusted validation explicitly enables native rules. Inactive branches retain their
existing behavior. Legacy signature-operation accounting remains unchanged; callers
admitting native outputs must use `NativeOutput::sig_op_count`, which includes
both signature families and inactive branches.

## Resource rules

The complete output, including the header, is limited to 10,000 bytes. Serialized
input arguments are limited to 512 KiB, with at most 17,089 payload bytes per push.
The main and alternate stacks together retain the 1,000-item limit and additionally
have a 1 MiB payload limit checked initially and after each instruction. Input
arguments must be push-only. Script-body pushes retain ordinary interpreter limits.
The 20-key multisig and 201-operation limits are unchanged, including charges for
each key before multisig matching. There is no one-signature-attempt restriction.
Twenty SHA2-128f signatures fit within the input bound.

These bounds define this prototype's execution behavior. They do not establish
acceptable block verification time, memory use, relay policy, or fees. Node-level
admission and resource measurements remain required before activation.

## Security argument and limits

The output commits to the algorithm and its exact key/signature encodings. Fixed
version-specific contexts separate native signatures from other protocols and
versions. Malformed nonempty signatures, public keys and selectors abort; an empty
signature with a correctly sized key or an incorrect cryptographic signature
evaluates false. No alternative algorithm is attempted on failure.

The digest callback is a security boundary: a valid signature authorizes its
returned digest. Tests exercise all six selectors against actual v5 transaction
digests, including previous amounts, scripts, outpoints and branch identifiers.
ZIP 244 binds authenticated previous outputs rather than its `scriptCode` argument;
passing the correct script alone cannot compensate for incorrect previous-output
data. Other supported transaction versions retain their existing digest rules.

The standardized signature's security category is not a claim about the whole
transaction system. Existing transaction hashes, alternative branches, ordinary
ECDSA operations, caller validation and private-key custody still constrain the
composed system. A branch that permits a weaker authorization remains weaker.

Independent NIST key-generation and OpenSSL signature fixtures are documented in
`vectors/README.md`. Dependency review, node activation, address encoding, wallet
derivation, signing-device support and production resource qualification remain
outside this library change.
