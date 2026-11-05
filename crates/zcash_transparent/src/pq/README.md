# Versioned PQ transparent outputs

The optional `pq` feature provides SLH-DSA transparent spends behind a versioned output
type. The version is a byte of the output itself, so an output's format is visible on
chain when the payment is made rather than when the receiver spends. These library APIs
activate no consensus rule and define no address format.

## Encoding

An output is exactly `50 01 vv 14 <commitment>`, 24 bytes:
`OP_RESERVED PUSH1(version) PUSH20(commitment)`. The commitment is `HASH160(body)`, where
the body is an ordinary transparent script and carries no header of its own. A spending
input is push-only, pushes the body last, and pushes the body's arguments before it. All of
the body executes, and every signature operation receives those same bytes as its signing
script.

The version appears once, in the output. An earlier draft repeated it inside the committed
script so the commitment would cover it too; that cost three bytes in every spend and a
rule that the two copies agree, to bind something the signing context and the v5 digest
already bind. What it gave up by removing it: the committed bytes no longer begin with
`OP_RESERVED`, so they are not self-describing, and the same twenty bytes can appear in an
output of either version or as an ordinary P2SH script hash. Those are separate outputs,
separately funded, and each is spent only by the rules its own output selects, so nothing
crosses between them — a signature made for one cannot authorize another, because the
context names the version and the v5 digest covers the whole previous output.

`OP_RESERVED` is the namespace and the version is the discriminator; there is no separate
tag, because nothing in validation would read one. Every other script template in this
layer is terse in the same way — P2SH is `a9 14 <hash> 87` — and a human-readable marker
belongs in the address encoding, where people see it, rather than in `scriptPubKey` bytes.
Writing the version as a push rather than a bare byte keeps the whole output a well-formed
sequence of pushes, so existing tools that walk a script read it cleanly.

| Version | Parameter set | Public key | Signature | Commitment | Pure signing context |
| --- | --- | --- | --- | --- | --- |
| 1 | SLH-DSA-SHA2-128f | 32 bytes | 17,088 bytes | `HASH160(body)` | `ZCASH/PQ/OUT/<network>` + `01` |
| 2 | SLH-DSA-SHA2-192s | 48 bytes | 16,224 bytes | `HASH160(body)` | `ZCASH/PQ/OUT/<network>` + `02` |

`<network>` is `main`, `test` or `regtest`. Consensus branch identifiers are scoped to a
network upgrade rather than to a network, so no transaction digest separates mainnet from
testnet; the context does. A signature argument appends one strict transparent sighash
selector: ALL, NONE, SINGLE, or any of those with ANYONECANPAY. The caller supplies the
existing transaction signature digest; Pure SLH-DSA signs those 32 bytes with the
version's context, and there is no additional application hash.

The version is the lever for replacing any of this: it selects the parameter set, the
signing context and the commitment, so a later version can use a 32-byte hash by adding a
row to this table and the length it implies. Versions and parameter sets are one to one in
the table as it stands, and the code relies on that: a parameter set stands in for a version
where that is convenient. Adding the row above is exactly the change that ends it, since a
new commitment with an existing signature scheme means two versions sharing one parameter
set. That row must also carry the version byte through `PqOutput` and key the signing
context on it, or the two versions would share a context. HASH160 is kept for now, and is the weakest
part of the format: it offers roughly 80-bit collision resistance, well below the signature
scheme's category, and an alternative script with the same hash spends the output.

Because the body carries no version, nothing in it says which parameter set may spend it.
The output decides, and the two parameter sets have different key lengths, so a body
written for one is unspendable under the other.

## Rules

Two rules apply at different times, and both are the caller's to enforce.

**When an output is created.** `output::classify_created_output` returns `Pq` for a
canonical output of a defined version, `Malformed` for anything else whose first byte is
`OP_RESERVED`, and `Legacy` for every other output. A node activating this format rejects
a transaction containing a `Malformed` output, so a wallet that applies the rules
incorrectly has its payment rejected while the sender still holds the coins. Unknown
versions are rejected at creation too: this format is deliberately not forward-compatible
in the way an anyone-can-spend reserved program would be.

Because the version is in the output, a node can also reject transactions that create
`Legacy` outputs from a chosen height, which is the whole reason the version lives here.
Choosing that height and its exemptions is a consensus decision outside this crate. At
minimum, coinbase outputs, whose recipients consensus fixes, and null-data outputs, which
are unspendable by design, need exempting; ZIP 320 (TEX) addresses are P2PKH hashes and
become unpayable, so that rule cannot ship before recipients accept a PQ output.

That ban applies to the outputs a transaction creates, never to outputs already in the
UTXO set. Coins paid to a legacy output before the ban stay spendable afterwards, under
exactly the rules that spend them today; the only consequence for their owner is that the
transaction spending them must pay to a PQ output.

**When an output is spent.** `output::parse_output` recognizes a PQ output, and
`PqOutput::verify_spend` requires the last pushed script to match that output's commitment,
then executes it under the version's parameter set and context.
Unknown versions, non-canonical outputs and failed authentication reject; nothing falls
back to ECDSA, and no script argument can select or weaken the verifier. Spendability does
not depend on the height at which the output was created.

Every signature check in a PQ body is SLH-DSA. The checker requires a public key of
exactly the version's length and aborts on anything else, so one body cannot mix
algorithms: "my PQ key, or my existing ECDSA key after a timelock" is a script that parses
and then kills the spend when that branch is taken. That is the intent — an adversary who
can forge ECDSA must have no path to the coins, which is also why no script argument can
select a verifier — but it costs the usual migration and recovery shape, which a legacy
P2SH script can express. Build a recovery path from several SLH-DSA keys instead. The same
check blocks the opposite shape too, a body requiring an SLH-DSA *and* an ECDSA signature,
which would be stronger than either alone; that one falls out of the rule rather than
having been weighed on its own.

PQ execution rules are fixed rather than flag-driven: `CHECKLOCKTIMEVERIFY` is always
enforced, every input push must use its shortest encoding, and execution must end with
exactly one stack item. The last two deny a third party cheap edits to someone else's
spend, since ZIP 244 leaves the serialized input out of the transaction identifier. There
are no interpreter flags to pass: this module verifies PQ outputs and nothing else, so
every other output keeps the evaluator, flags and limits the caller already applies to it.

Transaction version: these spends assume v5 or later, whose digest commits to the previous
output and therefore directly to the version and the commitment. A v4 digest commits only
to the script code it is handed, and not to the other inputs' outputs and amounts.

## Resource rules

The committed body is limited to 10,000 bytes, as any script is. Serialized input
arguments are limited to 512 KiB with at most 17,089 payload bytes per push. The main and
alternate stacks together retain the 1,000-item limit and additionally have a 1 MiB
payload limit, checked initially and after each instruction. The 20-key multisig and
201-operation limits are unchanged, including the charge for each key before multisig
matching.

Count signature operations with `PqSpend::sig_op_count`, over the committed body. Do not
count them over the serialized input: its signature pushes exceed the legacy push bound,
where legacy counting stops and would report almost none of the checks the body performs.
One SLH-DSA check costs far more than one ECDSA check, and that count does not distinguish
them, so a block budget must weight them separately. These bounds describe this
prototype's behavior; acceptable block verification time, memory use, relay policy and
fees still need qualification, and ZIP 317 currently has no rule that fits a 17 kB input.

## Security argument and limits

The output commits to the algorithm, the exact key and signature encodings, and the
committed body. Per-version, per-network contexts separate these signatures from other
protocols, versions and networks. Malformed nonempty signatures, public keys and selectors
abort; an empty signature with a correctly sized key, and a cryptographically incorrect
signature, evaluate false.

`OP_RESERVED` makes the output fail under legacy execution, so a PQ output is unspendable,
never claimable, wherever these rules are not active — including before activation and on
a node that has not upgraded.

What the marker does not do: it says nothing about the body, which stays hidden behind the
commitment until the spend. A body of `OP_TRUE` is anyone-can-spend, a body whose key is
the wrong length is unspendable, and a body of ordinary ECDSA operations is unspendable
here. No output rule can detect any of these when the payment is made, and only an output
type carrying its body in the clear could. Behind a commitment, body correctness remains
the receiver's responsibility.

The standardized signature's security category is not a claim about the whole transaction
system. Existing transaction hashes, alternative branches, ordinary ECDSA operations, the
HASH160 commitment, caller validation and private-key custody all still constrain the
composed system, and a branch that permits a weaker authorization remains weaker. The
digest callback is a security boundary: a valid signature authorizes the digest it returns,
so the caller must supply the authentic previous output and amount and must reject invalid
transaction structure, including SINGLE without a corresponding output, before returning
one.

Independent NIST key-generation and OpenSSL signature fixtures are documented in
`test_vectors/README.md`. Dependency review, network activation, node admission, address
encoding, wallet derivation, signing-device support, a fee rule and production resource
qualification all remain outside this library change.
