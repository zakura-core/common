# PQ transparent outputs

The optional `pq` feature provides SLH-DSA transparent spends behind a dedicated output
type. Its format and signature scheme are bytes of the output itself, so both are visible on
chain when the payment is made rather than when the receiver spends. These library APIs
activate no consensus rule and define no address format.

## Encoding

An output of the one format defined here is exactly `00 vv 20 <commitment>`, 35 bytes:
`OP_0 OP_<scheme> PUSH32(commitment)`. The commitment is `SHA-256(body)`, where the body is
an ordinary transparent script and carries no header of its own. A spending input is
push-only, pushes the body last, and pushes the body's arguments before it. All of the body
executes, and every signature operation receives those same bytes as its signing script.

The first two bytes are both opcodes rather than pushed data, so each costs one byte. That
is not economy for its own sake. A byte sitting loose in a script is not a field: the bytes
`0x01` through `0x4b` are push opcodes, and one in that position would swallow what follows
it and leave the commitment to be read as opcodes — which would also make the output's
signature-operation count depend on its hash bytes, since that count walks output scripts
opcode by opcode. `OP_0` and `OP_1` through `OP_16` are the only single bytes that denote a
small number without consuming what comes after, which is why SegWit spells witness versions
this way too, and which caps each of these bytes at seventeen or sixteen values.

Byte 0 names the **format** and byte 1 the **signature scheme** within it. Format 0 is the
only one defined here, and it fixes the commitment at a 32-byte `SHA-256`, so every output
defined by this document is 35 bytes. The two bytes are separate because they change for
different reasons: adding a signature scheme should not need a new format, and a format can
later change what the commitment *is* — a different hash, a different length — without
needing a second namespace.

The **namespace** is every script whose first byte is `0x00` or in `0x51`..`0x60`, whose
second byte is in `0x51`..`0x60`, and whose third byte is a direct push opcode
(`0x01`..`0x4b`) followed by exactly that many bytes and nothing more — so 4 to 78 bytes in
all. It deliberately claims far more than is defined, because a shape left outside it would
be spendable under the legacy rules and so could not be taken back later without a second
consensus change, while a shape inside it is refused from the start and stays available to
define. Everything inside it that format 0 does not define is **restricted**: a transaction
creating one is rejected and no spend of one is ever evaluated.

Anything outside the namespace — a second byte that is not a scheme opcode, a commitment
push that is not the shortest encoding of its payload, a trailing byte after the commitment —
is a legacy output and keeps the legacy rules. It is not a malformed PQ output, because
unlike under the previous marker those scripts really are spendable under those rules and may
already have an owner. A commitment *length* that format 0 does not fix is not one of those:
it is inside the namespace and restricted.

The format collides with nothing: Bitcoin's P2WSH is `OP_0 0x20 <32>` and Taproot is
`OP_1 0x20 <32>`, both 34 bytes with `0x20` as the second byte, so a 35-byte script whose
second byte is `0x51` matches no Bitcoin template and is shown as unknown rather than
mislabelled. Zcash has no witness programs, so no `OP_0`-led script is a standard template
here either. The other leading opcodes `OP_1`..`OP_16` are claimed as formats of this same
namespace rather than left free, which is what keeps a future format inside one set of rules
instead of needing a namespace of its own.

The two header bytes appear once, in the output. An earlier draft repeated them inside the
committed script so the commitment would cover them too; that cost three bytes in every spend and a
rule that the two copies agree, to bind something the signing context and the v5 digest
already bind. What it gave up by removing it: the committed bytes are not self-describing,
and the same thirty-two bytes can appear in an output of either scheme. Those are separate
outputs, separately funded, and each is spent only by the rules its own output selects, so
nothing crosses between them — a signature made for one cannot authorize another, because
the context names both bytes and the v5 digest covers the whole previous output.

Format 0, whose commitment is `SHA-256(body)`:

| Scheme | Parameter set | Public key | Signature | Commitment | Pure signing context |
| --- | --- | --- | --- | --- | --- |
| 1 | SLH-DSA-SHA2-128f | 32 bytes | 17,088 bytes | `SHA-256(body)` | `ZCASH/PQ/OUT/<network>` + `00 01` |
| 2 | SLH-DSA-SHA2-192s | 48 bytes | 16,224 bytes | `SHA-256(body)` | `ZCASH/PQ/OUT/<network>` + `00 02` |
| 3–16 | undefined | — | — | — | — |

The context's last two bytes are the format and the scheme. Both are there because scheme
numbering restarts in each format, so two formats will reuse scheme numbers; a context naming
only the scheme would let a signature made under one format verify under another.

`<network>` is `main`, `test` or `regtest`. Consensus branch identifiers are scoped to a
network upgrade rather than to a network, so no transaction digest separates mainnet from
testnet; the context does. A signature argument appends one strict transparent sighash
selector: ALL, NONE, SINGLE, or any of those with ANYONECANPAY. The caller supplies the
existing transaction signature digest; Pure SLH-DSA signs those 32 bytes with the
scheme's context, and there is no additional application hash.

These two bytes are the lever for replacing any of this: the scheme selects the parameter
set and the signing context, and the format selects the commitment and the lengths it
implies. Within format 0, schemes and parameter sets are one to one, and the code relies on
that: a parameter set stands in for a scheme where that is convenient. A second format, or a
scheme that reuses an existing parameter set under a new commitment, is exactly the change
that ends it. Such a row must carry both bytes through `PqOutput` and key the signing context
on both, or two schemes would share a context.

Because the body carries no header, nothing in it says which parameter set may spend it.
The output decides, and the two parameter sets have different key lengths, so a body
written for one is unspendable under the other.

## Rules

Two rules apply at different times, and both are the caller's to enforce.

**When an output is created.** `output::classify_created_output` returns `Pq` for an output
of a defined format and scheme, `Malformed` for a script in the namespace that format 0 does
not define — an undefined format, a commitment length format 0 does not fix, or an undefined
scheme within it — and `Legacy` for every other output, near misses of the namespace
included. A node activating this format rejects a transaction containing a `Malformed`
output, so neither a wallet nor a miner can mint one, and no such output can appear after
activation. This format is deliberately not
forward-compatible in the way an anyone-can-spend reserved program would be.

Legacy outputs stay creatable and spendable, for good. This format adds a namespace beside
them and bans nothing: an earlier draft used the marker's presence in the output to let a
node refuse to create legacy outputs from a chosen height, and that is no longer part of
it. Coins paid to a legacy output stay spendable under exactly the rules that spend them
today.

Everything the namespace claims and format 0 does not define — the other sixteen formats,
schemes 3 through 16, and every commitment length but 32 — is restricted in four places, so
none of them is a way in: a transaction creating one is rejected, such an output cannot be
spent, the legacy guard below covers the whole claimed shape rather than only what is
defined, and `ParameterSet` has no variant for an undefined scheme — the builder takes a
parameter set, not a script, so this library cannot construct one at all.

**When an output is spent.** `output::parse_output` recognizes a PQ output, and
`PqOutput::verify_spend` requires the last pushed script to match that output's commitment,
then executes it under the scheme's parameter set and context.
Undefined pairs and failed authentication reject; nothing falls back to ECDSA, and no
script argument can select or weaken the verifier. Spendability does not depend on the
height at which the output was created.

Every signature check in a PQ body is SLH-DSA. The checker requires a public key of
exactly the scheme's length and aborts on anything else, so one body cannot mix
algorithms: "my PQ key, or my existing ECDSA key after a timelock" is a script that parses
and then kills the spend when that branch is taken. That is the intent — an adversary who
can forge ECDSA must have no path to the coins, which is also why no script argument can
select a verifier — but it costs the usual migration and recovery shape, which a legacy
P2SH script can express. Build a recovery path from several SLH-DSA keys instead. The same
check blocks the opposite shape too, a body requiring an SLH-DSA *and* an ECDSA signature,
which would be stronger than either alone; that one falls out of the rule rather than
having been weighed on its own.

PQ execution rules are fixed rather than flag-driven: `CHECKLOCKTIMEVERIFY` is always
enforced, every input push must use its shortest encoding, the argument multisig consumes
without examining must be empty, and execution must end with exactly one stack item. The
last three deny a third party cheap edits to someone else's spend, since ZIP 244 leaves the
serialized input out of the transaction identifier. The shortest-encoding rule does not
cover the multisig argument on its own, because any padding put there is the shortest
encoding of its own payload and the item is discarded unexamined. There
are no interpreter flags to pass: this module verifies PQ outputs and nothing else, so
every other output keeps the evaluator, flags and limits the caller already applies to it.

Transaction version: these spends assume v5 or later, whose digest commits to the previous
output and therefore directly to both header bytes and the commitment. A v4 digest commits
only
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
committed body. Per-scheme, per-network contexts separate these signatures from other
protocols, formats and networks. Malformed nonempty signatures, public keys and selectors
abort; an empty signature with a correctly sized key, and a cryptographically incorrect
signature, evaluate false.

**A PQ output is claimable, not unspendable, wherever these rules are not active.** The
script is three pushes, so under legacy execution it leaves the truthy commitment on top of
the stack and is satisfied by an *empty* scriptSig: anyone takes the coins. This is the same
property that let SegWit ship as a soft fork, and it was accepted knowingly. `OP_RESERVED`,
which aborts legacy execution and would have made the output unspendable to any validator
lacking these rules, was considered and rejected for the marker: `OP_0` was chosen for the
SegWit idiom and because `OP_RESERVED` renders these outputs as invalid or burned in
script-aware tooling.

Three things carry the weight that marker would have carried, and none of them is optional:

1. `zcash_script`'s `Flags::PqOutputs`, which makes the legacy evaluator return
   `Error::PqNamespace` instead of running any script in the namespace — as a
   `scriptPubKey` and as a P2SH redeem script, for every shape it claims and not only the
   defined ones. It must be set
   uniformly once these rules activate; setting it for some inputs and not others makes the
   same output spendable or not depending on the verifier. It does not protect an
   implementation that does not use this crate, nor code that evaluates a script component
   directly rather than through a two-component entry point.
2. The restriction on everything in the namespace that format 0 does not define, described
   under Rules.
3. Policy before activation: a wallet built on this library must not create a PQ output
   until the rules are active, and relay policy should treat the whole namespace as
   nonstandard. Before activation there is no node anywhere with these rules, so a PQ
   output created early is claimable by anyone until then, and policy is all that stands in
   the way.

What the marker does not do: it says nothing about the body, which stays hidden behind the
commitment until the spend. A body of `OP_TRUE` is anyone-can-spend, a body whose key is
the wrong length is unspendable, and a body of ordinary ECDSA operations is unspendable
here. No output rule can detect any of these when the payment is made, and only an output
type carrying its body in the clear could. Behind a commitment, body correctness remains
the receiver's responsibility.

The standardized signature's security category is not a claim about the whole transaction
system. Existing transaction hashes, alternative branches, ordinary ECDSA operations, the
`SHA-256` commitment, caller validation and private-key custody all still constrain the
composed system, and a branch that permits a weaker authorization remains weaker. The
digest callback is a security boundary: a valid signature authorizes the digest it returns,
so the caller must supply the authentic previous output and amount and must reject invalid
transaction structure, including SINGLE without a corresponding output, before returning
one.

Independent NIST key-generation and OpenSSL signature fixtures are documented in
`test_vectors/README.md`. Dependency review, network activation, node admission, address
encoding, wallet derivation, signing-device support, a fee rule and production resource
qualification all remain outside this library change.
