#!/usr/bin/env python3
"""An independent ZIP 248 oracle for the v7 transaction vectors.

It parses v7 transaction bytes and computes the txid, the authorizing data commitment,
and every variant 0 signature digest, following the ZIP 248 text only. It also checks
that each vector is shaped like a transaction consensus could accept: its value pool
deltas balance and match its transparent values, it has no NSM delta, and a coinbase
transaction spends from no pool. ZIP 248 only says that registration does not activate
a bundle; that NU7.1 does not activate the NSM bundle is an assumption of this
implementation.

The envelope vectors are transactions that the typed layer rejects but whose txid and
authorizing data commitment are still defined: some lack authorizing data, some have
signatures of other sighash variants, and some an unknown consensus branch ID. The
oracle checks only those two digests for them, hashing every `sighashInfo` as given.

Standard library only. See README.md for how the vectors are generated and checked.
"""

import hashlib
import re
import struct
import sys


def H(person, data=b""):
    assert len(person) == 16, person
    return hashlib.blake2b(data, digest_size=32, person=person).digest()


def cs(n):
    if n < 253:
        return bytes([n])
    if n <= 0xFFFF:
        return b"\xfd" + struct.pack("<H", n)
    if n <= 0xFFFFFFFF:
        return b"\xfe" + struct.pack("<I", n)
    return b"\xff" + struct.pack("<Q", n)


class R:
    def __init__(self, b):
        self.b = b
        self.i = 0

    def take(self, n):
        assert self.i + n <= len(self.b), "truncated"
        out = self.b[self.i:self.i + n]
        self.i += n
        return out

    def u8(self):
        return self.take(1)[0]

    def u16(self):
        return struct.unpack("<H", self.take(2))[0]

    def u32(self):
        return struct.unpack("<I", self.take(4))[0]

    def i64(self):
        return struct.unpack("<q", self.take(8))[0]

    def u64(self):
        return struct.unpack("<Q", self.take(8))[0]

    def cs(self):
        f = self.u8()
        if f < 253:
            return f
        if f == 253:
            n = self.u16()
            assert n >= 253
            return n
        if f == 254:
            n = self.u32()
            assert n >= 0x10000
            return n
        n = self.u64()
        assert n >= 0x100000000
        return n

    def done(self):
        assert self.i == len(self.b), "trailing bytes"


def parse(tx):
    r = R(tx)
    header = r.take(20)
    hdr, vgid, branch, lock_time, expiry = struct.unpack("<IIIII", header)
    assert hdr == 0x80000007, hex(hdr)
    deltas = [(r.cs(), r.cs(), r.i64()) for _ in range(r.cs())]
    effects = []
    for _ in range(r.cs()):
        t, v, n = r.cs(), r.cs(), r.cs()
        effects.append((t, v, r.take(n)))
    auths = []
    for _ in range(r.cs()):
        t, v, n = r.cs(), r.cs(), r.cs()
        auths.append((t, v, r.take(n)))
    r.done()
    return header, branch, deltas, effects, auths


# ---- effecting data ----

def transparent_effects(payload):
    r = R(payload)
    inputs = [(r.take(36), r.u32()) for _ in range(r.cs())]
    outputs = []
    for _ in range(r.cs()):
        value = r.take(8)
        script = r.take(r.cs())
        outputs.append(value + cs(len(script)) + script)
    r.done()
    return inputs, outputs


def transparent_effects_digest(payload):
    inputs, outputs = transparent_effects(payload)
    prevouts = H(b"ZTxIdPrevoutHash", b"".join(p for p, _ in inputs))
    sequence = H(b"ZTxIdSequencHash", b"".join(struct.pack("<I", s) for _, s in inputs))
    outs = H(b"ZTxIdOutputsHash", b"".join(outputs))
    return H(b"ZTxIdTranspaHash", prevouts + sequence + outs)


def coinbase_effects_digest(payload):
    r = R(payload)
    height = r.u32()
    subsidy = r.u64()
    lockbox = r.u64()
    data = r.take(r.cs())
    n = r.cs()
    signals = r.take(2 * n)
    poll = r.take(16) if n > 0 else b""
    r.done()
    assert 1 <= height <= 499999999 and lockbox <= subsidy and len(data) <= 94
    codes = signals[0::2]
    assert all(codes[i] < codes[i + 1] for i in range(len(codes) - 1))
    preimage = (struct.pack("<I", height) + struct.pack("<Q", subsidy) + struct.pack("<Q", lockbox)
                + cs(len(data)) + data + cs(n) + signals + poll)
    return H(b"ZTxIdCoinbasHash", preimage)


def sapling_effects(payload):
    r = R(payload)
    spends = [(r.take(32), r.take(32), r.take(32)) for _ in range(r.cs())]
    outputs = [(r.take(32), r.take(32), r.take(32), r.take(580), r.take(80)) for _ in range(r.cs())]
    r.done()
    assert spends or outputs
    return spends, outputs


def sapling_effects_digest(payload):
    spends, outputs = sapling_effects(payload)
    if spends:
        compact = H(b"ZTxIdSSpendCHash", b"".join(nf for _, nf, _ in spends))
        noncompact = H(b"ZTxIdSSpendNH_v6", b"".join(cv + rk for cv, _, rk in spends))
        spends_digest = H(b"ZTxIdSSpendsHash", compact + noncompact)
    else:
        spends_digest = H(b"ZTxIdSSpendsHash")
    if outputs:
        c = H(b"ZTxIdSOutC__Hash", b"".join(cmu + epk + enc[:52] for _, cmu, epk, enc, _ in outputs))
        m = H(b"ZTxIdSOutM__Hash", b"".join(enc[52:564] for _, _, _, enc, _ in outputs))
        n = H(b"ZTxIdSOutN__Hash", b"".join(cv + enc[564:] + out for cv, _, _, enc, out in outputs))
        outputs_digest = H(b"ZTxIdSOutputHash", c + m + n)
    else:
        outputs_digest = H(b"ZTxIdSOutputHash")
    return H(b"ZTxIdSaplingH_v7", spends_digest + outputs_digest)


ORCHARD_PERSON = {
    3: (b"ZTxIdOrchardH_v7", b"ZTxIdOrcActCHash", b"ZTxIdOrcActMHash", b"ZTxIdOrcActNHash",
        b"ZTxAuthOrchaH_v7"),
    4: (b"ZTxIdIronwd_Hash", b"ZTxIdIrnActCH_v6", b"ZTxIdIrnActMH_v6", b"ZTxIdIrnActNH_v6",
        b"ZTxAuthIrnwdHash"),
}


def orchard_effects(payload):
    r = R(payload)
    actions = [(r.take(32), r.take(32), r.take(32), r.take(32), r.take(32), r.take(580), r.take(80))
               for _ in range(r.cs())]
    assert actions
    flags = r.take(1)
    r.done()
    return actions, flags


def orchard_effects_digest(t, payload):
    root, pc, pm, pn, _ = ORCHARD_PERSON[t]
    actions, flags = orchard_effects(payload)
    c = H(pc, b"".join(nf + cmx + epk + enc[:52] for _, nf, _, cmx, epk, enc, _ in actions))
    m = H(pm, b"".join(enc[52:564] for *_, enc, _ in actions))
    n = H(pn, b"".join(cv + rk + enc[564:] + out for cv, _, rk, _, _, enc, out in actions))
    return H(root, c + m + n + flags)


# ---- authorizing data ----

def sighash_info(r, variant0_only):
    """Reads a sighashInfo field and returns its field encoding."""
    info = r.take(r.cs())
    assert info, "a sighashInfo starts with its sighash variant"
    assert not variant0_only or info == b"\x00", info
    return cs(len(info)) + info


def signature_field(r, variant0_only):
    return sighash_info(r, variant0_only) + r.take(64)


def transparent_auth_digest(payload, n_inputs, variant0_only):
    r = R(payload)
    parts = []
    for _ in range(n_inputs):
        info = sighash_info(r, variant0_only)
        script = r.take(r.cs())
        parts.append(info + cs(len(script)) + script)
    r.done()
    return H(b"ZTxAuthTransHash", b"".join(parts))


def sapling_auth_digest(payload, n_spends, n_outputs, variant0_only):
    r = R(payload)
    anchor = r.take(32) if n_spends else b""
    spend_proofs = r.take(192 * n_spends)
    spend_sigs = b"".join(signature_field(r, variant0_only) for _ in range(n_spends))
    output_proofs = r.take(192 * n_outputs)
    binding = signature_field(r, variant0_only)
    r.done()
    return H(b"ZTxAuthSapliH_v7", anchor + spend_proofs + spend_sigs + output_proofs + binding)


def orchard_auth_digest(t, payload, n_actions, variant0_only):
    r = R(payload)
    anchor = r.take(32)
    proofs = r.take(r.cs())
    assert len(proofs) == 2720 + 2272 * n_actions
    sigs = b"".join(signature_field(r, variant0_only) for _ in range(n_actions))
    binding = signature_field(r, variant0_only)
    r.done()
    return H(ORCHARD_PERSON[t][4], anchor + proofs + sigs + binding)


def digests(tx, variant0_only=True):
    """Computes the txid and authorizing data commitment of `tx`.

    With `variant0_only`, every sighashInfo must select sighash variant 0, as in a
    transaction that the typed layer accepts.
    """
    header, branch, deltas, effects, auths = parse(tx)
    bp = struct.pack("<I", branch)
    header_digest = H(b"ZTxIdHeadersHash", header)
    vpd = H(b"ZTxIdVPDeltaHash", b"".join(cs(t) + cs(v) + struct.pack("<q", x) for t, v, x in deltas))
    counts = {}
    eff = b""
    for t, v, payload in effects:
        assert v == 0
        if t == 0:
            d = transparent_effects_digest(payload)
            counts[0] = len(transparent_effects(payload)[0])
        elif t == 1:
            d = coinbase_effects_digest(payload)
        elif t == 2:
            d = sapling_effects_digest(payload)
            s, o = sapling_effects(payload)
            counts[2] = (len(s), len(o))
        else:
            d = orchard_effects_digest(t, payload)
            counts[t] = len(orchard_effects(payload)[0])
        eff += cs(t) + cs(v) + d
    txid = H(b"ZcashTxHash_" + bp, header_digest + vpd + H(b"ZTxIdEffBnd_Hash", eff))
    auth = b""
    for t, v, payload in auths:
        if t == 0:
            d = transparent_auth_digest(payload, counts[0], variant0_only)
        elif t == 2:
            d = sapling_auth_digest(payload, *counts[2], variant0_only)
        else:
            d = orchard_auth_digest(t, payload, counts[t], variant0_only)
        auth += cs(t) + cs(v) + d
    auth_digest = H(b"ZTxAuthHash_" + bp, H(b"ZTxAuthBnd__Hash", auth))
    return txid, auth_digest, dict(effects=effects, counts=counts)


def signature_digest(txid, amounts, scripts, t, v, context):
    amounts_digest = H(b"ZTxTrAmountsHash", b"".join(struct.pack("<q", a) for a in amounts))
    scripts_digest = H(b"ZTxTrScriptsHash", b"".join(cs(len(s)) + s for s in scripts))
    return H(b"ZcashSigHash_v7_", b"\x00" + txid + amounts_digest + scripts_digest + cs(t) + cs(v) + context)


NSM_BUNDLE_TYPE = 6


def check_plausible(tx, amounts):
    """Checks the consensus rules a vector should satisfy beyond its encoding."""
    _, _, deltas, effects, _ = parse(tx)
    delta = {t: x for t, _, x in deltas}
    payloads = {t: p for t, _, p in effects}
    assert NSM_BUNDLE_TYPE not in delta, "an NSM delta, assumed inactive at NU7.1"
    assert sum(delta.values()) == 0, ("deltas do not balance", delta)
    inputs, outputs = transparent_effects(payloads[0]) if 0 in payloads else ([], [])
    output_values = sum(struct.unpack("<q", out[:8])[0] for out in outputs)
    assert delta.get(0, 0) == sum(amounts) - output_values, "transparent delta"
    if 1 in payloads:
        assert not inputs, "a coinbase transaction has transparent inputs"
        assert delta.get(5, 0) >= 0, "a coinbase transaction pays a fee"
        if 2 in payloads:
            assert not sapling_effects(payloads[2])[0], "a coinbase transaction spends Sapling"
        for t in (3, 4):
            if t in payloads:
                assert orchard_effects(payloads[t])[1][0] & 1 == 0, "coinbase enables spends"
    else:
        assert delta.get(5, 0) <= 0, "a non-coinbase transaction collects a fee"


def check_vector(vector):
    """Checks one vector, and returns the number of signature digests checked."""
    tx = bytes.fromhex(vector["tx"])
    amounts, scripts = vector["amounts"], vector["scripts"]
    check_plausible(tx, amounts)
    txid, auth, info = digests(tx)
    assert txid.hex() == vector["txid"], ("txid", txid.hex(), vector["txid"])
    assert auth.hex() == vector["auth"], ("auth", auth.hex(), vector["auth"])
    payloads = dict((t, p) for t, _, p in info["effects"])
    inputs = transparent_effects(payloads[0])[0] if 0 in payloads else []
    for label, got in vector["sigs"]:
        sig = label.split(" ")
        if sig[0] == "t":
            i = int(sig[1])
            prevout, seq = inputs[i]
            context = (prevout + struct.pack("<q", amounts[i]) + cs(len(scripts[i])) + scripts[i]
                       + struct.pack("<I", seq) + struct.pack("<H", i))
            expected = signature_digest(txid, amounts, scripts, 0, 0, context)
        else:
            t = int(sig[1])
            context = b"" if sig[2] == "b" else struct.pack("<H", int(sig[2]))
            expected = signature_digest(txid, amounts, scripts, t, 0, context)
        assert expected.hex() == got, ("sig", label, expected.hex())
    return len(vector["sigs"])


def check_envelope_vector(vector):
    """Checks the txid and authorizing data commitment of one envelope vector."""
    txid, auth, _ = digests(bytes.fromhex(vector["tx"]), variant0_only=False)
    assert txid.hex() == vector["txid"], ("txid", txid.hex(), vector["txid"])
    assert auth.hex() == vector["auth"], ("auth", auth.hex(), vector["auth"])


def vectors_from_dump(text):
    """Reads the vectors that the Rust test `dump_vectors_for_oracle` writes."""
    vectors = []
    for block in text.split("END\n"):
        if not block.strip():
            continue
        fields = {}
        sigs = []
        for line in block.strip().split("\n"):
            key, rest = (line.split(" ", 1) + [""])[:2]
            if key == "SIG":
                label, digest = rest.rsplit(" ", 1)
                sigs.append((label, digest))
            else:
                fields[key] = rest
        vectors.append(dict(
            tx=fields["TX"],
            amounts=[int(a) for a in fields["AMOUNTS"].split(",") if a],
            scripts=[bytes.fromhex(s) for s in fields["SCRIPTS"].split(",") if fields["SCRIPTS"]],
            txid=fields["TXID"],
            auth=fields["AUTH"],
            sigs=sigs,
        ))
    return vectors


def vectors_from_rust(text):
    """Reads the frozen vectors of `vectors.rs`, as written or as rustfmt lays them out."""
    vectors = []
    for body in re.findall(r"TestVector \{(.*?)\n    \},", text, re.S):
        tx = re.search(r"tx: (?:concat!\((.*?)\)|(\"[0-9a-f]*\"))", body, re.S)
        amounts = re.search(r"amounts: &\[(.*?)\]", body, re.S).group(1)
        scripts = re.search(r"script_pubkeys: &\[(.*?)\]", body, re.S).group(1)
        vectors.append(dict(
            tx="".join(re.findall(r'"([0-9a-f]*)"', tx.group(1) or tx.group(2))),
            amounts=[int(a) for a in re.findall(r"\d+", amounts)],
            scripts=[bytes.fromhex(s) for s in re.findall(r'"([0-9a-f]*)"', scripts)],
            txid=re.search(r'txid: "([0-9a-f]+)"', body).group(1),
            auth=re.search(r'auth_digest: "([0-9a-f]+)"', body).group(1),
            sigs=re.findall(r'\(\s*"([^"]+)",\s*"([0-9a-f]+)",?\s*\)', body),
        ))
    return vectors


def envelope_vectors_from_rust(text):
    """Reads the vectors of `envelope_vectors.rs`."""
    vectors = []
    for body in re.findall(r"\n    EnvelopeVector \{(.*?)\n    \},", text, re.S):
        tx = re.search(r"tx: (?:concat!\((.*?)\)|(\"[0-9a-f]*\"))", body, re.S)
        vectors.append(dict(
            scenario=re.search(r'scenario: "([^"]+)"', body).group(1),
            tx="".join(re.findall(r'"([0-9a-f]*)"', tx.group(1) or tx.group(2))),
            txid=re.search(r'txid: "([0-9a-f]+)"', body).group(1),
            auth=re.search(r'auth_digest: "([0-9a-f]+)"', body).group(1),
        ))
    return vectors


def read_vectors(path):
    """Reads the vectors of a dump, or of `vectors.rs` if `path` names a Rust file."""
    with open(path) as f:
        text = f.read()
    return vectors_from_rust(text) if path.endswith(".rs") else vectors_from_dump(text)


USAGE = """usage: oracle.py <vector dump | vectors.rs> [envelope_vectors.rs]
       oracle.py --envelope-digests <transaction hex>"""


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) == 2 and argv[0] == "--envelope-digests":
        txid, auth, _ = digests(bytes.fromhex(argv[1]), variant0_only=False)
        print(f"txid {txid.hex()}")
        print(f"auth_digest {auth.hex()}")
        return
    if len(argv) not in (1, 2):
        sys.exit(USAGE)
    vectors = read_vectors(argv[0])
    checked = sum(check_vector(v) for v in vectors)
    print(f"checked {len(vectors)} vectors and {checked} signature digests")
    if len(argv) == 2:
        with open(argv[1]) as f:
            envelope_vectors = envelope_vectors_from_rust(f.read())
        for vector in envelope_vectors:
            check_envelope_vector(vector)
        print(f"checked {len(envelope_vectors)} envelope vectors")


if __name__ == "__main__":
    main()
