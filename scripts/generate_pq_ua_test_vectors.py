#!/usr/bin/env python3
"""Generate the post-quantum Unified Address test vectors.

The vectors this writes are only worth having if they come from somewhere other than
the code they test, so nothing here calls the Rust crate. Bech32m, F4Jumble and the
ZIP 316 item encoding are implemented from their specifications below, and the F4Jumble
implementation is checked against the upstream vectors the crate already carries before
any vector is emitted. A mismatch there means this file is wrong, not the crate.

Usage:
    python3 scripts/generate_pq_ua_test_vectors.py            # write the Rust file
    python3 scripts/generate_pq_ua_test_vectors.py --check    # self-test only
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
UPSTREAM_F4JUMBLE_VECTORS = (
    REPO_ROOT / "crates/zcash_address/src/kind/unified/f4jumble/test_vectors.rs"
)
OUTPUT = REPO_ROOT / "crates/zcash_address/src/kind/unified/pq_test_vectors.rs"

# ZIP 316 typecodes. The two post-quantum codes are provisional: the experimental range
# cannot hold them, because the shared ZIP 316 vectors use those values as their own
# unknown-receiver cases.
P2PKH = 0x00
P2SH = 0x01
SAPLING = 0x02
ORCHARD = 0x03
PQ_SHA2_128F = 0x04
PQ_SHA2_192S = 0x05

HRPS = {"main": "u", "test": "utest", "regtest": "uregtest"}
PADDING_LEN = 16


# --- F4Jumble (ZIP 316) -------------------------------------------------------------

OUTBYTES = 64
VALID_LENGTH = range(48, 4_194_368 + 1)
ROUND_OFFSET = 13


def _personalization(prefix: bytes, round_: int, block: int | None) -> bytes:
    personal = bytearray(prefix + b"\0\0\0")
    personal[ROUND_OFFSET] = round_
    if block is not None:
        personal[ROUND_OFFSET + 1 :] = block.to_bytes(2, "little")
    assert len(personal) == 16
    return bytes(personal)


def _blake2b(data: bytes, personal: bytes, length: int) -> bytes:
    return hashlib.blake2b(data, digest_size=length, person=personal).digest()


def _xor(target: bytearray, source: bytes) -> None:
    for i, byte in enumerate(source[: len(target)]):
        target[i] ^= byte


def f4jumble(message: bytes) -> bytes:
    """The forward permutation: G0, H0, G1, H1 over a left/right split."""
    if len(message) not in VALID_LENGTH:
        raise ValueError(f"message length {len(message)} is out of range")
    split = min(OUTBYTES, len(message) // 2)
    left, right = bytearray(message[:split]), bytearray(message[split:])

    def g_round(round_: int) -> None:
        for block in range((len(right) + OUTBYTES - 1) // OUTBYTES):
            start = block * OUTBYTES
            chunk = bytearray(right[start : start + OUTBYTES])
            _xor(
                chunk,
                _blake2b(
                    bytes(left),
                    _personalization(b"UA_F4Jumble_G", round_, block),
                    OUTBYTES,
                ),
            )
            right[start : start + len(chunk)] = chunk

    def h_round(round_: int) -> None:
        _xor(
            left,
            _blake2b(
                bytes(right),
                _personalization(b"UA_F4Jumble_H", round_, None),
                len(left),
            ),
        )

    g_round(0)
    h_round(0)
    g_round(1)
    h_round(1)
    return bytes(left + right)


# --- Bech32m (BIP 350) --------------------------------------------------------------

CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
BECH32M_CONST = 0x2BC830A3


def _polymod(values: list[int]) -> int:
    generator = [0x3B6A57B2, 0x26508E6D, 0x1EA119FA, 0x3D4233DD, 0x2A1462B3]
    chk = 1
    for value in values:
        top = chk >> 25
        chk = ((chk & 0x1FFFFFF) << 5) ^ value
        for i, coefficient in enumerate(generator):
            if (top >> i) & 1:
                chk ^= coefficient
    return chk


def _hrp_expand(hrp: str) -> list[int]:
    return [ord(c) >> 5 for c in hrp] + [0] + [ord(c) & 31 for c in hrp]


def _convertbits(data: bytes, frombits: int, tobits: int) -> list[int]:
    acc = 0
    bits = 0
    out = []
    maxv = (1 << tobits) - 1
    for value in data:
        acc = (acc << frombits) | value
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            out.append((acc >> bits) & maxv)
    if bits:
        out.append((acc << (tobits - bits)) & maxv)
    return out


def bech32m_encode(hrp: str, data: bytes) -> str:
    values = _convertbits(data, 8, 5)
    checksum_input = _hrp_expand(hrp) + values + [0, 0, 0, 0, 0, 0]
    polymod = _polymod(checksum_input) ^ BECH32M_CONST
    checksum = [(polymod >> 5 * (5 - i)) & 31 for i in range(6)]
    return hrp + "1" + "".join(CHARSET[d] for d in values + checksum)


# --- ZIP 316 item encoding ----------------------------------------------------------


def compact_size(value: int) -> bytes:
    if value < 253:
        return bytes([value])
    if value <= 0xFFFF:
        return b"\xfd" + value.to_bytes(2, "little")
    if value <= 0xFFFFFFFF:
        return b"\xfe" + value.to_bytes(4, "little")
    return b"\xff" + value.to_bytes(8, "little")


def encode_address(receivers: dict[int, bytes], hrp: str) -> tuple[bytes, str]:
    """Returns the raw padded encoding and the Bech32m address string.

    Items are written in ascending typecode order, which is ZIP 316's encoding order,
    then the HRP is appended zero-padded to sixteen bytes and the whole is jumbled.
    """
    raw = b"".join(
        compact_size(typecode) + compact_size(len(data)) + data
        for typecode, data in sorted(receivers.items())
    )
    padding = hrp.encode() + bytes(PADDING_LEN - len(hrp))
    padded = raw + padding
    return padded, bech32m_encode(hrp, f4jumble(padded))


# --- Self-test against the crate's upstream F4Jumble vectors -------------------------


def _parse_upstream_vectors(path: Path) -> list[tuple[bytes, bytes]]:
    text = path.read_text()
    blocks = re.findall(
        r"normal:\s*&\[(.*?)\],\s*jumbled:\s*&\[(.*?)\],", text, re.DOTALL
    )
    out = []
    for normal, jumbled in blocks:
        out.append(
            (
                bytes(int(b, 16) for b in re.findall(r"0x([0-9a-f]{2})", normal)),
                bytes(int(b, 16) for b in re.findall(r"0x([0-9a-f]{2})", jumbled)),
            )
        )
    return out


def self_test() -> None:
    vectors = _parse_upstream_vectors(UPSTREAM_F4JUMBLE_VECTORS)
    if not vectors:
        sys.exit(f"found no upstream F4Jumble vectors in {UPSTREAM_F4JUMBLE_VECTORS}")
    for index, (normal, jumbled) in enumerate(vectors):
        got = f4jumble(normal)
        if got != jumbled:
            sys.exit(
                f"F4Jumble self-test failed on upstream vector {index}:\n"
                f"  expected {jumbled.hex()}\n  got      {got.hex()}"
            )
    # One Bech32m string from BIP 350's own test vectors, to catch a checksum constant
    # or charset mistake. Its data part is empty, so only the checksum is exercised.
    expected = "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharac"
    expected += "tersbioandnumber11sg7hg6"
    got = bech32m_encode(
        "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharac"
        "tersbioandnumber1",
        b"",
    )
    if got != expected:
        sys.exit(f"Bech32m self-test failed:\n  expected {expected}\n  got      {got}")
    print(f"self-test passed: {len(vectors)} F4Jumble vectors, 1 Bech32m vector")


# --- Vector definitions -------------------------------------------------------------


def label_bytes(label: str, length: int) -> bytes:
    """Deterministic filler for receivers whose contents this crate does not interpret."""
    out = b""
    counter = 0
    while len(out) < length:
        out += hashlib.sha256(f"{label}/{counter}".encode()).digest()
        counter += 1
    return out[:length]


CASES = [
    (
        "orchard_and_pq_128f",
        "The additive case with no legacy transparent receiver.",
        {ORCHARD: label_bytes("orchard", 43), PQ_SHA2_128F: label_bytes("128f", 32)},
    ),
    (
        "orchard_and_pq_192s",
        "The same address under the stronger scheme.",
        {ORCHARD: label_bytes("orchard", 43), PQ_SHA2_192S: label_bytes("192s", 32)},
    ),
    (
        "orchard_p2pkh_and_pq_192s",
        "A PQ receiver beside the legacy transparent receiver it is meant to replace.",
        {
            ORCHARD: label_bytes("orchard", 43),
            P2PKH: label_bytes("p2pkh", 20),
            PQ_SHA2_192S: label_bytes("192s", 32),
        },
    ),
    (
        "sapling_p2sh_and_pq_128f",
        "A PQ receiver beside P2SH, which ZIP 316 bars P2PKH from accompanying.",
        {
            SAPLING: label_bytes("sapling", 43),
            P2SH: label_bytes("p2sh", 20),
            PQ_SHA2_128F: label_bytes("128f", 32),
        },
    ),
    (
        "every_pool_and_pq_192s",
        "Both shielded pools, a legacy transparent receiver, and a PQ receiver.",
        {
            ORCHARD: label_bytes("orchard", 43),
            SAPLING: label_bytes("sapling", 43),
            P2PKH: label_bytes("p2pkh", 20),
            PQ_SHA2_192S: label_bytes("192s", 32),
        },
    ),
]

NAMES = {
    P2PKH: "p2pkh",
    P2SH: "p2sh",
    SAPLING: "sapling",
    ORCHARD: "orchard",
    PQ_SHA2_128F: "pq_sha2_128f",
    PQ_SHA2_192S: "pq_sha2_192s",
}


def rust_bytes(data: bytes, indent: str) -> str:
    lines = []
    for start in range(0, len(data), 12):
        chunk = data[start : start + 12]
        lines.append(indent + " ".join(f"0x{b:02x}," for b in chunk))
    return "\n".join(lines)


def render() -> str:
    out = [
        "//! Post-quantum Unified Address vectors, generated outside this crate.",
        "//!",
        "//! Written by `scripts/generate_pq_ua_test_vectors.py`, which implements Bech32m,",
        "//! F4Jumble and the ZIP 316 item encoding from their specifications rather than",
        "//! calling this crate, and checks its F4Jumble against the upstream vectors in",
        "//! `f4jumble/test_vectors.rs` before emitting anything. Edit the generator, not",
        "//! this file.",
        "//!",
        "//! The two post-quantum typecodes are provisional, so these vectors are a",
        "//! regression fence for the encoding this crate produces today, not a durable",
        "//! interoperability claim. They move when the ZIP process assigns the codes.",
        "",
        "/// One address, with the receivers it carries and the string it encodes to.",
        "pub(super) struct TestVector {",
        "    /// A name for the case, used in assertion messages.",
        "    pub(super) name: &'static str,",
        "    /// Each receiver as `(typecode, data)`, in ascending typecode order.",
        "    pub(super) receivers: &'static [(u32, &'static [u8])],",
        "    /// The raw item encoding with the padded HRP appended, before F4Jumble.",
        "    pub(super) padded: &'static [u8],",
        "    /// The encoded address for each network, as `(hrp, address)`.",
        "    pub(super) encoded: &'static [(&'static str, &'static str)],",
        "}",
        "",
        "pub(super) const TEST_VECTORS: &[TestVector] = &[",
    ]
    for name, comment, receivers in CASES:
        padded_main, _ = encode_address(receivers, HRPS["main"])
        out.append(f"    // {comment}")
        out.append("    TestVector {")
        out.append(f'        name: "{name}",')
        out.append("        receivers: &[")
        for typecode, data in sorted(receivers.items()):
            out.append(f"            // {NAMES[typecode]}")
            out.append(f"            ({typecode:#04x}, &[")
            out.append(rust_bytes(data, " " * 16))
            out.append("            ]),")
        out.append("        ],")
        out.append("        padded: &[")
        out.append(rust_bytes(padded_main, " " * 12))
        out.append("        ],")
        out.append("        encoded: &[")
        for network in ("main", "test", "regtest"):
            hrp = HRPS[network]
            _, address = encode_address(receivers, hrp)
            out.append(f'            ("{hrp}", "{address}"),')
        out.append("        ],")
        out.append("    },")
    out.append("];")
    out.append("")
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="run the self-test and exit without writing the Rust file",
    )
    args = parser.parse_args()

    self_test()
    if args.check:
        return
    OUTPUT.write_text(render())
    print(f"wrote {len(CASES)} vectors to {OUTPUT.relative_to(REPO_ROOT)}")


if __name__ == "__main__":
    main()
