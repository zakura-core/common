#!/usr/bin/env python3
"""Check that the AVX2 arithmetic functions do not use AVX-512 instructions.

Pass unstripped Pasta test binaries built with `-C target-cpu=x86-64-v3`, or
with `--features glv,multicore,x86_64-asm` and no extra target CPU features.
`target-cpu=native` on AVX-512 hardware deliberately permits those instructions
and is not suitable for this check.

Example:
    python3 scripts/check_avx2_isa.py target/debug/deps/pasta_curves-<hash>

The check covers the named AVX2 square-root/chord functions and chord-level
entry points, including code inlined into those functions. It does not claim
to validate the instruction set of the entire binary or external callees.
"""

import argparse
import re
import subprocess


SYMBOL = re.compile(r"^[0-9a-f]+ <(.*)>:$")
INSTRUCTION = re.compile(r"^\s+[0-9a-f]+:")
AVX512_REGISTER = re.compile(r"%zmm\d+|%ymm(?:1[6-9]|2\d|3[01])\b|%k[0-7]\b")
LEGACY_PREFIXES = {"f0", "f2", "f3", "2e", "36", "3e", "26", "64", "65", "66", "67"}
ARITHMETIC_SYMBOLS = ("avx2_chord", "chord_level", "avx2_sqrt")


def inspect(assembly):
    symbol = ""
    instructions = 0
    violations = []
    for line in assembly.splitlines():
        match = SYMBOL.match(line)
        if match:
            symbol = match.group(1)
        if not any(name in symbol for name in ARITHMETIC_SYMBOLS):
            continue
        # GNU objdump separates the address, bytes, and mnemonic with tabs.
        # Ignore wrapped byte continuations, which have no mnemonic.
        columns = line.split("\t")
        if not INSTRUCTION.match(line) or len(columns) < 3 or not columns[2].strip():
            continue
        instructions += 1
        if AVX512_REGISTER.search(columns[2]):
            violations.append((symbol, "AVX-512 register", line.strip()))
        encoding = columns[1].split()
        while encoding and encoding[0] in LEGACY_PREFIXES:
            encoding = encoding[1:]
        # EVEX can encode AVX-512VL operations using only low YMM registers,
        # so a register-name check alone is insufficient.
        if encoding and encoding[0] == "62":
            violations.append((symbol, "EVEX encoding", line.strip()))
    return instructions, violations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binaries", nargs="+", help="Unstripped x86-64 Pasta test binaries")
    parser.add_argument("--objdump", default="objdump", help="GNU objdump executable")
    args = parser.parse_args()
    failed = False
    for binary in args.binaries:
        assembly = subprocess.check_output([args.objdump, "-d", "-C", binary], text=True)
        instructions, violations = inspect(assembly)
        print(f"{binary}: {instructions} arithmetic instructions, {len(violations)} violations")
        if instructions == 0:
            print("No matching arithmetic instructions: check the features and debug symbols.")
            failed = True
        for symbol, reason, line in violations:
            print(f"  {symbol}: {reason}: {line}")
        failed |= bool(violations)
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
