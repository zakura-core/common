"""Specialize only mutable std iterator dictionary calls in generated Lean.

Aeneas's ordinary Iterator dictionary omits the mutable borrow reconstruction
returned by its built-in IterMut.next model. Preserve that reconstruction with
a separate transparent dictionary and Zip model; Rust arithmetic is unchanged.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


def adapt(source, expected=1, chunks=0, expected_next=None):
    expected_next = expected if expected_next is None else expected_next
    original = source
    dictionaries = [
        ("core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT",
         "core.slice.iter.IteratorIterMut.next", expected),
        ("core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice",
         "core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next", chunks),
    ]
    blocks = []
    for marker, next_name, count in dictionaries:
        matches = list(re.finditer(r"\bimpl_def\s+" + re.escape(marker) + r"\s", source))
        if len(matches) != (1 if count else 0):
            raise RuntimeError("Unexpected mutable iterator dictionary: " + marker)
        if not matches:
            continue
        position = matches[0].start()
        start = source.rfind("/-- Trait implementation:", 0, position)
        end = source.index("\n}", position) + 2
        block = source[start:end]
        if start < 0 or not re.search(r"\bnext\s*:=\s*" + re.escape(next_name) + r"\s*\}", block):
            raise RuntimeError("Unexpected mutable next implementation")
        if len(re.findall(r"\b(?:impl_def|def)\s", block)) != 1:
            raise RuntimeError("The selected block contains another declaration")
        blocks.append((start, end, block))
    for start, end, block in sorted(blocks, reverse=True):
        source = source[:start] + source[end:]
    pairs = [
        ("core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next", "mutableZipNext"),
        ("core.iter.traits.iterator.Iterator.zip.trait_default", "mutableZipCtor"),
    ]
    for marker, _, expected_count in dictionaries:
        prefix = r"(?=\s+\(" + re.escape(marker) + r"\s)"
        for old, new in pairs:
            call_count = expected_next if marker == dictionaries[0][0] and new == "mutableZipNext" else expected_count
            source, count = re.subn(r"\b" + re.escape(old) + prefix, new, source)
            if count != call_count:
                raise RuntimeError(f"Expected {call_count} mutable {old} calls for {marker}, found {count}")
    recovered = source
    for old, new in pairs:
        recovered = re.sub(r"\b"+new+r"\b", old, recovered)
    for start, _, block in sorted(blocks):
        recovered = recovered[:start] + block + recovered[start:]
    if recovered != original:
        raise RuntimeError("The iterator specialization altered other generated code")
    digest = lambda text: hashlib.sha256(text.encode()).hexdigest()
    return source, {"original_sha256": digest(original), "adapted_sha256": digest(source),
        "dictionary_sha256": [digest(block) for _, _, block in sorted(blocks)],
        "mutable_zip_calls": expected, "mutable_zip_next_calls": expected_next, "chunk_mutable_zip_calls": chunks,
        "other_generated_code_unchanged": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--expected", type=int, default=1)
    parser.add_argument("--chunks", type=int, default=0)
    parser.add_argument("--expected-next", type=int)
    args = parser.parse_args()
    result, report = adapt(args.source.read_text(), args.expected, args.chunks, args.expected_next)
    args.source.write_text(result)
    print(json.dumps(report, indent=2))
