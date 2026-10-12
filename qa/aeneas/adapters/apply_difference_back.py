"""Apply two mutable Zip backward functions to their original slice seeds.

After loop exits are hoisted, Aeneas's opaque Iterator dictionaries leave a
backward function where the caller expects the restored Zip. The subtraction
proof checks all eight reconstructed writes. Operational agreement with Rust's
mutable iterators remains an explicit standard-library translation boundary.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

if not __debug__:
    raise RuntimeError("This adapter requires Python assertions")


def adapt(original):
    name = "zakura_udon.field.pasta.products.PastaField.product_difference"
    assert original.count("def " + name + "\n") == 1
    start = original.index("def " + name + "\n")
    end = original.index("\n/--", start)
    body = original[start:end]
    changed = body
    replacements = []
    for loop, borrow, back, seed in [("1", "borrow", "back1", "iter1"),
                                     ("3", "borrow", "back", "iter")]:
        call = rf"let \({borrow}, {back}\) ←\s+{re.escape(name)}_loop{loop}\s+{seed}\s+\(fun z => z\) 0#u64"
        assert len(re.findall(call, body)) == 1
        before = f"let im1 := trait_default_back {back}\n"
        after = f"let im1 := trait_default_back ({back} {seed})\n"
        assert changed.count(before) == 1 and after not in changed
        replacements.append((before, after))
        changed = changed.replace(before, after)
    result = original[:start] + changed + original[end:]
    restored = result
    for before, after in reversed(replacements):
        assert restored.count(after) == 1
        restored = restored.replace(after, before)
    assert restored == original
    digest = lambda text: hashlib.sha256(text.encode()).hexdigest()
    return result, {"restored_zip_borrows": 2, "all_other_generated_code_unchanged": True,
                    "original_sha256": digest(original), "adapted_sha256": digest(result)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lean_file", type=Path)
    args = parser.parse_args()
    result, report = adapt(args.lean_file.read_text())
    args.lean_file.write_text(result)
    print(json.dumps(report))


if __name__ == "__main__":
    main()
