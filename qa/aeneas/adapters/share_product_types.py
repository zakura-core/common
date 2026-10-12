"""Share identical production Rust types between independent product extractions.

Require byte-identical declaration blocks after namespace renaming, including
Rust symbol/source annotations and every field. Only declaration order may
vary. Replace the duplicate nominal Lean types with transparent aliases to the
already compiled portable model of those same Rust types. No function body or
constant is changed. This adapter is part of the translation trust boundary.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

if not __debug__:
    raise RuntimeError("This adapter requires Python assertions")

NAMES = ["core.marker.PhantomData", "field.pasta.PastaField",
    "field.pasta.representation.sealed.Sealed", "field.pasta.representation.ReductionState",
    "field.pasta.representation.Reduced", "field.pasta.representation.Loose",
    "field.pasta.parameters.sealed.Sealed", "field.pasta.parameters.sealed.Parameters",
    "field.pasta.parameters.PrimeModulus", "field.pasta.products.ProductSum",
    "field.pasta.products.PastaField.sum_of_products_slice.closure"]


def declarations(source, namespace):
    suffix = "\nend " + namespace + "\n"
    assert source.endswith(suffix)
    source = source[:-len(suffix)]
    pieces = re.split(r"\n(?=/--)", source)
    header, blocks = pieces[0], pieces[1:]
    assert header.endswith("namespace " + namespace + "\n")
    result = {}
    for block in blocks:
        matches = re.findall(r"^(?:structure|inductive|def) ([\w.]+)\b", block, re.M)
        assert len(matches) == 1 and matches[0] not in result
        result[matches[0]] = block.strip() + "\n"
    assert set(result) == set(NAMES)
    return header, result


def check_identity(source, reference, namespace):
    original_header, original = declarations(source.replace(namespace, "CommonProductsPortable"), "CommonProductsPortable")
    reference_header, expected = declarations(reference, "CommonProductsPortable")
    assert original_header == reference_header
    assert original == expected


def adapt(source, reference, namespace, self_test=False):
    assert namespace in {"CommonProductPairs", "CommonProductDotIter"}
    check_identity(source, reference, namespace)
    if self_test:
        mutations = [source.replace("limbs : Array Std.U64 4#usize", "limbs : Array Std.U64 3#usize"),
            source.replace("  TWICE_MODULUS :", "  CHANGED_MODULUS :"),
            source.replace("public import Aeneas", "public import Different"),
            source.replace("\nend " + namespace, "\nstructure Extra where\n  value : Nat\n\nend " + namespace)]
        assert all(m != source for m in mutations)
        for mutation in mutations:
            try:
                check_identity(mutation, reference, namespace)
            except AssertionError:
                pass
            else:
                raise RuntimeError("The type identity checker accepted a changed declaration")
    result = "module\npublic import CommonProductsPortable.Types\npublic import " + namespace + ".TypesExternal\n@[expose] public section\n\nnamespace " + namespace + "\n\n"
    result += "\n".join("abbrev " + name + " := CommonProductsPortable." + name for name in NAMES)
    result += "\n\nend " + namespace + "\n"
    digest = lambda text: hashlib.sha256(text.encode()).hexdigest()
    return result, {"same_production_Rust_type_declarations": len(NAMES),
        "declarations_identical_after_namespace_rename": True, "allowed_difference": "declaration order only",
        "all_function_bodies_and_constants_unchanged": True, "transparent_aliases": True,
        "rejected_mutations": 4 if self_test else 0, "original_sha256": digest(source),
        "reference_sha256": digest(reference), "adapted_sha256": digest(result)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("reference", type=Path)
    parser.add_argument("--namespace", default="CommonProductPairs")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    source, report = adapt(args.source.read_text(), args.reference.read_text(), args.namespace, args.self_test)
    args.source.write_text(source)
    print(json.dumps(report, indent=2))
