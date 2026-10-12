#!/usr/bin/env python3
"""Remove an unused dictionary back edge, retaining all callbacks and bodies."""

import argparse
import copy
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("The projection checks require Python assertions")


def project(data):
    translated = data["translated"]
    original = copy.deepcopy(translated)
    name = [{"Ident": [part, 0]} for part in
            ["zakura_udon", "field", "pasta", "parameters", "sealed", "Parameters"]]
    parameters = next(decl["def_id"] for decl in translated["trait_decls"]
                      if decl and decl["item_meta"]["name"] == name)

    def reject_parent_references(value):
        if isinstance(value, dict):
            if "ParentClause" in value:
                parent, _ = value["ParentClause"]
                assert parent["Untagged"]["trait_decl_ref"]["skip_binder"]["id"] != parameters
            for child in value.values():
                reject_parent_references(child)
        elif isinstance(value, list):
            for child in value:
                reject_parent_references(child)

    for category in ["type_decls", "fun_decls", "global_decls", "trait_decls", "trait_impls"]:
        reject_parent_references(translated[category])
    declaration = translated["trait_decls"][parameters]
    assert len(declaration["implied_clauses"]) == 1
    prime = declaration["implied_clauses"][0]["trait_"]["skip_binder"]["id"]
    prime_name = name[:-2] + [{"Ident": ["PrimeModulus", 0]}]
    assert translated["trait_decls"][prime]["item_meta"]["name"] == prime_name
    declaration["implied_clauses"] = []
    implementations = {i for i, impl in enumerate(translated["trait_impls"])
                       if impl and impl["impl_trait"]["id"] == parameters}
    assert len(implementations) == 2
    for index in implementations:
        implementation = translated["trait_impls"][index]
        assert len(implementation["implied_trait_refs"]) == 1
        implementation["implied_trait_refs"] = []
    order = []
    for group in translated["ordered_decls"]:
        kind, entries = next(iter(group.items()))
        if kind == "TraitDecl" and "Rec" in entries and parameters in entries["Rec"]:
            assert set(entries["Rec"]) == {parameters, prime}
            order.extend([{"TraitDecl": {"NonRec": parameters}}, {"TraitDecl": {"NonRec": prime}}])
        elif kind == "TraitImpl" and "Rec" in entries and implementations.intersection(entries["Rec"]):
            assert len(entries["Rec"]) == 2
            first = next(index for index in entries["Rec"] if index in implementations)
            second = next(index for index in entries["Rec"] if index not in implementations)
            assert translated["trait_impls"][second]["impl_trait"]["id"] == prime
            order.extend([{"TraitImpl": {"NonRec": first}}, {"TraitImpl": {"NonRec": second}}])
        else:
            order.append(group)
    translated["ordered_decls"] = order
    for category in ["fun_decls", "type_decls", "global_decls"]:
        assert original[category] == translated[category]
    for index, decl in enumerate(original["trait_decls"]):
        expected = copy.deepcopy(decl)
        if index == parameters:
            expected["implied_clauses"] = []
        assert translated["trait_decls"][index] == expected
    for index, impl in enumerate(original["trait_impls"]):
        expected = copy.deepcopy(impl)
        if index in implementations:
            expected["implied_trait_refs"] = []
        assert translated["trait_impls"][index] == expected
    return "Unused parent projected; all bodies, types, globals and callback fields retained."


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    data = json.loads(args.source.read_text())
    report = project(data)
    args.destination.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    print(report)


if __name__ == "__main__":
    main()
