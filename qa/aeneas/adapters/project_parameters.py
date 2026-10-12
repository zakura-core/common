"""Project parameter dictionary entries that no retained body uses.

The projection rejects references to the removed parent dictionary and callback
fields. Every arithmetic body, type, and compiled constant remains unchanged.
With --retain-callback-functions, transparent exponentiation callbacks remain
independent proof roots. With --large-sqrt, the four transparent large-table
callbacks are retained instead. Their exact bodies are checked before the
unused dictionary cycle is split; calling an erased field is always rejected.
"""

import argparse
import copy
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("This translation adapter requires Python assertions")


def project(document, retain_callback_functions=False, large_sqrt=False,
            generic_dictionary=False):
    t = document["translated"]
    original = copy.deepcopy(t)
    name = [{"Ident": [x, 0]} for x in
            ["zakura_udon", "field", "pasta", "parameters", "sealed", "Parameters"]]
    pid = next(d["def_id"] for d in t["trait_decls"]
               if d and d["item_meta"]["name"] == name)
    parameters = t["trait_decls"][pid]
    assert len(parameters["implied_clauses"]) == 1
    clause = parameters["implied_clauses"][0]
    assert clause["clause_id"] == 0
    prime_id = clause["trait_"]["skip_binder"]["id"]
    assert t["trait_decls"][prime_id]["item_meta"]["name"][-1] == {"Ident": ["PrimeModulus", 0]}
    expected_methods = {"pow_sqrt_exponent"}
    retained_names = expected_methods if retain_callback_functions else set()
    if large_sqrt:
        assert retain_callback_functions
        expected_methods |= {"sqrt_large", "sqrt_finish_large"}
        retained_names = {"sqrt_large", "sqrt_finish_large"}
    assert {method["skip_binder"]["name"] for method in parameters["methods"]} == expected_methods
    assert len(parameters["methods"]) == len(expected_methods)
    implementations = {i for i, d in enumerate(t["trait_impls"])
                       if d and d["impl_trait"]["id"] == pid}
    # A direct generic method root retains the dictionary declaration but no
    # concrete implementations. Require that shape explicitly; the native
    # wrapper extraction continues to require both Pasta implementations.
    expected_implementations = 0 if generic_dictionary else 2
    assert len(implementations) == expected_implementations
    if generic_dictionary:
        assert not retain_callback_functions and not large_sqrt
    callbacks = set()
    retained = set()
    for i in implementations:
        d = t["trait_impls"][i]
        assert len(d["implied_trait_refs"]) == 1 and len(d["methods"]) == len(expected_methods)
        method_names = {}
        for index, method in enumerate(d["methods"]):
            assert method["kind"] == {"TraitMethod": [pid, index]}
            name = parameters["methods"][index]["skip_binder"]["name"]
            function_name = t["fun_decls"][method["skip_binder"]["id"]]["item_meta"]["name"][-1]
            assert function_name == {"Ident": [name, 0]}
            method_names[method["skip_binder"]["id"]] = name
        assert set(method_names.values()) == expected_methods
        for method in d["methods"]:
            callbacks.add(method["skip_binder"]["id"])
            if method_names[method["skip_binder"]["id"]] in retained_names:
                retained.add(method["skip_binder"]["id"])
    assert len(callbacks) == expected_implementations * len(expected_methods)
    assert len(retained) == expected_implementations * len(retained_names)
    for i in callbacks:
        if i in retained:
            assert set(t["fun_decls"][i]["body"]) == {"Structured"}
        else:
            assert t["fun_decls"][i]["body"] == "Opaque"

    def check(x):
        if isinstance(x, dict):
            if "ParentClause" in x:
                parent, _ = x["ParentClause"]
                assert parent["Untagged"]["trait_decl_ref"]["skip_binder"]["id"] != pid
            if "Fun" in x and isinstance(x["Fun"], int):
                assert x["Fun"] not in callbacks
            if "TraitMethod" in x and isinstance(x["TraitMethod"], dict):
                assert x["TraitMethod"].get("trait_id") != pid
            for v in x.values():
                check(v)
        elif isinstance(x, list):
            for v in x:
                check(v)

    for i, f in enumerate(t["fun_decls"]):
        if f and (i not in callbacks or i in retained):
            check(f["body"])
            check(f["signature"])
    for g in t["global_decls"]:
        if g:
            check(g["value"])
    parameters["implied_clauses"] = []
    parameters["methods"] = []
    if not retained:
        t["assoc_item_names"][pid]["methods"] = []
    for i in implementations:
        t["trait_impls"][i]["implied_trait_refs"] = []
        t["trait_impls"][i]["methods"] = []
    for i in callbacks:
        if i in retained:
            # Aeneas otherwise drops these now-unreferenced dependency functions.
            t["fun_decls"][i]["item_meta"]["is_local"] = True
        else:
            t["fun_decls"][i] = None

    order = []
    for declaration in t["ordered_decls"]:
        kind, group = next(iter(declaration.items()))
        if kind == "Fun" and group.get("NonRec") in callbacks - retained:
            continue
        if kind == "TraitDecl" and "Rec" in group and pid in group["Rec"]:
            assert set(group["Rec"]) == {pid, prime_id}
            order.extend([{"TraitDecl": {"NonRec": pid}},
                          {"TraitDecl": {"NonRec": prime_id}}])
        elif kind == "Mixed" and retained:
            members = group["Rec"]
            impls = {m["TraitImpl"] for m in members if "TraitImpl" in m}
            funs = {m["Fun"] for m in members if "Fun" in m}
            assert len(members) == len(impls) + len(funs)
            assert len(impls) == 2 and 1 <= len(funs) <= len(expected_methods)
            assert funs <= callbacks
            first = next(i for i in impls if i in implementations)
            second = next(i for i in impls if i not in implementations)
            assert t["trait_impls"][second]["impl_trait"]["id"] == prime_id
            assert funs <= {method["skip_binder"]["id"]
                            for method in original["trait_impls"][first]["methods"]}
            order.extend([{"TraitImpl": {"NonRec": first}},
                          {"TraitImpl": {"NonRec": second}}])
            order.extend({"Fun": {"NonRec": i}} for i in sorted(funs & retained))
        elif kind == "TraitImpl" and "Rec" in group and implementations.intersection(group["Rec"]):
            assert len(group["Rec"]) == 2
            first = next(i for i in group["Rec"] if i in implementations)
            second = next(i for i in group["Rec"] if i not in implementations)
            assert t["trait_impls"][second]["impl_trait"]["id"] == prime_id
            order.extend([{"TraitImpl": {"NonRec": first}},
                          {"TraitImpl": {"NonRec": second}}])
        else:
            order.append(declaration)
    t["ordered_decls"] = order
    for i, f in enumerate(original["fun_decls"]):
        if i in retained:
            expected = copy.deepcopy(f)
            expected["item_meta"]["is_local"] = True
            assert t["fun_decls"][i] == expected
        elif i not in callbacks:
            assert t["fun_decls"][i] == f
    assert original["type_decls"] == t["type_decls"]
    assert original["global_decls"] == t["global_decls"]
    return {"erased_unused_parent": pid, "erased_unused_callback_fields": sorted(callbacks),
            "retained_callback_functions": sorted(retained),
            "retained_function_bodies_unchanged": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--retain-callback-functions", action="store_true")
    parser.add_argument("--large-sqrt", action="store_true")
    parser.add_argument("--generic-dictionary", action="store_true")
    args = parser.parse_args()
    data = json.loads(args.source.read_text())
    report = project(data, args.retain_callback_functions, args.large_sqrt,
                     args.generic_dictionary)
    args.output.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    print(json.dumps(report, indent=2))
