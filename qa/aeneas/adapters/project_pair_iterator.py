"""Expose IntoIterator's existing Iterator dictionary to the pair-sum loop.

The pinned Aeneas loop export drops the collection type parameter while retaining
its parent-dictionary projection. Add an explicit Iterator clause and replace
only that projection. Public Lean contracts must supply IntoIterator.iteratorInst
for the added argument. Calls in this extraction pass that same parent directly.
This is an audited dictionary projection, not a verified compiler pass.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from unroll_merge import named, nodes

if not __debug__:
    raise RuntimeError("This adapter requires Python assertions")


def target(data):
    matches = [f for f in data["translated"]["fun_decls"] if f
        and f["item_meta"]["name"][:4] == named("zakura_udon", "field", "pasta", "products")
        and f["item_meta"]["name"][-1] == {"Ident": ["sum_of_product_pairs", 0]}]
    assert len(matches) == 1
    return matches[0]


def parent_refs(body):
    return [n for n in nodes(body) if isinstance(n, dict)
        and isinstance(n.get("Untagged"), dict)
        and isinstance(n["Untagged"].get("kind"), dict)
        and "ParentClause" in n["Untagged"]["kind"]]


def inventory(data):
    function = target(data)
    generics = function["generics"]
    assert [t["index"] for t in generics["types"]] == list(range(5))
    assert len(generics["regions"]) == 1 and not generics["const_generics"]
    assert [c["clause_id"] for c in generics["trait_clauses"]] == list(range(4))
    refs = parent_refs(function["body"])
    assert len(refs) == 6 and all(r == refs[0] for r in refs)
    parent = refs[0]
    base, index = parent["Untagged"]["kind"]["ParentClause"]
    assert index == 0 and base["Untagged"]["kind"] == {"Clause": {"Free": 3}}
    assert base["Untagged"]["trait_decl_ref"] == generics["trait_clauses"][3]["trait_"]
    into = base["Untagged"]["trait_decl_ref"]["skip_binder"]
    iterator = parent["Untagged"]["trait_decl_ref"]["skip_binder"]
    traits = data["translated"]["trait_decls"]
    assert traits[into["id"]]["item_meta"]["name"] == named("core", "iter", "traits", "collect", "IntoIterator")
    assert traits[iterator["id"]]["item_meta"]["name"] == named("core", "iter", "traits", "iterator", "Iterator")
    implied = traits[into["id"]]["implied_clauses"]
    assert len(implied) == 1 and implied[0]["clause_id"] == 0
    implied_trait = implied[0]["trait_"]
    assert implied_trait["regions"] == [] and implied_trait["skip_binder"]["id"] == iterator["id"]
    assert implied_trait["skip_binder"]["generics"] == {
        "regions": [], "types": [{"Untagged": {"TypeVar": {"Free": i}}} for i in (2, 1)],
        "const_generics": [], "trait_refs": []}
    expected = copy.deepcopy(into["generics"])
    expected["types"] = [expected["types"][i] for i in (2, 1)]
    assert iterator["generics"] == expected
    assert into["generics"]["types"][0] == {"Untagged": {"TypeVar": {"Free": 3}}}
    assert into["generics"]["types"][2] == {"Untagged": {"TypeVar": {"Free": 4}}}
    assert parent["Untagged"]["trait_decl_ref"]["regions"] == []
    return function, parent


def replacement(parent):
    direct = copy.deepcopy(parent)
    direct["Untagged"]["kind"] = {"Clause": {"Free": 4}}
    return direct


def map_reference(value, source, destination):
    if value == source:
        return copy.deepcopy(destination)
    if isinstance(value, dict):
        return {k: map_reference(v, source, destination) for k, v in value.items()}
    if isinstance(value, list):
        return [map_reference(v, source, destination) for v in value]
    return value


def calls(data, identifier):
    for f in data["translated"]["fun_decls"]:
        if not f or not f.get("body"):
            continue
        for n in nodes(f["body"]):
            if isinstance(n, dict) and "Call" in n:
                func = n["Call"]["call"]["func"]
                if isinstance(func, dict) and func.get("Regular", {}).get("kind") == {"Fun": identifier}:
                    yield func["Regular"]["generics"]


def call_argument(generics, parent):
    assert len(generics["trait_refs"]) == 4
    base = generics["trait_refs"][3]
    original_into_id = parent["Untagged"]["kind"]["ParentClause"][0]["Untagged"]["trait_decl_ref"]["skip_binder"]["id"]
    into = base["Untagged"]["trait_decl_ref"]["skip_binder"]
    assert into["id"] == original_into_id
    iterator = copy.deepcopy(parent["Untagged"]["trait_decl_ref"])
    iterator["skip_binder"]["generics"] = copy.deepcopy(into["generics"])
    iterator["skip_binder"]["generics"]["types"] = [copy.deepcopy(into["generics"]["types"][i]) for i in (2, 1)]
    return {"Untagged": {"kind": {"ParentClause": [copy.deepcopy(base), 0]}, "trait_decl_ref": iterator}}


def check_projection(original, projected):
    function, parent = inventory(original)
    got = target(projected)
    assert len(got["generics"]["trait_clauses"]) == 5
    expected_clause = copy.deepcopy(function["generics"]["trait_clauses"][3])
    expected_clause["clause_id"] = 4
    expected_clause["trait_"] = copy.deepcopy(parent["Untagged"]["trait_decl_ref"])
    assert got["generics"]["trait_clauses"][4] == expected_clause
    restored = copy.deepcopy(projected)
    restored_function = target(restored)
    restored_function["generics"]["trait_clauses"].pop()
    assert not parent_refs(got["body"])
    direct = replacement(parent)
    count = sum(n == direct for n in nodes(got["body"]))
    assert count == 6
    restored_function["body"] = map_reference(got["body"], direct, parent)
    old_calls = list(calls(original, function["def_id"]))
    new_calls = list(calls(restored, function["def_id"]))
    assert len(old_calls) == len(new_calls)
    for old, new in zip(old_calls, new_calls):
        assert len(new["trait_refs"]) == 5
        assert new["trait_refs"][-1] == call_argument(old, parent)
        new["trait_refs"].pop()
    assert restored == original


def adapt(data, self_test=False):
    original = copy.deepcopy(data)
    function, parent = inventory(data)
    clause = copy.deepcopy(function["generics"]["trait_clauses"][3])
    clause["clause_id"] = 4
    clause["trait_"] = copy.deepcopy(parent["Untagged"]["trait_decl_ref"])
    function["generics"]["trait_clauses"].append(clause)
    function["body"] = map_reference(function["body"], parent, replacement(parent))
    call_count = 0
    for generics in calls(data, function["def_id"]):
        generics["trait_refs"].append(call_argument(generics, parent))
        call_count += 1
    check_projection(original, data)
    if self_test:
        mutations = []
        changed = copy.deepcopy(data)
        target(changed)["generics"]["trait_clauses"][4]["trait_"]["skip_binder"]["generics"]["types"].reverse()
        mutations.append(changed)
        changed = copy.deepcopy(data)
        target(changed)["body"]["Structured"]["body"]["statements"][0]["kind"] = "Nop"
        mutations.append(changed)
        changed = copy.deepcopy(data)
        target(changed)["signature"]["inputs"].pop()
        mutations.append(changed)
        changed = copy.deepcopy(data)
        target(changed)["generics"]["trait_clauses"][3]["clause_id"] = 7
        mutations.append(changed)
        if call_count:
            changed = copy.deepcopy(data)
            next(calls(changed, function["def_id"]))["trait_refs"][-1]["Untagged"]["kind"]["ParentClause"][1] = 1
            mutations.append(changed)
        for mutation in mutations:
            try:
                check_projection(original, mutation)
            except (AssertionError, IndexError, KeyError, TypeError):
                pass
            else:
                raise RuntimeError("The dictionary checker accepted a changed AST")
    digest = lambda value: hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"existing_parent_dictionary_checked": True, "projected_references": 6,
        "updated_call_sites": call_count, "public_argument_obligation": "IntoIterator.iteratorInst",
        "all_arithmetic_and_control_flow_unchanged": True, "complete_original_AST_restored": True,
        "rejected_mutations": (5 if call_count else 4) if self_test else 0,
        "original_sha256": digest(original), "adapted_sha256": digest(data)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    data = json.loads(args.source.read_text())
    report = adapt(data, args.self_test)
    args.destination.write_text(json.dumps(data, separators=(",", ":")))
    print(json.dumps(report, indent=2))
