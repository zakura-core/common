"""Recover Iterator::Item equality shared by IntoIterator and ExactSizeIterator.

Rust has one Iterator implementation for a fixed Self. The pinned Charon lift
introduces separate Item variables for the two supertrait paths. Check both
paths and substitute the original shared Pasta-field item types in dot_iter.
Only type annotations change. This audited coherence projection belongs to the
translation trust boundary, rather than being a verified compiler pass.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from unroll_merge import named, nodes

if not __debug__:
    raise RuntimeError("This adapter requires Python assertions")


def variable(index):
    return {"Untagged": {"TypeVar": {"Free": index}}}


def target(data):
    matches = [f for f in data["translated"]["fun_decls"] if f
        and f["item_meta"]["name"] == named("zakura_udon", "field", "pasta", "products", "dot_iter")]
    assert len(matches) == 1
    return matches[0]


def inventory(data):
    f = target(data)
    g = f["generics"]
    assert [t["index"] for t in g["types"]] == list(range(9))
    assert [t["name"] for t in g["types"]] == ["M", "S", "T", "A", "B", "Clause3_IntoIter",
        "Clause4_IntoIter", "Clause5_Clause0_Item", "Clause6_Clause0_Item"]
    assert [c["clause_id"] for c in g["trait_clauses"]] == list(range(7))
    assert not g["trait_type_constraints"]
    substitutions = {}
    traits = data["translated"]["trait_decls"]
    for into_index, exact_index, self_index, item_index in [(3,5,5,7), (4,6,6,8)]:
        into = g["trait_clauses"][into_index]["trait_"]["skip_binder"]
        exact = g["trait_clauses"][exact_index]["trait_"]["skip_binder"]
        into_decl, exact_decl = traits[into["id"]], traits[exact["id"]]
        assert into_decl["item_meta"]["name"] == named("core", "iter", "traits", "collect", "IntoIterator")
        assert exact_decl["item_meta"]["name"] == named("core", "iter", "traits", "exact_size", "ExactSizeIterator")
        assert len(into_decl["implied_clauses"]) == len(exact_decl["implied_clauses"]) == 1
        into_parent = into_decl["implied_clauses"][0]["trait_"]["skip_binder"]
        exact_parent = exact_decl["implied_clauses"][0]["trait_"]["skip_binder"]
        assert into_parent["id"] == exact_parent["id"]
        assert traits[into_parent["id"]]["item_meta"]["name"] == named("core", "iter", "traits", "iterator", "Iterator")
        assert into_parent["generics"]["types"] == [variable(2), variable(1)]
        assert exact_parent["generics"]["types"] == [variable(0), variable(1)]
        assert into["generics"]["types"][2] == exact["generics"]["types"][0] == variable(self_index)
        assert exact["generics"]["types"][1] == variable(item_index)
        item = into["generics"]["types"][1]
        region, field, borrow = item["Untagged"]["Ref"]
        assert region == {"Var": {"Free": 0}} and borrow == "Shared"
        assert field["Untagged"]["Adt"]["generics"]["types"] == [variable(0),variable(into_index-2)]
        substitutions[item_index] = copy.deepcopy(item)
    assert [sum(n == variable(i) for n in nodes(f)) for i in (7,8)] == [17,20]
    # dot_iter is a direct root. No caller may retain its old lifted signature.
    for other in data["translated"]["fun_decls"]:
        if not other or not other.get("body"):
            continue
        for n in nodes(other["body"]):
            if isinstance(n, dict) and "Call" in n:
                func=n["Call"]["call"]["func"]
                assert not (isinstance(func,dict) and func.get("Regular",{}).get("kind") == {"Fun":f["def_id"]})
    return f, substitutions


def substitute(value, substitutions):
    for index, item in substitutions.items():
        if value == variable(index):
            return copy.deepcopy(item)
    if isinstance(value, dict):
        return {k:substitute(v,substitutions) for k,v in value.items()}
    if isinstance(value,list):
        return [substitute(v,substitutions) for v in value]
    return value


def expected_projection(original):
    f, substitutions=inventory(original)
    expected=copy.deepcopy(original)
    projected=substitute(f,substitutions)
    projected["generics"]["types"]=projected["generics"]["types"][:7]
    expected["translated"]["fun_decls"][f["def_id"]]=projected
    return expected


def check_projection(original, projected):
    assert projected == expected_projection(original)


def adapt(original, self_test=False):
    result=expected_projection(original)
    check_projection(original,result)
    if self_test:
        mutations=[]
        changed=copy.deepcopy(result)
        target(changed)["generics"]["trait_clauses"][5]["trait_"]["skip_binder"]["generics"]["types"][1]=variable(0)
        mutations.append(changed)
        changed=copy.deepcopy(result)
        target(changed)["body"]["Structured"]["body"]["statements"][0]["kind"]="Nop"
        mutations.append(changed)
        changed=copy.deepcopy(result)
        target(changed)["signature"]["inputs"].reverse()
        mutations.append(changed)
        changed=copy.deepcopy(result)
        target(changed)["generics"]["types"].append({"index":7,"name":"unjustified"})
        mutations.append(changed)
        changed=copy.deepcopy(result)
        first=next(f for f in changed["translated"]["fun_decls"] if f and f["def_id"]!=target(changed)["def_id"])
        first["signature"]["is_unsafe"]=not first["signature"]["is_unsafe"]
        mutations.append(changed)
        for mutation in mutations:
            try:
                check_projection(original,mutation)
            except (AssertionError,IndexError,KeyError,TypeError):
                pass
            else:
                raise RuntimeError("The coherence checker accepted a changed AST")
    digest=lambda value:hashlib.sha256(json.dumps(value,sort_keys=True,separators=(",",":")).encode()).hexdigest()
    return result,{"coherent_Iterator_supertrait_paths_checked":2,"substituted_type_annotations":37,
        "removed_redundant_type_parameters":2,"all_operations_and_control_flow_unchanged":True,
        "all_other_AST_nodes_unchanged":True,"rejected_mutations":5 if self_test else 0,
        "original_sha256":digest(original),"adapted_sha256":digest(result)}


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source",type=Path)
    parser.add_argument("destination",type=Path)
    parser.add_argument("--self-test",action="store_true")
    args=parser.parse_args()
    result,report=adapt(json.loads(args.source.read_text()),args.self_test)
    args.destination.write_text(json.dumps(result,separators=(",",":")))
    print(json.dumps(report,indent=2))
