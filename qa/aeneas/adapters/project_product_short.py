"""Scope the slice method to its unchanged paths for lengths zero through three.

Replace only the outside-scope branch with an existing panic and deselect
unreferenced functions. The checked theorem must require lhs.length <= 3.
This is an explicit partial model, not a model of the long-slice paths.
All retained arithmetic and every function signature are preserved.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from unroll_merge import named

if not __debug__:
    raise RuntimeError("This adapter requires Python assertions")


def target(data):
    matches = [f for f in data["translated"]["fun_decls"] if f
        and f["item_meta"]["name"][:4] == named("zakura_udon", "field", "pasta", "products")
        and f["item_meta"]["name"][-1] == {"Ident": ["sum_of_products_slice", 0]}]
    assert len(matches) == 1
    return matches[0]


def short_dispatch(function):
    statements = function["body"]["Structured"]["body"]["statements"]
    for position in (47, 9):
        statements = statements[position]["kind"]["Switch"]["branches"][1]["statements"]
    return statements


def panic_statement(function):
    statements = function["body"]["Structured"]["body"]["statements"]
    panic = statements[33]["kind"]["Switch"]["branches"][1]["statements"][-1]
    assert "Panic" in panic["kind"]
    return panic


def check_scope(data):
    function = target(data)
    block = short_dispatch(function)
    assert len(block) == 77
    ref_dest, ref_value = block[5]["kind"]["Assign"]
    assert ref_value["Ref"]["kind"] == "Shared"
    assert ref_value["Ref"]["place"]["kind"]["Projection"][0]["kind"] == {"Local": 1}
    assert ref_value["Ref"]["place"]["kind"]["Projection"][1] == "Deref"
    call = block[6]["kind"]["Call"]["call"]
    callee = data["translated"]["fun_decls"][call["func"]["Regular"]["kind"]["Fun"]]
    assert callee["item_meta"]["name"][:2] == named("core", "slice")
    assert callee["item_meta"]["name"][-1] == {"Ident": ["len", 0]}
    assert len(call["args"]) == 1 and call["args"][0]["Move"] == ref_dest
    condition, calculation = block[8]["kind"]["Assign"]
    op, left, right = calculation["BinaryOp"]
    assert op == "Le" and left["Move"] == call["dest"]
    assert right["Const"]["Untagged"][0] == {"Integer": {"Unsigned": ["Usize", "3"]}}
    switch = block[9]["kind"]["Switch"]
    assert switch["data"] == {"scrutinee": {"Value": {"Move": condition}},
        "branches": [[{"Untagged": [{"Bool": False}, {"Untagged": {"Scalar": "Bool"}}]}, 1]],
        "fallback": 0}
    assert switch["branches"][0]["statements"] == []
    return function


def check_projection(original, projected):
    function = check_scope(original)
    new_function = target(projected)
    old_dead = short_dispatch(function)[9]["kind"]["Switch"]["branches"][1]
    new_dead = short_dispatch(new_function)[9]["kind"]["Switch"]["branches"][1]
    assert new_dead["statements"] == [panic_statement(function)]
    restored = copy.deepcopy(projected)
    short_dispatch(target(restored))[9]["kind"]["Switch"]["branches"][1]["statements"] = \
        copy.deepcopy(old_dead["statements"])
    for old, got in zip(original["translated"]["fun_decls"], restored["translated"]["fun_decls"]):
        if not old:
            assert got is None
            continue
        if old["def_id"] != function["def_id"]:
            assert got["item_meta"]["is_local"] is False and got["item_meta"]["started_from"] is False
            for field in ("is_local", "started_from"):
                got["item_meta"][field] = old["item_meta"][field]
    assert restored == original


def adapt(data, self_test=False):
    original = copy.deepcopy(data)
    function = check_scope(data)
    short_dispatch(function)[9]["kind"]["Switch"]["branches"][1]["statements"] = \
        [copy.deepcopy(panic_statement(function))]
    deselected = []
    for other in data["translated"]["fun_decls"]:
        if other and other["def_id"] != function["def_id"]:
            for field in ("is_local", "started_from"):
                other["item_meta"][field] = False
            deselected.append(other["def_id"])
    check_projection(original, data)
    if self_test:
        changed_guard = copy.deepcopy(data)
        short_dispatch(target(changed_guard))[8]["kind"]["Assign"][1]["BinaryOp"][0] = "Lt"
        changed_prefix = copy.deepcopy(data)
        target(changed_prefix)["body"]["Structured"]["body"]["statements"][0]["kind"] = "Nop"
        changed_outside = copy.deepcopy(data)
        short_dispatch(target(changed_outside))[9]["kind"]["Switch"]["branches"][1]["statements"] = []
        changed_signature = copy.deepcopy(data)
        target(changed_signature)["signature"]["inputs"].pop()
        for mutation in (changed_guard, changed_prefix, changed_outside, changed_signature):
            try:
                check_projection(original, mutation)
            except AssertionError:
                pass
            else:
                raise RuntimeError("The partial-model checker accepted a changed AST")
    digest = lambda value: hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"scope": "lhs.length <= 3", "outside_scope": "existing panic",
            "partial_model": True, "retained_branch_arithmetic_unchanged": True,
            "signatures_types_and_globals_unchanged": True,
            "deselected_function_metadata": deselected,
            "complete_original_AST_restored": True, "rejected_mutations": 4 if self_test else 0,
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
