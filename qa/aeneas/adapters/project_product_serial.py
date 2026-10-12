"""Select the unchanged portable serial slice arm, for lengths 4 through 63.

Every guard and retained instruction is checked against the original LLBC.
Other arms end in the routine's existing panic. This is a partial model:
the Lean contract must discharge its length preconditions. The adapter is
part of the translation trust boundary, not a verified compiler pass.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from project_product_short import check_scope, panic_statement, short_dispatch, target

if not __debug__:
    raise RuntimeError("This adapter requires Python assertions")


def scoped_branches(data):
    assert [t["key"] for t in data["translated"]["target_information"]] == ["x86_64-apple-darwin"]
    function = check_scope(data)
    statements = function["body"]["Structured"]["body"]["statements"]
    empty = statements[47]["kind"]["Switch"]["branches"]
    singleton = empty[1]["statements"][9]["kind"]["Switch"]["branches"]
    short = short_dispatch(function)[9]["kind"]["Switch"]["branches"]
    serial = short[1]["statements"]
    assert len(serial) == 69
    reference, value = serial[5]["kind"]["Assign"]
    assert value["Ref"]["kind"] == "Shared"
    assert value["Ref"]["place"]["kind"]["Projection"][0]["kind"] == {"Local": 1}
    call = serial[6]["kind"]["Call"]["call"]
    callee = data["translated"]["fun_decls"][call["func"]["Regular"]["kind"]["Fun"]]
    assert callee["item_meta"]["name"][-1] == {"Ident": ["len", 0]}
    assert call["args"] == [{"Move": reference}]
    condition, calculation = serial[8]["kind"]["Assign"]
    operator, left, right = calculation["BinaryOp"]
    assert operator == "Lt" and left == {"Move": call["dest"]}
    global_id = right["Copy"]["kind"]["Global"]["id"]
    declaration = data["translated"]["global_decls"][global_id]
    assert declaration["item_meta"]["name"][-1] == {"Ident": ["LANE_THRESHOLD", 0]}
    initializer = declaration["value"]["Untagged"][0]["Call"][0]["kind"]["Fun"]
    body = data["translated"]["fun_decls"][initializer]["body"]["Structured"]["body"]["statements"]
    assert len(body) == 3 and body[0]["kind"] == {"StorageLive": 0} and body[2]["kind"] == "Return"
    assert body[1]["kind"]["Assign"][0]["kind"] == {"Local": 0}
    assert body[1]["kind"]["Assign"][1]["Use"][0]["Const"]["Untagged"][0] == {
        "Integer": {"Unsigned": ["Usize", "64"]}}
    switch = serial[9]["kind"]["Switch"]
    assert switch["data"]["scrutinee"] == {"Value": {"Move": condition}}
    assert switch["branches"][0]["statements"] == []
    assert switch["data"]["branches"] == [[
        {"Untagged": [{"Bool": False}, {"Untagged": {"Scalar": "Bool"}}]}, 1]]
    assert switch["data"]["fallback"] == 0
    return function, [empty[0], singleton[0], short[0], switch["branches"][1]]


def check_projection(original, projected):
    function, original_branches = scoped_branches(original)
    # Locate the selected branches without requiring their original contents.
    new_function = target(projected)
    statements = new_function["body"]["Structured"]["body"]["statements"]
    empty = statements[47]["kind"]["Switch"]["branches"]
    singleton = empty[1]["statements"][9]["kind"]["Switch"]["branches"]
    short = short_dispatch(new_function)[9]["kind"]["Switch"]["branches"]
    serial = short[1]["statements"][9]["kind"]["Switch"]["branches"]
    selected = [empty[0], singleton[0], short[0], serial[1]]
    assert all(b["statements"] == [panic_statement(function)] for b in selected)
    restored = copy.deepcopy(projected)
    restored_function = target(restored)
    restored_top = restored_function["body"]["Structured"]["body"]["statements"]
    restored_empty = restored_top[47]["kind"]["Switch"]["branches"]
    restored_singleton = restored_empty[1]["statements"][9]["kind"]["Switch"]["branches"]
    restored_short = short_dispatch(restored_function)[9]["kind"]["Switch"]["branches"]
    restored_serial = restored_short[1]["statements"][9]["kind"]["Switch"]["branches"]
    for old, new in zip(original_branches, [restored_empty[0], restored_singleton[0],
                                           restored_short[0], restored_serial[1]]):
        new["statements"] = copy.deepcopy(old["statements"])
    for old, new in zip(original["translated"]["fun_decls"], restored["translated"]["fun_decls"]):
        if not old:
            assert new is None
        elif old["def_id"] != function["def_id"]:
            assert new["item_meta"]["is_local"] is False and new["item_meta"]["started_from"] is False
            for field in ("is_local", "started_from"):
                new["item_meta"][field] = old["item_meta"][field]
    assert restored == original


def adapt(data, self_test=False):
    original = copy.deepcopy(data)
    function, branches = scoped_branches(data)
    for branch in branches:
        branch["statements"] = [copy.deepcopy(panic_statement(function))]
    for other in data["translated"]["fun_decls"]:
        if other and other["def_id"] != function["def_id"]:
            other["item_meta"]["is_local"] = False
            other["item_meta"]["started_from"] = False
    check_projection(original, data)
    if self_test:
        mutations = []
        changed = copy.deepcopy(data)
        short_dispatch(target(changed))[8]["kind"]["Assign"][1]["BinaryOp"][0] = "Lt"
        mutations.append(changed)
        changed = copy.deepcopy(data)
        target(changed)["signature"]["inputs"].pop()
        mutations.append(changed)
        changed = copy.deepcopy(data)
        serial = short_dispatch(target(changed))[9]["kind"]["Switch"]["branches"][1]["statements"]
        serial[30]["kind"]["Loop"]["statements"][-1]["kind"] = "Nop"
        mutations.append(changed)
        changed = copy.deepcopy(data)
        serial = short_dispatch(target(changed))[9]["kind"]["Switch"]["branches"][1]["statements"]
        serial[9]["kind"]["Switch"]["branches"][1]["statements"] = []
        mutations.append(changed)
        for mutation in mutations:
            try:
                check_projection(original, mutation)
            except (AssertionError, KeyError, IndexError):
                pass
            else:
                raise RuntimeError("The serial-path checker accepted a changed AST")
    digest = lambda value: hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"scope": "4 <= lhs.length < 64", "target": "x86_64-apple-darwin",
            "partial_model": True, "retained_branch_arithmetic_unchanged": True,
            "signatures_types_and_globals_unchanged": True, "complete_original_AST_restored": True,
            "rejected_mutations": 4 if self_test else 0,
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
