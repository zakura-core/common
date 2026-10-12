"""Replace the unreachable portable four-lane branch on the pinned AArch64 target.

The original guards require length < 32 and length >= 64 simultaneously.
Check their LLBC def-use chains and retain every other AST node unchanged.
The corresponding Lean dispatch lemma must also be checked. This adapter is
part of the translation trust boundary; it is not a verified compiler pass.
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


def branches(function):
    statements = function["body"]["Structured"]["body"]["statements"]
    for position in (47, 9, 9):
        statements = statements[position]["kind"]["Switch"]["branches"][1]["statements"]
    block_dispatch = statements
    portable_dispatch = statements[9]["kind"]["Switch"]["branches"][1]["statements"]
    dead = portable_dispatch[9]["kind"]["Switch"]["branches"][1]
    return block_dispatch, portable_dispatch, dead


def check_guards(data):
    translated = data["translated"]
    assert [item["key"] for item in translated["target_information"]] == ["aarch64-apple-darwin"]
    function = target(data)
    blocks = branches(function)
    assert [len(blocks[0]), len(blocks[1]), len(blocks[2]["statements"])] == [72, 69, 129]
    for block, operator in zip(blocks[:2], ("Ge", "Lt")):
        ref_dest, ref_value = block[5]["kind"]["Assign"]
        assert ref_value["Ref"]["kind"] == "Shared"
        assert ref_value["Ref"]["place"]["kind"]["Projection"][0]["kind"] == {"Local": 1}
        assert ref_value["Ref"]["place"]["kind"]["Projection"][1] == "Deref"
        call = block[6]["kind"]["Call"]["call"]
        callee = translated["fun_decls"][call["func"]["Regular"]["kind"]["Fun"]]
        assert callee["item_meta"]["name"] == named("core", "slice") + [
            {"Impl": callee["item_meta"]["name"][2]["Impl"]}, {"Ident": ["len", 0]}]
        assert len(call["args"]) == 1 and call["args"][0]["Move"] == ref_dest
        condition, calculation = block[8]["kind"]["Assign"]
        op, left, right = calculation["BinaryOp"]
        assert op == operator and left["Move"] == call["dest"]
        switch = block[9]["kind"]["Switch"]
        assert switch["data"] == {"scrutinee": {"Value": {"Move": condition}},
            "branches": [[{"Untagged": [{"Bool": False}, {"Untagged": {"Scalar": "Bool"}}]}, 1]],
            "fallback": 0}
        assert switch["branches"][0]["statements"] == []
        if operator == "Ge":
            assert right["Const"]["Untagged"][0] == {"Integer": {"Unsigned": ["Usize", "32"]}}
        else:
            global_id = right["Copy"]["kind"]["Global"]["id"]
            declaration = translated["global_decls"][global_id]
            assert declaration["item_meta"]["name"][-1] == {"Ident": ["LANE_THRESHOLD", 0]}
            initializer = declaration["value"]["Untagged"][0]["Call"][0]["kind"]["Fun"]
            body = translated["fun_decls"][initializer]["body"]["Structured"]["body"]["statements"]
            assert len(body) == 3 and body[0]["kind"] == {"StorageLive": 0} and body[2]["kind"] == "Return"
            destination, value = body[1]["kind"]["Assign"]
            assert destination["kind"] == {"Local": 0}
            assert value["Use"][0]["Const"]["Untagged"][0] == {
                "Integer": {"Unsigned": ["Usize", "64"]}}
    return function, blocks[2]


def panic_statement(function):
    statements = function["body"]["Structured"]["body"]["statements"]
    panic = statements[33]["kind"]["Switch"]["branches"][1]["statements"][-1]
    assert "Panic" in panic["kind"]
    return panic


def check_projection(original, projected):
    function, _ = check_guards(original)
    new_dead = branches(target(projected))[2]
    assert new_dead["statements"] == [panic_statement(function)]
    restored = copy.deepcopy(projected)
    branches(target(restored))[2]["statements"] = copy.deepcopy(branches(function)[2]["statements"])
    assert restored == original


def adapt(data, self_test=False):
    original = copy.deepcopy(data)
    function, dead = check_guards(data)
    dead["statements"] = [copy.deepcopy(panic_statement(function))]
    check_projection(original, data)
    if self_test:
        changed_guard = copy.deepcopy(data)
        branches(target(changed_guard))[0][8]["kind"]["Assign"][1]["BinaryOp"][0] = "Le"
        changed_source = copy.deepcopy(data)
        branches(target(changed_source))[1][5]["kind"]["Assign"][1]["Ref"]["place"]["kind"]["Projection"][0]["kind"] = {"Local": 2}
        changed_dead = copy.deepcopy(data)
        branches(target(changed_dead))[2]["statements"] = []
        changed_prefix = copy.deepcopy(data)
        target(changed_prefix)["body"]["Structured"]["body"]["statements"][0]["kind"] = "Nop"
        for mutation in (changed_guard, changed_source, changed_dead, changed_prefix):
            try:
                check_projection(original, mutation)
            except AssertionError:
                pass
            else:
                raise RuntimeError("The projection checker accepted a changed AST")
    digest = lambda value: hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"target": "aarch64-apple-darwin", "dead_path_conditions": ["length < 32", "length >= 64"],
            "guards_and_def_use_checked": True, "all_other_AST_nodes_preserved": True,
            "replacement": "existing panic", "rejected_mutations": 4 if self_test else 0,
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
