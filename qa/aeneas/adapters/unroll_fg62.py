"""Expand the bounded signed-62 f/g update loop without changing its payload.

The pinned translator cannot join this loop's mutable borrows. There are at
most four payloads and a fifth iterator call checks exhaustion. Keep every
original instruction and the original post-loop continuation, adding only an
unreachable failure guard after the fifth successful iterator call. The Lean
contracts must discharge that guard for all active lengths 1 through 5.

This structural adapter is part of the translation trust boundary.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from unroll_merge import check_expansion, named, nodes, sequence, strip_ids

if not __debug__:
    raise RuntimeError("This adapter requires Python assertions")


def adapt(data, self_test=False):
    original = copy.deepcopy(data)
    translated = data["translated"]
    functions = [decl for decl in translated["fun_decls"] if decl
                 and decl["item_meta"]["name"] ==
                 named("zakura_udon", "field", "pasta", "safegcd", "update_fg_62_var")]
    assert len(functions) == 1
    function = functions[0]
    assert len(function["signature"]["inputs"]) == 4
    statements = function["body"]["Structured"]["body"]["statements"]
    positions = [i for i, statement in enumerate(statements)
                 if isinstance(statement["kind"], dict) and "Loop" in statement["kind"]]
    assert positions == [151]
    position = positions[0]
    loop = copy.deepcopy(statements[position]["kind"]["Loop"])
    tail = copy.deepcopy(statements[position + 1:])
    assert len(loop["statements"]) == 160
    assert len(tail) == 101 and tail[-1]["kind"] == "Return"
    assert loop["statements"][-1]["kind"] == {"Continue": 0}
    switch = loop["statements"][7]["kind"]["Switch"]
    assert [branch["statements"] for branch in switch["branches"]] == [
        [next(statement for statement in switch["branches"][0]["statements"]
              if statement["kind"] == {"Break": 0})], []]
    assert switch["data"]["fallback"] is None
    flow = [node["kind"] for node in nodes(loop) if isinstance(node, dict)
            and isinstance(node.get("kind"), dict)
            and any(key in node["kind"] for key in ["Loop", "Switch", "Break", "Continue"])]
    assert len(flow) == 3
    span = copy.deepcopy(function["item_meta"]["span"])
    assertion = {
        "assert": {"cond": {
            "Const": {"Untagged": [{"Bool": False}, {"Untagged": {"Scalar": "Bool"}}]}},
            "expected": True, "check_kind": None},
        "on_failure": {"Panic": named("core", "panicking", "panic")},
        "on_unwind": {"span": span, "id": 0, "statements": [
            {"span": span, "id": 0, "kind": "UnwindResume", "comments_before": []}]}}
    guard = {"span": function["item_meta"]["span"], "id": 0,
             "kind": {"Assert": assertion}, "comments_before": []}

    def expand(remaining):
        if remaining == 0:
            return [copy.deepcopy(guard)] + copy.deepcopy(tail)
        return sequence(loop["statements"], [], tail, expand(remaining - 1))

    expanded = expand(5)
    check_expansion(expanded, loop, tail, guard, remaining=5)
    if self_test:
        changed_payload = copy.deepcopy(expanded)
        payload = changed_payload[7]["kind"]["Switch"]["branches"][1]["statements"]
        index = next(i for i, statement in enumerate(loop["statements"][8:-1])
                     if statement["kind"] != "Nop")
        payload[index]["kind"] = "Nop"
        changed_exit = copy.deepcopy(expanded)
        changed_exit[7]["kind"]["Switch"]["branches"][0]["statements"].pop()
        changed_guard = copy.deepcopy(expanded)
        last = changed_guard
        for _ in range(5):
            last = last[7]["kind"]["Switch"]["branches"][1]["statements"][151:]
        last[0]["kind"]["Assert"]["assert"]["cond"]["Const"]["Untagged"][0] = {"Bool": True}
        for mutation in [changed_payload, changed_exit, expand(4), changed_guard]:
            try:
                check_expansion(mutation, loop, tail, guard, remaining=5)
            except AssertionError:
                pass
            else:
                raise RuntimeError("The checker accepted a changed f/g expansion")

    body = function["body"]["Structured"]["body"]
    body["statements"] = copy.deepcopy(statements[:position]) + expanded
    next_id = max(node["id"] for node in nodes(original["translated"])
                  if isinstance(node, dict) and isinstance(node.get("id"), int)) + 1
    for node in nodes(body):
        if isinstance(node, dict) and "id" in node and "span" in node \
                and ("kind" in node or "statements" in node):
            node["id"] = next_id
            next_id += 1
    check_expansion(body["statements"][position:], loop, tail, guard, remaining=5)
    assert strip_ids(body["statements"][:position]) == strip_ids(statements[:position])
    restored = copy.deepcopy(data)
    restored["translated"]["fun_decls"][function["def_id"]]["body"] = \
        original["translated"]["fun_decls"][function["def_id"]]["body"]
    assert restored == original
    digest = lambda value: hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"expanded_fg_loops": 1, "payload_bound": 4, "iterator_checks": 5,
            "unreachable_guard": True, "independent_structural_check": True,
            "complete_original_AST_restored": True, "original_sha256": digest(original),
            "adapted_sha256": digest(data), "original_loop_sha256": digest(loop),
            "rejected_mutations": 4 if self_test else 0}


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
