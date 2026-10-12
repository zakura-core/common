"""Expand the fixed eight-word ProductSum merge without changing its arithmetic.

The pinned Aeneas translator cannot reconstruct the nested mutable/shared Zip
borrow at a loop join. Preserve nine copies of the actual loop: eight payloads
and the iterator exhaustion check. A false assertion bounds the expansion;
the Lean merge equivalence proof discharges that unreachable branch.

This is a translation adapter, not a verified compiler transformation. An
independent structural checker certifies each copied instruction and branch.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("This adapter requires Python assertions")


def nodes(value):
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def named(*parts):
    return [{"Ident": [part, 0]} for part in parts]


def strip_ids(value):
    """Ignore only statement/block IDs, keeping every other AST field."""
    value = copy.deepcopy(value)
    for node in nodes(value):
        if isinstance(node, dict) and "span" in node and ("kind" in node or "statements" in node):
            node.pop("id", None)
    return value


def sequence(statements, normal, on_break, on_continue):
    if not statements:
        return copy.deepcopy(normal)
    statement = copy.deepcopy(statements[0])
    kind = statement["kind"]
    if kind == {"Break": 0}:
        return copy.deepcopy(on_break)
    if kind == {"Continue": 0}:
        return copy.deepcopy(on_continue)
    rest = sequence(statements[1:], normal, on_break, on_continue)
    if isinstance(kind, dict) and "Switch" in kind:
        for branch in kind["Switch"]["branches"]:
            branch["statements"] = sequence(branch["statements"], rest, on_break, on_continue)
        return [statement]
    return [statement] + rest


def check_expansion(expanded, loop, tail, guard, remaining=9):
    """Check the pinned loop shape independently of CPS construction."""
    if remaining == 0:
        assert strip_ids(expanded) == strip_ids([guard] + tail)
        return
    # Every iteration retains the actual next call and discriminant switch.
    assert len(expanded) == 8
    assert strip_ids(expanded[:7]) == strip_ids(loop["statements"][:7])
    actual = expanded[7]["kind"]["Switch"]
    expected = loop["statements"][7]["kind"]["Switch"]
    assert strip_ids(actual["data"]) == strip_ids(expected["data"])
    assert len(actual["branches"]) == 2
    for got, old in zip(actual["branches"], expected["branches"]):
        assert strip_ids({**got, "statements": []}) == strip_ids({**old, "statements": []})
    # None runs exactly the original post-loop continuation; Some retains
    # every payload instruction, then reaches the next copied iteration.
    assert strip_ids(actual["branches"][0]["statements"]) == strip_ids(tail)
    payload = loop["statements"][8:-1]
    some = actual["branches"][1]["statements"]
    assert strip_ids(some[:len(payload)]) == strip_ids(payload)
    check_expansion(some[len(payload):], loop, tail, guard, remaining - 1)


def adapt(data, self_test=False):
    original = copy.deepcopy(data)
    translated = data["translated"]
    sums = [decl for decl in translated["type_decls"] if decl
            and decl["item_meta"]["name"] == named("zakura_udon", "field", "pasta", "products", "ProductSum")]
    assert len(sums) == 1
    fields = sums[0]["kind"]["Struct"]
    assert [field["name"] for field in fields] == ["wide", "carry", "marker"]
    word = {"Untagged": {"Scalar": {"Integer": {"Unsigned": "U64"}}}}
    wide = fields[0]["ty"]["Untagged"]["Array"]
    assert wide[0] == word and wide[2] is None
    assert wide[1]["Untagged"][0] == {"Integer": {"Unsigned": ["Usize", "8"]}}
    assert fields[1]["ty"] == word
    functions = [decl for decl in translated["fun_decls"] if decl
                 and decl["item_meta"]["name"][:4] == named("zakura_udon", "field", "pasta", "products")
                 and decl["item_meta"]["name"][-1] == {"Ident": ["merge", 0]}]
    assert len(functions) == 1
    function = functions[0]
    inputs = function["signature"]["inputs"]
    assert len(inputs) == 2
    for argument, borrow in zip(inputs, ["Mut", "Shared"]):
        reference = argument["Untagged"]["Ref"]
        assert reference[2] == borrow
        assert reference[1]["Untagged"]["Adt"]["id"] == sums[0]["def_id"]
    body = function["body"]["Structured"]["body"]
    statements = body["statements"]
    positions = [i for i, statement in enumerate(statements)
                 if isinstance(statement["kind"], dict) and "Loop" in statement["kind"]]
    assert positions == [23]
    position = positions[0]
    loop_statement = copy.deepcopy(statements[position])
    loop = loop_statement["kind"]["Loop"]
    tail = copy.deepcopy(statements[position + 1:])
    assert len(tail) == 40 and tail[-1]["kind"] == "Return"
    assert len(loop["statements"]) == 43
    switch = loop["statements"][7]["kind"]["Switch"]
    assert len(switch["branches"]) == 2
    assert [branch["statements"] for branch in switch["branches"]] == \
        [[next(statement for statement in switch["branches"][0]["statements"]
               if statement["kind"] == {"Break": 0})], []]
    assert loop["statements"][-1]["kind"] == {"Continue": 0}
    assert [case[0]["Untagged"][0]["Discriminant"][1] for case in switch["data"]["branches"]] == [0, 1]
    assert switch["data"]["fallback"] is None
    flow = [node["kind"] for node in nodes(loop) if isinstance(node, dict) and "kind" in node
            and isinstance(node["kind"], dict) and any(key in node["kind"] for key in ["Loop", "Break", "Continue", "Switch"])]
    assert len(flow) == 3
    for index, name in [(5, named("core", "iter", "adapters", "zip")),
                        (19, named("zakura_udon", "field", "pasta", "word", "adc"))]:
        identifier = loop["statements"][index]["kind"]["Call"]["call"]["func"]["Regular"]["kind"]["Fun"]
        actual_name = translated["fun_decls"][identifier]["item_meta"]["name"]
        assert actual_name[:len(name)] == name
    assertion = copy.deepcopy(next(node["kind"]["Assert"] for node in nodes(translated["fun_decls"])
                                  if isinstance(node, dict) and isinstance(node.get("kind"), dict)
                                  and "Assert" in node["kind"]))
    assertion["assert"]["cond"] = {"Const": {"Untagged": [{"Bool": False}, {"Untagged": {"Scalar": "Bool"}}]}}
    assertion["assert"]["expected"] = True
    guard = {"span": function["item_meta"]["span"], "id": 0,
             "kind": {"Assert": assertion}, "comments_before": []}

    def expand(remaining):
        if remaining == 0:
            return [copy.deepcopy(guard)] + copy.deepcopy(tail)
        return sequence(loop["statements"], [], tail, expand(remaining - 1))

    expanded = expand(9)
    check_expansion(expanded, loop, tail, guard)
    if self_test:
        # These mutations attack the independent checker, not the generator.
        mutations = []
        changed_payload = copy.deepcopy(expanded)
        changed_payload[7]["kind"]["Switch"]["branches"][1]["statements"][11]["kind"] = "Nop"
        mutations.append(changed_payload)
        changed_exit = copy.deepcopy(expanded)
        changed_exit[7]["kind"]["Switch"]["branches"][0]["statements"].pop()
        mutations.append(changed_exit)
        mutations.append(expand(8))
        changed_guard = copy.deepcopy(expanded)
        last = changed_guard
        for _ in range(9):
            last = last[7]["kind"]["Switch"]["branches"][1]["statements"][34:]
        last[0]["kind"]["Assert"]["assert"]["cond"]["Const"]["Untagged"][0] = {"Bool": True}
        mutations.append(changed_guard)
        for mutation in mutations:
            try:
                check_expansion(mutation, loop, tail, guard)
            except AssertionError:
                pass
            else:
                raise RuntimeError("The independent checker accepted a changed expansion")
    body["statements"] = copy.deepcopy(statements[:position]) + expanded
    next_id = max(node["id"] for node in nodes(original["translated"])
                  if isinstance(node, dict) and isinstance(node.get("id"), int)) + 1
    for node in nodes(body):
        if isinstance(node, dict) and "id" in node and "span" in node and ("kind" in node or "statements" in node):
            node["id"] = next_id
            next_id += 1
    check_expansion(body["statements"][position:], loop, tail, guard)
    assert strip_ids(body["statements"][:position]) == strip_ids(statements[:position])
    # Restore the checked expansion to its input loop, and compare the entire
    # AST so no signature, local, type, other routine or continuation drifts.
    restored = copy.deepcopy(data)
    restored["translated"]["fun_decls"][function["def_id"]]["body"] = \
        original["translated"]["fun_decls"][function["def_id"]]["body"]
    assert restored == original
    digest = lambda value: hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"expanded_merge_loops": 1, "payload_bound": 8, "iterator_checks": 9,
            "copied_ADC_calls": 9, "unreachable_guard": True,
            "independent_structural_check": True, "complete_original_AST_restored": True,
            "original_sha256": digest(original), "adapted_sha256": digest(data),
            "original_loop_sha256": digest(loop), "rejected_mutations": 4 if self_test else 0}


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
