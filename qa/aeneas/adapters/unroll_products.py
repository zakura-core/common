"""Expand the three fixed mutable Zip loops in the public product-sum slice.

The payloads are copied from the pinned local-crate LLBC, including every
checked arithmetic operation. Each expansion includes one final iterator
exhaustion check and an assertion that the bound was sufficient. Lean proofs
must discharge that assertion. This is a structurally audited translation
adapter, not a verified compiler transformation.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from unroll_merge import check_expansion, named, nodes, sequence, strip_ids

if not __debug__:
    raise RuntimeError("This adapter requires Python assertions")


def adapt(data, self_test=False, short_only=False):
    original = copy.deepcopy(data)
    declarations = data["translated"]["fun_decls"]
    targets = {
        # source line: (routine, payload bound, loop length, tail length, call index, callee)
        301: ("merge", 8, 43, 40, 19, "adc"),
        496: ("sum_of_products_slice", 8, 43, 17, 19, "adc"),
        530: ("sum_of_products_slice", 4, 32, 9, 21, "add_product_inner"),
    }
    if short_only:
        targets = {496: targets[496]}
    found = []
    for function in declarations:
        if not function or not function.get("body"):
            continue
        name = function["item_meta"]["name"]
        if name[:4] != named("zakura_udon", "field", "pasta", "products"):
            continue
        if name[-1] not in [{"Ident": ["merge", 0]}, {"Ident": ["sum_of_products_slice", 0]}]:
            continue
        for block in nodes(function["body"]):
            if not isinstance(block, dict) or "statements" not in block:
                continue
            for position, statement in enumerate(block["statements"]):
                kind = statement["kind"]
                if not isinstance(kind, dict) or "Loop" not in kind:
                    continue
                line = statement["span"]["Untagged"]["data"]["beg"]["line"]
                if line in targets:
                    found.append((line, function["def_id"], block, position))
    assert sorted(item[0] for item in found) == sorted(targets)
    assertion = copy.deepcopy(next(node["kind"]["Assert"] for node in nodes(declarations)
        if isinstance(node, dict) and isinstance(node.get("kind"), dict) and "Assert" in node["kind"]))
    assertion["assert"]["cond"] = {
        "Const": {"Untagged": [{"Bool": False}, {"Untagged": {"Scalar": "Bool"}}]}}
    assertion["assert"]["expected"] = True
    reports = []
    for line, identifier, block, position in found:
        routine, bound, loop_length, tail_length, call_index, callee = targets[line]
        function = declarations[identifier]
        assert function["item_meta"]["name"][-1] == {"Ident": [routine, 0]}
        statements = copy.deepcopy(block["statements"])
        loop = statements[position]["kind"]["Loop"]
        tail = statements[position + 1:]
        assert len(loop["statements"]) == loop_length and len(tail) == tail_length
        assert loop["statements"][-1]["kind"] == {"Continue": 0}
        if routine == "merge":
            assert position == 24 and tail[-1]["kind"] == "Return"
        switch = loop["statements"][7]["kind"]["Switch"]
        assert [branch["statements"] for branch in switch["branches"]] == [
            [next(s for s in switch["branches"][0]["statements"] if s["kind"] == {"Break": 0})], []]
        assert [case[0]["Untagged"][0]["Discriminant"][1]
                for case in switch["data"]["branches"]] == [0, 1]
        assert switch["data"]["fallback"] is None
        flow = [node["kind"] for node in nodes(loop) if isinstance(node, dict)
                and isinstance(node.get("kind"), dict)
                and any(key in node["kind"] for key in ["Loop", "Break", "Continue", "Switch"])]
        assert len(flow) == 3
        for index, prefix in [(5, named("core", "iter", "adapters", "zip")),
                              (call_index, named("zakura_udon", "field", "pasta"))]:
            call = loop["statements"][index]["kind"]["Call"]["call"]["func"]["Regular"]["kind"]["Fun"]
            actual = declarations[call]["item_meta"]["name"]
            assert actual[:len(prefix)] == prefix
            if index == call_index:
                assert actual[-1] == {"Ident": [callee, 0]}
        guard = {"span": copy.deepcopy(function["item_meta"]["span"]), "id": 0,
                 "kind": {"Assert": copy.deepcopy(assertion)}, "comments_before": []}

        def expand(remaining):
            if remaining == 0:
                return [copy.deepcopy(guard)] + copy.deepcopy(tail)
            return sequence(loop["statements"], [], tail, expand(remaining - 1))

        expanded = expand(bound + 1)
        check_expansion(expanded, loop, tail, guard, bound + 1)
        if self_test:
            mutations = []
            payload = copy.deepcopy(expanded)
            payload[7]["kind"]["Switch"]["branches"][1]["statements"][0]["kind"] = "Nop"
            mutations.append(payload)
            exit_branch = copy.deepcopy(expanded)
            exit_branch[7]["kind"]["Switch"]["branches"][0]["statements"].pop()
            mutations.append(exit_branch)
            mutations.append(expand(bound))
            changed_guard = copy.deepcopy(expanded)
            last = changed_guard
            for _ in range(bound + 1):
                last = last[7]["kind"]["Switch"]["branches"][1]["statements"][loop_length - 9:]
            last[0]["kind"]["Assert"]["assert"]["cond"]["Const"]["Untagged"][0] = {"Bool": True}
            mutations.append(changed_guard)
            for mutation in mutations:
                try:
                    check_expansion(mutation, loop, tail, guard, bound + 1)
                except AssertionError:
                    pass
                else:
                    raise RuntimeError("The independent checker accepted a changed product expansion")
        block["statements"] = statements[:position] + expanded
        assert strip_ids(block["statements"][:position]) == strip_ids(statements[:position])
        check_expansion(block["statements"][position:], loop, tail, guard, bound + 1)
        reports.append({"routine": routine, "source_line": line, "payload_bound": bound,
                        "iterator_checks": bound + 1,
                        "rejected_mutations": 4 if self_test else 0})
    next_id = max(node["id"] for node in nodes(original["translated"])
                  if isinstance(node, dict) and isinstance(node.get("id"), int)) + 1
    changed_functions = {identifier for _, identifier, _, _ in found}
    for identifier in changed_functions:
        for node in nodes(declarations[identifier]["body"]):
            if isinstance(node, dict) and "id" in node and "span" in node and (
                    "kind" in node or "statements" in node):
                node["id"] = next_id
                next_id += 1
    restored = copy.deepcopy(data)
    for identifier in changed_functions:
        restored["translated"]["fun_decls"][identifier]["body"] = \
            original["translated"]["fun_decls"][identifier]["body"]
    assert restored == original
    digest = lambda value: hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"expanded_loops": reports, "independent_structural_check": True,
            "complete_original_AST_restored": True, "unreachable_guards": True,
            "original_sha256": digest(original), "adapted_sha256": digest(data)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--short-only", action="store_true")
    args = parser.parse_args()
    data = json.loads(args.source.read_text())
    report = adapt(data, args.self_test, args.short_only)
    args.destination.write_text(json.dumps(data, separators=(",", ":")))
    print(json.dumps(report, indent=2))
