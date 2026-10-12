"""Outline the sixteen unchanged Comba macro expansions in add_product_block.

The pinned translator cannot handle all thirty-two loops in one function.
Each helper receives the mutable column array and the two shared slices. Its
payload is copied from the original LLBC, with a checked local renaming and
column reference. Only unwind storage cleanup outside the helper's scope is
removed. The checker inverts these changes and reconstructs the complete AST.
This adapter remains part of the translation trust boundary.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from unroll_merge import named, nodes, strip_ids

if not __debug__:
    raise RuntimeError("This adapter requires Python assertions")


def normal_nodes(value):
    if isinstance(value, dict):
        yield value
        for key, child in value.items():
            if key != "on_unwind":
                yield from normal_nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from normal_nodes(child)


def target(data):
    functions = [f for f in data["translated"]["fun_decls"] if f and
                 f["item_meta"]["name"][:4] == named("zakura_udon", "field", "pasta", "products") and
                 f["item_meta"]["name"][-1] == {"Ident": ["add_product_block", 0]}]
    assert len(functions) == 1
    return functions[0]


def inventory(data):
    assert [t["key"] for t in data["translated"]["target_information"]] == ["aarch64-apple-darwin"]
    function = target(data)
    assert len(function["signature"]["inputs"]) == 3
    assert len(function["generics"]["types"]) == len(function["generics"]["regions"]) == 3
    assert function["generics"]["trait_clauses"] == []
    body = function["body"]["Structured"]
    assert body["locals"]["arg_count"] == 3
    statements = body["body"]["statements"]
    assert len(statements) == 2722 and statements[0]["kind"] == {"StorageLive": 0}
    assert statements[2]["kind"]["Assign"][0]["kind"] == {"Local": 0}
    assert statements[-1]["kind"] == "Return"
    columns = body["locals"]["locals"][23]["ty"]
    word = {"Untagged": {"Scalar": {"Integer": {"Unsigned": "U64"}}}}
    inner, four, extra = columns["Untagged"]["Array"]
    assert extra is None and four["Untagged"][0] == {"Integer": {"Unsigned": ["Usize", "4"]}}
    element, three, extra = inner["Untagged"]["Array"]
    assert extra is None and element == word
    assert three["Untagged"][0] == {"Integer": {"Unsigned": ["Usize", "3"]}}
    loops = [i for i, s in enumerate(statements) if isinstance(s["kind"], dict) and "Loop" in s["kind"]]
    assert len(loops) == 32
    ranges = [(loops[i] - 36, loops[i+1] + 9) for i in range(0, 32, 2)]
    for start, end in ranges:
        assert end - start == 66
        assert [len(statements[j]["kind"]["Loop"]["statements"]) for j in (start+36, end-9)] == [269,64]
        assert [statements[j]["span"]["Untagged"]["data"]["beg"]["line"] for j in (start+36,end-9)] == [197,219]
        assert statements[start+3]["kind"]["Call"]["call"]["func"]["Regular"]["kind"].get("Fun") is not None
    return function, ranges, columns


def slot_set(fragment):
    used = {0,1,2,3}
    for node in normal_nodes(fragment):
        for key in ("Local", "StorageLive", "StorageDead"):
            if isinstance(node.get(key), int):
                used.add(node[key])
    assert not any(node.get("StorageLive") == 23 or node.get("StorageDead") == 23 for node in normal_nodes(fragment))
    return used - {23}


def scoped_cleanup(value, allowed):
    value = copy.deepcopy(value)
    for node in nodes(value):
        if isinstance(node, dict) and "statements" in node:
            node["statements"] = [s for s in node["statements"] if not (
                isinstance(s["kind"], dict) and "StorageDead" in s["kind"] and s["kind"]["StorageDead"] not in allowed)]
    return value


def column_place(function, columns):
    reference = copy.deepcopy(function["body"]["Structured"]["locals"]["locals"][1]["ty"])
    reference["Untagged"]["Ref"][1] = copy.deepcopy(columns)
    return {"kind": {"Projection": [{"kind": {"Local": 1}, "ty": reference}, "Deref"]}, "ty": copy.deepcopy(columns)}


def make_helper(function, fragment, columns, identifier, ordinal):
    helper = copy.deepcopy(function)
    helper["def_id"] = identifier
    helper["item_meta"]["name"] = named("zakura_udon", "field", "pasta", "products", f"outlined_block_{ordinal:02}")
    helper["item_meta"]["started_from"] = True
    helper["item_meta"]["is_local"] = True
    helper["signature"]["inputs"][0]["Untagged"]["Ref"][1] = copy.deepcopy(columns)
    body = helper["body"]["Structured"]
    body["locals"]["locals"][1]["ty"]["Untagged"]["Ref"][1] = copy.deepcopy(columns)
    captured = column_place(function, columns)

    def capture(value):
        if isinstance(value, dict):
            if value.get("kind") == {"Local": 23} and "ty" in value:
                return copy.deepcopy(captured)
            return {key: capture(child) for key, child in value.items()}
        if isinstance(value, list):
            return [capture(child) for child in value]
        return value

    source = function["body"]["Structured"]["body"]["statements"]
    body["body"]["statements"] = [copy.deepcopy(source[0]), copy.deepcopy(source[2])] + capture(fragment) + [copy.deepcopy(source[-1])]
    used = slot_set(fragment)
    body["body"] = scoped_cleanup(body["body"], used)
    mapping = {old: new for new, old in enumerate(sorted(used))}
    for node in nodes(body["body"]):
        if isinstance(node, dict):
            for key in ("Local", "StorageLive", "StorageDead"):
                if isinstance(node.get(key), int):
                    node[key] = mapping[node[key]]
    body["locals"]["locals"] = [copy.deepcopy(body["locals"]["locals"][old]) for old in sorted(used)]
    for index, local in enumerate(body["locals"]["locals"]):
        assert local["drop_flag_for"] is None
        local["index"] = index
    return helper


def call_fragment(function, columns, source, identifier, local_id, region):
    reference = {"Untagged": {"Ref": [{"Body": region}, copy.deepcopy(columns), "Mut"]}}
    place = {"kind": {"Local": local_id}, "ty": copy.deepcopy(reference)}
    local = {"index": local_id, "name": None, "span": copy.deepcopy(function["item_meta"]["span"]),
             "ty": reference, "drop_flag_for": None}
    make = lambda kind: {"span": copy.deepcopy(source[0]["span"]), "id": 0, "kind": kind, "comments_before": []}
    inputs = function["body"]["Structured"]["locals"]["locals"]
    call = {"call": {"func": {"Regular": {"kind": {"Fun": identifier}, "generics": {
        "regions": [{"Body": region}, {"Body": 3}, {"Body": 5}],
        "types": [{"Untagged": {"TypeVar": {"Free": i}}} for i in range(3)],
        "const_generics": [], "trait_refs": []}}},
        "args": [{"Move": copy.deepcopy(place)}] + [{"Copy": {"kind": {"Local": i},
            "ty": copy.deepcopy(inputs[i]["ty"])}} for i in (2,3)],
        "dest": {"kind": {"Local": 0}, "ty": copy.deepcopy(function["signature"]["output"])}, "safety": "Inherit"},
        "on_unwind": copy.deepcopy(source[3]["kind"]["Call"]["on_unwind"])}
    statements = [make({"StorageLive": local_id}), make({"Assign": [copy.deepcopy(place), {"Ref": {
        "place": {"kind": {"Local": 23}, "ty": copy.deepcopy(columns)}, "kind": "Mut",
        "ptr_metadata": {"Const": {"Untagged": [{"Adt": [None, []]}, copy.deepcopy(function["signature"]["output"])]}}}}]}),
        make({"Call": call}), make({"StorageDead": local_id})]
    return local, statements


def check_outline(original, outlined):
    function, ranges, columns = inventory(original)
    translated = original["translated"]
    new = outlined["translated"]
    count = len(translated["fun_decls"])
    assert len(new["fun_decls"]) == count + 16
    parent = target(outlined)
    old_body = function["body"]["Structured"]
    new_body = parent["body"]["Structured"]
    original_statements = old_body["body"]["statements"]
    reconstructed = copy.deepcopy(parent)
    reconstructed_body = reconstructed["body"]["Structured"]
    offset = 0
    for ordinal, (start,end) in enumerate(ranges):
        identifier = count + ordinal
        helper = new["fun_decls"][identifier]
        fragment = original_statements[start:end]
        used = sorted(slot_set(fragment))
        inverse = {index: old for index, old in enumerate(used)}
        captured = column_place(function, columns)

        def unmap(value):
            if isinstance(value, dict):
                if value == captured:
                    return {"kind": {"Local": 23}, "ty": copy.deepcopy(columns)}
                result = {key: unmap(child) for key, child in value.items()}
                for key in ("Local", "StorageLive", "StorageDead"):
                    if isinstance(value.get(key), int):
                        result[key] = inverse[value[key]]
                return result
            if isinstance(value, list):
                return [unmap(child) for child in value]
            return value

        hb = helper["body"]["Structured"]
        payload = hb["body"]["statements"]
        assert strip_ids(payload[:2]) == strip_ids([original_statements[0],original_statements[2]])
        assert strip_ids(payload[-1:]) == strip_ids([original_statements[-1]])
        assert strip_ids(unmap(payload[2:-1])) == strip_ids(scoped_cleanup(fragment, set(used)))
        # Validate the helper interface, local table, and all body metadata
        # separately from the inverse payload comparison above.
        expected = copy.deepcopy(function)
        expected["def_id"] = identifier
        expected["item_meta"]["name"] = named("zakura_udon", "field", "pasta", "products", f"outlined_block_{ordinal:02}")
        expected["item_meta"]["started_from"] = expected["item_meta"]["is_local"] = True
        expected["signature"]["inputs"][0]["Untagged"]["Ref"][1] = copy.deepcopy(columns)
        eb = expected["body"]["Structured"]
        eb["locals"]["locals"][1]["ty"]["Untagged"]["Ref"][1] = copy.deepcopy(columns)
        eb["locals"]["locals"] = [copy.deepcopy(eb["locals"]["locals"][old]) for old in used]
        for index, local in enumerate(eb["locals"]["locals"]):
            local["index"] = index
        eb["body"]["statements"] = copy.deepcopy(payload)
        assert strip_ids(helper) == strip_ids(expected)
        # Check each caller's capture, argument routing and storage lifetime.
        local_id = len(old_body["locals"]["locals"]) + 15 - ordinal
        region = old_body["bound_body_regions"] + 15 - ordinal
        local, replacement = call_fragment(function, columns, fragment, identifier, local_id, region)
        position = start - offset
        assert strip_ids(new_body["body"]["statements"][position:position+4]) == strip_ids(replacement)
        assert new_body["locals"]["locals"][local_id] == local
        offset += (end-start)-4
    # Restore all payloads using original positions after a separate forward
    # pass; do not rely on the length-changing substitutions above.
    current = new_body["body"]["statements"]
    restored_statements = []
    cursor = 0
    previous_end = 0
    for start,end in ranges:
        retained = start - previous_end
        restored_statements.extend(copy.deepcopy(current[cursor:cursor+retained]))
        cursor += retained
        restored_statements.extend(copy.deepcopy(original_statements[start:end]))
        cursor += 4
        previous_end = end
    restored_statements.extend(copy.deepcopy(current[cursor:]))
    reconstructed_body["body"]["statements"] = restored_statements
    assert len(new_body["locals"]["locals"]) == len(old_body["locals"]["locals"]) + 16
    assert new_body["bound_body_regions"] == old_body["bound_body_regions"] + 16
    reconstructed_body["locals"]["locals"] = copy.deepcopy(old_body["locals"]["locals"])
    reconstructed_body["bound_body_regions"] = old_body["bound_body_regions"]
    assert strip_ids(reconstructed) == strip_ids(function)
    expected_order = copy.deepcopy(translated["ordered_decls"])
    index = expected_order.index({"Fun": {"NonRec": function["def_id"]}})
    expected_order[index:index] = [{"Fun": {"NonRec": count+i}} for i in range(16)]
    assert new["ordered_decls"] == expected_order
    assert new["item_names"] == translated["item_names"] + [{"key": {"Fun": count+i},
        "value": named("zakura_udon", "field", "pasta", "products", f"outlined_block_{i:02}")} for i in range(16)]
    restored = copy.deepcopy(outlined)
    restored["translated"]["fun_decls"] = restored["translated"]["fun_decls"][:count]
    restored["translated"]["fun_decls"][function["def_id"]] = copy.deepcopy(function)
    for field in ("ordered_decls", "item_names"):
        restored["translated"][field] = copy.deepcopy(translated[field])
    assert restored == original


def adapt(data, self_test=False):
    original = copy.deepcopy(data)
    function, ranges, columns = inventory(data)
    translated = data["translated"]
    body = function["body"]["Structured"]
    statements = body["body"]["statements"]
    helpers = []
    for ordinal, (start,end) in enumerate(ranges):
        identifier = len(translated["fun_decls"])
        helper = make_helper(function, statements[start:end], columns, identifier, ordinal)
        translated["fun_decls"].append(helper)
        translated["item_names"].append({"key": {"Fun": identifier}, "value": helper["item_meta"]["name"]})
        helpers.append((start,end,identifier))
    index = translated["ordered_decls"].index({"Fun": {"NonRec": function["def_id"]}})
    translated["ordered_decls"][index:index] = [{"Fun": {"NonRec": identifier}} for _,_,identifier in helpers]
    for start,end,identifier in reversed(helpers):
        local_id = len(body["locals"]["locals"])
        region = body["bound_body_regions"]
        body["bound_body_regions"] += 1
        local, replacement = call_fragment(function, columns, statements[start:end], identifier, local_id, region)
        body["locals"]["locals"].append(local)
        statements[start:end] = replacement
    for changed in [function] + [translated["fun_decls"][identifier] for _,_,identifier in helpers]:
        for index, node in enumerate(n for n in nodes(changed["body"]) if isinstance(n, dict) and "id" in n and "span" in n):
            node["id"] = index
    check_outline(original, data)
    if self_test:
        mutations = []
        count = len(original["translated"]["fun_decls"])
        changed = copy.deepcopy(data)
        changed["translated"]["fun_decls"][count]["body"]["Structured"]["body"]["statements"][-1]["kind"] = "Nop"
        mutations.append(changed)
        changed = copy.deepcopy(data)
        changed["translated"]["fun_decls"][count]["signature"]["inputs"][0]["Untagged"]["Ref"][2] = "Shared"
        mutations.append(changed)
        changed = copy.deepcopy(data)
        source = target(changed)["body"]["Structured"]["body"]["statements"]
        source[ranges[0][0]+2]["kind"]["Call"]["call"]["func"]["Regular"]["kind"] = {"Fun": count+1}
        mutations.append(changed)
        changed = copy.deepcopy(data)
        target(changed)["body"]["Structured"]["body"]["statements"][-1]["kind"] = "Nop"
        mutations.append(changed)
        changed = copy.deepcopy(data)
        helper = changed["translated"]["fun_decls"][count]
        call = next(n["Call"]["call"] for n in nodes(helper["body"]) if isinstance(n, dict) and "Call" in n)
        call["func"]["Regular"]["kind"] = {"Fun": count+1}
        mutations.append(changed)
        changed = copy.deepcopy(data)
        changed["translated"]["fun_decls"][count]["body"]["Structured"]["locals"]["locals"][1]["name"] = "changed_capture"
        mutations.append(changed)
        for mutation in mutations:
            try:
                check_outline(original, mutation)
            except (AssertionError, KeyError, IndexError, TypeError):
                pass
            else:
                raise RuntimeError("The outlining checker accepted a changed AST")
    digest = lambda value: hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"outlined_macro_expansions": 16, "retained_loops": 32, "arithmetic_payloads_unchanged": True,
            "inverse_local_and_capture_check": True, "caller_arguments_and_lifetimes_checked": True,
            "unwind_changes": "only storage cleanup outside each introduced helper's scope",
            "complete_original_AST_restored": True, "rejected_mutations": 6 if self_test else 0,
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
