"""Model the portable product loop's read-only borrowed chunk iterators.

Aeneas cannot join this loop's two by_ref borrows. Use owned snapshots of
ChunksExact instead. Their items are shared slices; advancing them changes
only the remaining chunks. Check that the original iterators' only subsequent
uses are remainder(), whose result never changes during iteration. Lean must
also check the corresponding remainder frame lemmas. This is a standard-library
borrow model in the translation trust boundary, not a verified compiler pass.

The independent checker permits only the specified borrow/type/dictionary
substitutions. All arithmetic, guards and other declarations must be identical.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from project_product_short import short_dispatch, target
from unroll_merge import named, nodes

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


def inventory(data):
    translated = data["translated"]
    assert [t["key"] for t in translated["target_information"]] == ["x86_64-apple-darwin"]
    types = [t for t in translated["type_decls"] if t and t["item_meta"]["name"] ==
             named("core", "slice", "iter", "ChunksExact")]
    assert len(types) == 1
    chunk_id = types[0]["def_id"]
    by_ref = [f for f in translated["fun_decls"] if f and
              f["item_meta"]["name"][:4] == named("core", "iter", "traits", "iterator") and
              f["item_meta"]["name"][-1] == {"Ident": ["by_ref", 0]}]
    assert len(by_ref) == 1
    assert by_ref[0]["signature"]["inputs"] == [by_ref[0]["signature"]["output"]]
    assert by_ref[0]["signature"]["output"]["Untagged"]["Ref"][2] == "Mut"
    borrowed = [i for i in translated["trait_impls"] if i and
                i["item_meta"]["name"][:4] == named("core", "iter", "traits", "iterator") and
                i["impl_trait"]["generics"]["types"][0].get("Untagged", {}).get("Ref", [None, None, None])[2] == "Mut"]
    assert len(borrowed) == 1
    function = target(data)
    serial = short_dispatch(function)[9]["kind"]["Switch"]["branches"][1]["statements"]
    lanes = serial[9]["kind"]["Switch"]["branches"][1]["statements"]
    assert len(lanes) == 129 and "Loop" in lanes[42]["kind"]
    assert lanes[42]["span"]["Untagged"]["data"]["beg"]["line"] == 529
    captures = []
    for node in normal_nodes(lanes[:42]):
        if isinstance(node.get("Ref"), dict):
            ref = node["Ref"]
            place = ref["place"]
            if ref["kind"] in ("Mut", "TwoPhaseMut") and place["kind"].get("Local") is not None:
                if place["ty"].get("Untagged", {}).get("Adt", {}).get("id") == chunk_id:
                    captures.append(place["kind"]["Local"])
    assert len(captures) == len(set(captures)) == 2
    # After the borrowed loop, each original iterator is borrowed once, shared,
    # and passed immediately to remainder(). No other read or write is allowed.
    observed = []
    for position, statement in enumerate(lanes[43:], 43):
        kind = statement["kind"]
        if not isinstance(kind, dict) or "Assign" not in kind:
            continue
        destination, value = kind["Assign"]
        ref = value.get("Ref", {})
        place = ref.get("place", {})
        if place.get("kind", {}).get("Local") not in captures:
            continue
        assert ref["kind"] == "Shared"
        call = lanes[position + 1]["kind"]["Call"]["call"]
        callee = translated["fun_decls"][call["func"]["Regular"]["kind"]["Fun"]]
        assert callee["item_meta"]["name"][:3] == named("core", "slice", "iter")
        assert callee["item_meta"]["name"][-1] == {"Ident": ["remainder", 0]}
        assert call["args"] == [{"Move": destination}]
        observed.append(place)
    references = [node for node in normal_nodes(lanes[43:]) if isinstance(node.get("kind"), dict) and node["kind"].get("Local") in captures]
    assert references == observed and len(observed) == 2
    return function, chunk_id, by_ref[0]["def_id"], borrowed[0]["def_id"]


def patterns(chunk_id, by_ref_id, borrowed_id):
    def chunk(ty):
        return isinstance(ty, dict) and ty.get("Untagged", {}).get("Adt", {}).get("id") == chunk_id

    def classify(value):
        if not isinstance(value, dict):
            return None
        untagged = value.get("Untagged")
        if isinstance(untagged, dict):
            ref = untagged.get("Ref")
            if isinstance(ref, list) and ref[2] == "Mut" and chunk(ref[1]):
                return "type", ref[1]
            impl = untagged.get("kind", {}).get("TraitImpl")
            if impl and impl["id"] == borrowed_id and chunk(impl["generics"]["types"][0]):
                assert len(impl["generics"]["trait_refs"]) == 1
                return "dictionary", impl["generics"]["trait_refs"][0]
        kind = value.get("kind")
        if isinstance(kind, dict) and "Call" in kind:
            call = kind["Call"]["call"]
            if call["func"]["Regular"]["kind"] == {"Fun": by_ref_id}:
                assert chunk(call["func"]["Regular"]["generics"]["types"][0])
                assert len(call["args"]) == 1
                assert all(s["kind"] == "UnwindResume" or isinstance(s["kind"], dict) and
                           set(s["kind"]) == {"StorageDead"}
                           for s in kind["Call"]["on_unwind"]["statements"])
                return "by_ref", call
        if isinstance(kind, dict) and "Assign" in kind:
            destination, value = kind["Assign"]
            ref = value.get("Ref", {})
            if ref.get("kind") in ("Mut", "TwoPhaseMut") and chunk(ref["place"]["ty"]):
                assert ref["ptr_metadata"]["Const"]["Untagged"][0] == {"Adt": [None, []]}
                return "snapshot", (destination, ref["place"])
        if isinstance(kind, dict) and "Projection" in kind:
            base, projection = kind["Projection"]
            ref = base["ty"]["Untagged"].get("Ref")
            if projection == "Deref" and ref and ref[2] == "Mut" and chunk(ref[1]):
                return "deref", base
        return None
    return classify


def check_model(original, modeled):
    function, *identifiers = inventory(original)
    classify = patterns(*identifiers)
    counts = {}

    def check(old, new):
        match = classify(old)
        if match:
            kind, value = match
            counts[kind] = counts.get(kind, 0) + 1
            if kind in ("type", "dictionary", "deref"):
                check(value, new)
                return
            assert set(old) == set(new)
            for key in old:
                if key != "kind":
                    check(old[key], new[key])
            assignment = new["kind"]["Assign"]
            assert set(new["kind"]) == {"Assign"} and len(assignment) == 2
            assert set(assignment[1]) == {"Use"}
            operand, flag = assignment[1]["Use"]
            assert flag == "Yes"
            if kind == "by_ref":
                check(value["dest"], assignment[0])
                check(value["args"][0], operand)
            else:
                destination, place = value
                assert set(operand) == {"Copy"}
                check(destination, assignment[0])
                check(place, operand["Copy"])
            return
        assert type(old) is type(new)
        if isinstance(old, dict):
            assert set(old) == set(new)
            for key in old:
                check(old[key], new[key])
        elif isinstance(old, list):
            assert len(old) == len(new)
            for left, right in zip(old, new):
                check(left, right)
        else:
            assert old == new

    check(function["body"], target(modeled)["body"])
    restored = copy.deepcopy(modeled)
    target(restored)["body"] = copy.deepcopy(function["body"])
    assert restored == original
    assert counts == {"type": 61, "snapshot": 3, "by_ref": 2, "deref": 1, "dictionary": 6}, counts
    return counts


def adapt(data, self_test=False):
    original = copy.deepcopy(data)
    function, *identifiers = inventory(data)
    classify = patterns(*identifiers)

    def rewrite(value):
        match = classify(value)
        if match:
            kind, selected = match
            if kind in ("type", "dictionary", "deref"):
                return rewrite(selected)
            if kind == "by_ref":
                assignment = [rewrite(selected["dest"]), {"Use": [rewrite(selected["args"][0]), "Yes"]}]
            else:
                destination, place = selected
                assignment = [rewrite(destination), {"Use": [{"Copy": rewrite(place)}, "Yes"]}]
            return {**copy.deepcopy(value), "kind": {"Assign": assignment}}
        if isinstance(value, dict):
            return {key: rewrite(child) for key, child in value.items()}
        if isinstance(value, list):
            return [rewrite(child) for child in value]
        return value

    function["body"] = rewrite(function["body"])
    counts = check_model(original, data)
    if self_test:
        mutations = []
        changed = copy.deepcopy(data)
        target(changed)["signature"]["inputs"].pop()
        mutations.append(changed)
        changed = copy.deepcopy(data)
        assignment = next(n["kind"]["Assign"] for n in nodes(target(changed)["body"])
                          if isinstance(n, dict) and isinstance(n.get("kind"), dict) and
                          "Assign" in n["kind"] and "Use" in n["kind"]["Assign"][1] and
                          "Copy" in n["kind"]["Assign"][1]["Use"][0] and
                          n["kind"]["Assign"][1]["Use"][0]["Copy"]["ty"].get("Untagged", {}).get("Adt", {}).get("id") == identifiers[0])
        assignment[1]["Use"][0]["Copy"]["kind"] = {"Local": 0}
        mutations.append(changed)
        changed = copy.deepcopy(data)
        statement = next(n for n in nodes(target(changed)["body"]) if isinstance(n, dict) and
                         isinstance(n.get("kind"), dict) and "Loop" in n["kind"])
        statement["kind"]["Loop"]["statements"][-1]["kind"] = "Nop"
        mutations.append(changed)
        changed = copy.deepcopy(data)
        target(changed)["body"]["Structured"]["body"]["statements"][0]["kind"] = "Nop"
        mutations.append(changed)
        for mutation in mutations:
            try:
                check_model(original, mutation)
            except (AssertionError, KeyError, IndexError, TypeError):
                pass
            else:
                raise RuntimeError("The read-only borrow checker accepted a changed AST")
    digest = lambda value: hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"owned_readonly_chunk_snapshots": True, "checked_substitutions": counts,
            "post_loop_observations": "two shared remainder() calls only",
            "arithmetic_and_dispatch_unchanged": True, "all_other_declarations_unchanged": True,
            "complete_original_AST_restored": True, "rejected_mutations": 4 if self_test else 0,
            "required_Lean_obligations": ["ChunksExact.next preserves remainder", "remainder frame through the paired loop"],
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
