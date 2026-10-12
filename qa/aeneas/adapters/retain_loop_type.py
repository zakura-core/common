"""Retain the decoder loop's generic type through an inert PhantomData clone.

Aeneas retains a ReductionState<S> dictionary but drops S from the loop's
parameters when S appears only in that dictionary. The added zero-sized clone
keeps S in the term. Its transparent model returns the same marker, and Rust's
PhantomData clone is inert. Every original instruction is preserved; removing
the addition must restore the complete original AST.
"""
import argparse
import copy
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


def adapt(data):
    original = copy.deepcopy(data)
    translated = data["translated"]
    phantom = next(decl["def_id"] for decl in translated["type_decls"]
                   if decl and decl["item_meta"]["name"] == named("core", "marker", "PhantomData"))
    clones = [decl for decl in translated["fun_decls"] if decl
              and decl["item_meta"]["name"][:2] == named("core", "marker")
              and decl["item_meta"]["name"][-1] == {"Ident": ["clone", 0]}]
    assert len(clones) == 1
    clone = clones[0]
    assert clone["body"] == "Opaque"
    assert clone["signature"]["output"]["Untagged"]["Adt"]["id"] == phantom
    assert len(clone["generics"]["types"]) == 1
    assert not clone["generics"]["trait_clauses"]
    assert len(clone["signature"]["inputs"]) == 1
    signature_ref = clone["signature"]["inputs"][0]["Untagged"]["Ref"]
    assert signature_ref[1] == clone["signature"]["output"] and signature_ref[2] == "Shared"
    functions = [decl for decl in translated["fun_decls"] if decl
                 and decl["item_meta"]["name"][:4] == named("zakura_udon", "field", "pasta", "encoding")
                 and decl["item_meta"]["name"][-1] == {"Ident": ["from_bytes_reduced", 0]}]
    assert len(functions) == 1
    function = functions[0]
    assert [(param["index"], param["name"]) for param in function["generics"]["types"]] == [(0, "M"), (1, "S")]
    body = function["body"]["Structured"]
    locals_ = body["locals"]["locals"]
    local_count = len(locals_)
    region = body["bound_body_regions"]
    loops = [node["Loop"] for node in nodes(body) if isinstance(node, dict) and "Loop" in node]
    assert len(loops) == 1
    loop = loops[0]
    span = loop["span"]
    next_id = max(node["id"] for node in nodes(translated)
                  if isinstance(node, dict) and isinstance(node.get("id"), int)) + 1

    def metadata(kind):
        nonlocal next_id
        statement = {"span": span, "id": next_id, "kind": kind, "comments_before": []}
        next_id += 1
        return statement

    state_type = {"Untagged": {"TypeVar": {"Free": 1}}}
    generics = {"regions": [], "types": [state_type], "const_generics": [], "trait_refs": []}
    adt = {"id": phantom, "generics": generics, "builtin": None}
    marker_type = {"Untagged": {"Adt": adt}}
    ref_type = {"Untagged": {"Ref": [{"Body": region}, marker_type, "Shared"]}}
    places = []
    for offset, ty in enumerate([marker_type, ref_type, marker_type]):
        index = local_count + offset
        locals_.append({"index": index, "name": None, "span": span, "ty": ty, "drop_flag_for": None})
        places.append({"kind": {"Local": index}, "ty": ty})
    body["bound_body_regions"] += 1
    marker, reference, output = places
    unit = {"Untagged": {"Adt": {"id": 0,
            "generics": {"regions": [], "types": [], "const_generics": [], "trait_refs": []}, "builtin": "Tuple"}}}
    thin_metadata = {"Const": {"Untagged": [{"Adt": [None, []]}, unit]}}
    unwind = {"span": span, "id": next_id, "statements": []}
    next_id += 1
    unwind["statements"].append(metadata("UnwindResume"))
    call = {"call": {
        "func": {"Regular": {"kind": {"Fun": clone["def_id"]},
            "generics": {**generics, "regions": [{"Body": region}]}}},
        "args": [{"Move": reference}], "dest": output, "safety": "Inherit"}, "on_unwind": unwind}
    additions = [metadata({"StorageLive": local_count + offset}) for offset in range(3)]
    additions += [
        metadata({"Assign": [marker, {"Aggregate": [{"Adt": [adt, None, None]}, []]}]}),
        metadata({"Assign": [reference, {"Ref": {"place": marker, "kind": "Shared", "ptr_metadata": thin_metadata}}]}),
        metadata({"Call": call}),
    ]
    additions += [metadata({"StorageDead": local_count + offset}) for offset in reversed(range(3))]
    loop["statements"][:0] = additions
    restored = copy.deepcopy(data)
    restored_body = restored["translated"]["fun_decls"][function["def_id"]]["body"]["Structured"]
    restored_body["locals"]["locals"] = restored_body["locals"]["locals"][:local_count]
    restored_body["bound_body_regions"] = region
    restored_loops = [node["Loop"] for node in nodes(restored_body) if isinstance(node, dict) and "Loop" in node]
    assert len(restored_loops) == 1
    assert restored_loops[0]["statements"][:len(additions)] == additions
    del restored_loops[0]["statements"][:len(additions)]
    assert restored == original
    return {"inert_marker_clones": 1, "inserted_locals": 3, "inserted_statements": 9,
            "complete_original_AST_restored": True}


def explicit_argument(source):
    start = source.index("def zakura_udon.field.pasta.encoding.PastaField.from_bytes_reduced_loop.body")
    end = source.index("\n/--", start)
    block = source[start:end]
    assert "{S : Type}" in block
    old = "core.marker.PhantomData.Insts.CoreCloneClone.clone ()"
    new = "core.marker.PhantomData.Insts.CoreCloneClone.clone (T := S) ()"
    assert block.count(old) == source.count(old) == 1
    adapted = source[:start] + block.replace(old, new) + source[end:]
    assert adapted.replace(new, old) == source
    return adapted


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path, nargs="?")
    parser.add_argument("--lean", action="store_true")
    args = parser.parse_args()
    if args.lean:
        assert args.destination is None
        args.source.write_text(explicit_argument(args.source.read_text()))
        print("The single inserted marker clone's type argument is explicit; other generated code is unchanged.")
    else:
        assert args.destination is not None
        data = json.loads(args.source.read_text())
        report = adapt(data)
        args.destination.write_text(json.dumps(data, separators=(",", ":")) + "\n")
        print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
