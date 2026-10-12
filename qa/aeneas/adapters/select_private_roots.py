"""Retain explicitly selected private Udon routines in Aeneas's output.

Aeneas drops unreferenced functions in dependencies. Mark only Charon's
explicit private halving root as local for selection; its body and Rust
visibility are unchanged.
"""

import argparse
import copy
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("This translation adapter requires Python assertions")


def select(document):
    translated = document["translated"]
    original = copy.deepcopy(translated)
    selected = []
    prefix = [{"Ident": [name, 0]} for name in ["zakura_udon", "field", "pasta"]]
    for function in translated["fun_decls"]:
        if not function:
            continue
        metadata = function["item_meta"]
        if metadata["name"][:3] != prefix or metadata["name"][-1] != {"Ident": ["half", 0]}:
            continue
        assert metadata["started_from"] and not metadata["is_local"]
        assert metadata["opacity"] == "Transparent" and not metadata["is_extern"]
        assert not metadata["attr_info"]["public"]
        assert set(function["body"]) == {"Structured"}
        metadata["is_local"] = True
        selected.append(function["def_id"])
    assert len(selected) == 1
    expected = copy.deepcopy(original)
    for identifier in selected:
        expected["fun_decls"][identifier]["item_meta"]["is_local"] = True
    assert translated == expected
    return {"selected_private_roots": selected, "function_bodies_unchanged": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    document = json.loads(args.source.read_text())
    report = select(document)
    args.output.write_text(json.dumps(document, separators=(",", ":")) + "\n")
    print(json.dumps(report, indent=2))
