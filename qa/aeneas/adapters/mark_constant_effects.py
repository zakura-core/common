"""Work around Aeneas effect inference for generic field ONE initializers.

A generic trait constant is modeled as a fallible Result, but the initializer
was annotated as pure. An assertion of the literal `true` has no operational
effect and makes the initializer's inferred return type consistently fallible.
"""
import argparse
import copy
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("This translation adapter requires Python assertions")


def mark(document):
    t = document["translated"]
    original = copy.deepcopy(t)
    marked = []
    ids = []
    def visit(x):
        if isinstance(x, dict):
            if "id" in x and ("statements" in x or "comments_before" in x):
                ids.append(x["id"])
            for v in x.values():
                visit(v)
        elif isinstance(x, list):
            for v in x:
                visit(v)
    visit(t["fun_decls"])
    next_id = max(ids) + 1
    for g in t["global_decls"]:
        if not g:
            continue
        parts = g["item_meta"]["name"]
        if parts[-1] != {"Ident": ["ONE", 0]}:
            continue
        if not any("Impl" in p and "Ty" in p["Impl"] for p in parts):
            continue
        assert parts[:3] == [{"Ident": [x, 0]} for x in ["zakura_udon", "field", "pasta"]]
        fid = g["value"]["Untagged"][0]["Call"][0]["kind"]["Fun"]
        f = t["fun_decls"][fid]
        assert f["src"]["GlobalInitializer"]["id"] == g["def_id"]
        statements = f["body"]["Structured"]["body"]["statements"]
        assert statements[-1]["kind"] == "Return"
        span = f["item_meta"]["span"]
        literal = {"Const": {"Untagged": [{"Bool": True}, {"Untagged": {"Scalar": "Bool"}}]}}
        statements.insert(-1, {
            "span": span, "id": next_id,
            "kind": {"Assert": {
                "assert": {"cond": literal, "expected": True, "check_kind": None},
                "on_failure": {"Panic": [{"Ident": [x, 0]} for x in ["core", "panicking", "panic"]]},
                "on_unwind": {"span": span, "id": next_id + 1, "statements": [
                    {"span": span, "id": next_id + 2, "kind": "UnwindResume", "comments_before": []}]}
            }},
            "comments_before": [],
        })
        next_id += 3
        marked.append(fid)
    assert len(marked) == 1
    restored = copy.deepcopy(t)
    for fid in marked:
        statements = restored["fun_decls"][fid]["body"]["Structured"]["body"]["statements"]
        added = statements.pop(-2)
        assert added["kind"]["Assert"]["assert"]["cond"] == {
            "Const": {"Untagged": [{"Bool": True}, {"Untagged": {"Scalar": "Bool"}}]}}
    assert restored == original
    return {"assert_true_in_generic_one_initializer": marked,
            "remaining_definitions_unchanged": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    document = json.loads(args.source.read_text())
    report = mark(document)
    args.output.write_text(json.dumps(document, separators=(",", ":")) + "\n")
    print(json.dumps(report, indent=2))
