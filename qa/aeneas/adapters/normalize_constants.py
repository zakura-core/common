"""Normalize literal Charon globals to initializer calls for Aeneas.

Accept only closed, typed booleans, 8/32/64-bit integers, arrays, structures,
tuples, and shared static references. Existing functions and dictionaries are
retained.
"""

import argparse
import copy
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("This translation adapter requires Python assertions")


ARGS = {"regions": [], "types": [], "const_generics": [], "trait_refs": []}
PARAMS = {"regions": [], "types": [], "const_generics": [], "trait_clauses": [],
          "regions_outlive": [], "types_outlive": [], "trait_type_constraints": []}


def unpack(value):
    assert isinstance(value, dict) and set(value) == {"Untagged"}, value
    return value["Untagged"]


def literal_initializer(constant, types, span, start):
    """Build a pure initializer for closed, typed structured literal data."""
    _, output = unpack(constant)
    locals_ = [{"index": 0, "name": None, "span": span,
                "ty": output, "drop_flag_for": None}]
    statements = []

    def place(index):
        return {"kind": {"Local": index}, "ty": locals_[index]["ty"]}

    def statement(kind):
        statements.append({"span": span, "id": start + len(statements) + 1,
                           "kind": kind, "comments_before": []})

    def allocate(ty):
        index = len(locals_)
        locals_.append({"index": index, "name": None, "span": span,
                        "ty": ty, "drop_flag_for": None})
        return index

    def substitute(ty, arguments):
        if isinstance(ty, dict):
            if set(ty) == {"Untagged"} and isinstance(ty["Untagged"], dict):
                kind = ty["Untagged"]
                if set(kind) == {"TypeVar"}:
                    assert set(kind["TypeVar"]) == {"Free"}
                    return arguments[kind["TypeVar"]["Free"]]
            return {k: substitute(v, arguments) for k, v in ty.items()}
        if isinstance(ty, list):
            return [substitute(v, arguments) for v in ty]
        return ty

    def scalar(value):
        expression, ty = unpack(value)
        if set(expression) == {"Bool"}:
            assert type(expression["Bool"]) is bool
            assert ty == {"Untagged": {"Scalar": "Bool"}}
            return True
        if set(expression) == {"Integer"}:
            sign, pair = next(iter(expression["Integer"].items()))
            kind, number = pair
            assert set(expression["Integer"]) == {sign}
            assert (sign, kind) in [("Unsigned", "U8"), ("Unsigned", "U32"), ("Unsigned", "U64"),
                                    ("Unsigned", "Usize"), ("Signed", "I64")]
            assert ty == {"Untagged": {"Scalar": {"Integer": {sign: kind}}}}
            number_int = int(number)
            assert str(number_int) == number
            # A usize literal must also fit the 32-bit interpretation.
            bits = 8 if kind == "U8" else 32 if kind in ["Usize", "U32"] else 64
            assert ((0 <= number_int < 2**bits) if sign == "Unsigned"
                    else (-2**63 <= number_int < 2**63))
            return True
        return False

    def operand(value):
        if scalar(value):
            return {"Const": value}
        _, ty = unpack(value)
        local = allocate(ty)
        initialize(value, local)
        return {"Move": place(local)}

    def initialize(value, destination):
        expression, ty = unpack(value)
        assert ty == locals_[destination]["ty"]
        statement({"StorageLive": destination})
        if scalar(value):
            rhs = {"Use": [{"Const": value}, "Yes"]}
        elif set(expression) == {"Array"}:
            elem, length, align = unpack(ty)["Array"]
            assert align is None
            nvalue, nty = unpack(length)
            assert nty == {"Untagged": {"Scalar": {"Integer": {"Unsigned": "Usize"}}}}
            kind, count = nvalue["Integer"]["Unsigned"]
            assert kind == "Usize" and str(int(count)) == count
            assert int(count) == len(expression["Array"])
            assert all(unpack(v)[1] == elem for v in expression["Array"])
            rhs = {"Aggregate": [{"Array": [elem, length, align]},
                                 [operand(v) for v in expression["Array"]]]}
        elif set(expression) == {"Adt"}:
            variant, fields = expression["Adt"]
            tref = unpack(ty)["Adt"]
            assert variant is None
            assert not tref["generics"]["regions"] and not tref["generics"]["const_generics"]
            if tref["builtin"] == "Tuple":
                field_types = tref["generics"]["types"]
            else:
                declaration = types[tref["id"]]
                assert set(declaration["kind"]) == {"Struct"}
                field_types = [substitute(field["ty"], tref["generics"]["types"])
                               for field in declaration["kind"]["Struct"]]
            assert [unpack(v)[1] for v in fields] == field_types
            rhs = {"Aggregate": [{"Adt": [tref, variant, None]},
                                 [operand(v) for v in fields]]}
        elif set(expression) == {"Ref"}:
            inner, metadata = expression["Ref"]
            region, inner_type, kind = unpack(ty)["Ref"]
            assert metadata is None and region == "Static" and kind == "Shared"
            assert unpack(inner)[1] == inner_type
            local = allocate(inner_type)
            initialize(inner, local)
            unit_ty = {"Untagged": {"Adt": {"id": 0, "generics": copy.deepcopy(ARGS),
                                           "builtin": "Tuple"}}}
            unit = {"Const": {"Untagged": [{"Adt": [None, []]}, unit_ty]}}
            rhs = {"Ref": {"place": place(local), "kind": "Shared", "ptr_metadata": unit}}
        else:
            raise ValueError(f"unsupported literal {expression}")
        statement({"Assign": [place(destination), rhs]})

    initialize(constant, 0)
    statement("Return")
    return {"Structured": {"span": span, "bound_body_regions": 0,
                           "locals": {"arg_count": 0, "locals": locals_},
                           "body": {"span": span, "id": start, "statements": statements},
                           "comments": []}}, start + len(statements) + 1


def normalize(document):
    assert not document["has_errors"]
    original = copy.deepcopy(document["translated"])
    t = document["translated"]
    statements = []
    def statement_ids(x):
        if isinstance(x, dict):
            if "id" in x and ("statements" in x or "comments_before" in x):
                statements.append(x["id"])
            for value in x.values():
                statement_ids(value)
        elif isinstance(x, list):
            for value in x:
                statement_ids(value)
    statement_ids(t["fun_decls"])
    next_statement = max(statements, default=0) + 1
    added = {}
    for g in t["global_decls"]:
        if g is None:
            continue
        if "Call" in unpack(g["value"])[0]:
            continue
        assert g["generics"] == PARAMS
        assert not g["item_meta"]["has_errors"]
        value = g["value"]
        _, ty = unpack(value)
        assert ty == g["ty"]
        fid = len(t["fun_decls"])
        gid = g["def_id"]
        span = g["item_meta"]["span"]
        body, next_statement = literal_initializer(value, t["type_decls"], span, next_statement)
        f = {
            "def_id": fid, "item_meta": copy.deepcopy(g["item_meta"]),
            "generics": copy.deepcopy(PARAMS),
            "signature": {"is_unsafe": False, "abi": "Rust", "is_variadic": False,
                          "inputs": [], "output": ty},
            "src": {"GlobalInitializer": {"id": gid, "generics": copy.deepcopy(ARGS)}},
            "body": body
        }
        t["fun_decls"].append(f)
        t["item_names"].append({"key": {"Fun": fid}, "value": f["item_meta"]["name"]})
        short = next((x["value"] for x in t["short_names"]
                      if x["key"] == {"Global": gid}), None)
        if short is not None:
            t["short_names"].append({"key": {"Fun": fid}, "value": short})
        g["value"] = {"Untagged": [{"Call": [
            {"kind": {"Fun": fid}, "generics": copy.deepcopy(ARGS)}, []]}, ty]}
        added[gid] = fid
    order = []
    for declaration in t["ordered_decls"]:
        gid = declaration.get("Global", {}).get("NonRec")
        if gid in added:
            order.append({"Fun": {"NonRec": added[gid]}})
        order.append(declaration)
    t["ordered_decls"] = order
    assert t["fun_decls"][:len(original["fun_decls"])] == original["fun_decls"]
    assert t["type_decls"] == original["type_decls"]
    assert t["trait_decls"] == original["trait_decls"]
    assert t["trait_impls"] == original["trait_impls"]
    for old, new in zip(original["global_decls"], t["global_decls"]):
        if old:
            assert {k: v for k, v in old.items() if k != "value"} == {
                k: v for k, v in new.items() if k != "value"}
    return {"literal_initializers": added,
            "existing_function_bodies_unchanged": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    data = json.loads(args.source.read_text())
    report = normalize(data)
    args.output.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    print(json.dumps(report, indent=2))
