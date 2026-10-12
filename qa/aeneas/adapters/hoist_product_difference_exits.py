"""Move three pinned loop exhaustion continuations past their loops.

Aeneas cannot translate Returns nested inside these loops. Each continuation
is moved intact, leaving a Break in its place. A separate reverse checker
requires equality of the complete original AST and rejects four mutations.
Agreement with LLBC control-flow semantics remains a translation boundary.
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


def declaration(data):
    prefix = [{"Ident": [s, 0]} for s in ["zakura_udon", "field", "pasta", "products"]]
    matches = [f for f in data["translated"]["fun_decls"] if f and
               f["item_meta"]["name"][:4] == prefix and
               f["item_meta"]["name"][-1] == {"Ident": ["product_difference", 0]}]
    assert len(matches) == 1
    return matches[0]


def locate(body, loop_id):
    matches = []
    for block in nodes(body):
        if isinstance(block, dict) and isinstance(block.get("statements"), list):
            for i, statement in enumerate(block["statements"]):
                if statement["id"] == loop_id and isinstance(statement["kind"], dict) \
                        and "Loop" in statement["kind"]:
                    matches.append((block["statements"], i))
    assert len(matches) == 1
    return matches[0]


def check(original, adapted, moves):
    restored = copy.deepcopy(adapted)
    body = declaration(restored)["body"]
    for loop_id, tail, old_exit, new_exit in reversed(moves):
        statements, i = locate(body, loop_id)
        assert statements[i + 1:i + 1 + len(tail)] == tail
        branch = statements[i]["kind"]["Loop"]["statements"][7]["kind"]["Switch"]["branches"][0]
        assert branch["statements"] == new_exit
        del statements[i + 1:i + 1 + len(tail)]
        branch["statements"] = copy.deepcopy(old_exit)
    assert restored == original


def adapt(original, self_test=False):
    data = copy.deepcopy(original)
    fun = declaration(data)
    body = fun["body"]["Structured"]["body"]
    main = body["statements"]
    assert len(main) == 66
    branches = main[41]["kind"]["Switch"]["branches"]
    assert len(branches) == 2
    statements = branches[0]["statements"]
    assert len(statements) == 11
    statement = statements[9]
    loop = statement["kind"]["Loop"]["statements"]
    switch = loop[7]["kind"]["Switch"]["branches"]
    assert len(switch) == 2
    old_exit = copy.deepcopy(switch[0]["statements"])
    assert len(old_exit) == 33 and old_exit[-1]["kind"] == {"Break": 0}
    assert switch[1]["statements"][-1]["kind"] == {"Continue": 0}
    assert statement["span"]["Untagged"]["data"]["beg"]["line"] == 419
    new_exit = [copy.deepcopy(old_exit[-1])]
    tail = copy.deepcopy(old_exit[:-1])
    switch[0]["statements"] = new_exit
    statements[10:10] = tail
    moves = [(statement["id"], copy.deepcopy(tail), old_exit, copy.deepcopy(new_exit))]
    template = new_exit[0]
    next_id = max(n["id"] for n in nodes(data["translated"])
                  if isinstance(n, dict) and isinstance(n.get("id"), int)) + 1
    candidates = [n for n in nodes(body) if isinstance(n, dict) and
                  isinstance(n.get("kind"), dict) and "Loop" in n["kind"] and
                  n["span"]["Untagged"]["data"]["beg"]["line"] == 427]
    assert len(candidates) == 2
    for statement in candidates:
        statements, i = locate(body, statement["id"])
        loop = statement["kind"]["Loop"]["statements"]
        assert len(loop) == 43 and loop[-1]["kind"] == {"Continue": 0}
        switch = loop[7]["kind"]["Switch"]["branches"]
        assert len(switch) == 2 and not switch[1]["statements"]
        for n in nodes(loop[:7] + loop[8:]):
            if isinstance(n, dict) and "kind" in n:
                assert n["kind"] != "Return"
                assert not (isinstance(n["kind"], dict) and "Break" in n["kind"])
        old_exit = copy.deepcopy(switch[0]["statements"])
        assert len(old_exit) == 101 and old_exit[-1]["kind"] == "Return"
        branch_exit = copy.deepcopy(template)
        branch_exit["id"] = next_id
        next_id += 1
        branch_exit["span"] = copy.deepcopy(statement["span"])
        new_exit = [branch_exit]
        switch[0]["statements"] = new_exit
        statements[i + 1:i + 1] = copy.deepcopy(old_exit)
        moves.append((statement["id"], old_exit, old_exit, copy.deepcopy(new_exit)))
    check(original, data, moves)
    rejected = 0
    if self_test:
        mutations = []
        changed = copy.deepcopy(data)
        ss, i = locate(declaration(changed)["body"], moves[-1][0])
        ss[i + 1]["span"] = None
        mutations.append(changed)
        changed = copy.deepcopy(data)
        ss, i = locate(declaration(changed)["body"], moves[-1][0])
        ss[i]["kind"]["Loop"]["statements"][8]["span"] = None
        mutations.append(changed)
        changed = copy.deepcopy(data)
        ss, i = locate(declaration(changed)["body"], moves[-1][0])
        ss[i]["kind"]["Loop"]["statements"][7]["kind"]["Switch"]["branches"][0]["statements"][0]["kind"] = {"Continue": 0}
        mutations.append(changed)
        changed = copy.deepcopy(data)
        changed["has_errors"] = not changed["has_errors"]
        mutations.append(changed)
        for changed in mutations:
            try:
                check(original, changed, moves)
            except AssertionError:
                rejected += 1
            else:
                raise RuntimeError("The reverse checker accepted a mutation")
    return data, {"continuations_hoisted": len(moves),
                  "entire_original_ast_restored": True, "mutations_rejected": rejected}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    raw = args.input.read_bytes()
    result, report = adapt(json.loads(raw), args.self_test)
    output = json.dumps(result, separators=(",", ":")).encode()
    args.output.write_bytes(output)
    report.update(original_sha256=hashlib.sha256(raw).hexdigest(),
                  adapted_sha256=hashlib.sha256(output).hexdigest())
    print(json.dumps(report))


if __name__ == "__main__":
    main()
