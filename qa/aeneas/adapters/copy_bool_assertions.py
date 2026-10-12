"""Read scalar Boolean assertion operands by Copy instead of Move.

Bool implements Copy and has no drop behavior. This preserves its value and
all assertion branches. It avoids Aeneas reading a concrete Move operand twice
in eval_assertion followed by eval_assertion_concrete. No assertion is erased.
"""
import argparse
import copy
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("This translation adapter requires Python assertions")


def adapt(data):
    original = copy.deepcopy(data)
    changed = []

    def walk(value, path=()):
        if isinstance(value, dict):
            if "Assert" in value:
                operand = value["Assert"]["assert"]["cond"]
                if set(operand) == {"Move"}:
                    place = operand["Move"]
                    assert place["ty"] == {"Untagged": {"Scalar": "Bool"}}
                    assert set(place["kind"]) == {"Local"}
                    operand.clear()
                    operand["Copy"] = place
                    changed.append(path)
            for key, child in value.items():
                walk(child, (*path, key))
        elif isinstance(value, list):
            for index, child in enumerate(value):
                walk(child, (*path, index))

    walk(data)
    restored = copy.deepcopy(data)
    for path in changed:
        target = restored
        for key in path:
            target = target[key]
        operand = target["Assert"]["assert"]["cond"]
        operand["Move"] = operand.pop("Copy")
    assert restored == original
    return {
        "copied_boolean_assertions": len(changed),
        "all_assertions_and_other_AST_unchanged": True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--expected", type=int, required=True)
    args = parser.parse_args()
    data = json.loads(args.source.read_text())
    report = adapt(data)
    assert report["copied_boolean_assertions"] == args.expected
    args.output.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
