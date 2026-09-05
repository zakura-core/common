#!/usr/bin/env python3
"""Collect transaction latency runs and retain every sample."""

import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
hosts = ["mac-os-1", "linux-2"]
result = {"units": "nanoseconds", "hosts": {}, "runs": []}
for host in hosts:
    directory = root / host
    result["hosts"][host] = {
        p.name: p.read_text()
        for p in sorted((directory / "results").glob("*.txt"))
    }
    for name in ["profile-six.log"]:
        path = directory / name
        if path.exists():
            result["hosts"][host][name] = path.read_text()
    for estimate in sorted((directory / "target" / "criterion").glob("*/*/*/estimates.json")):
        label = estimate.parent.name
        match = re.fullmatch(
            rf"{host}-t(4|6)-(control|inversion|lazy|planned|configured|streamed|final)-(.+)",
            label,
        )
        if match is None:
            continue
        threads, variant, leg = match.groups()
        result["runs"].append({
            "host": host, "threads": int(threads), "variant": variant,
            "leg": leg, "label": label,
            "group": estimate.parent.parent.parent.name,
            "case": estimate.parent.parent.name,
            "estimates": json.loads(estimate.read_text()),
            "sample": json.loads((estimate.parent / "sample.json").read_text()),
        })
json.dump(result, sys.stdout, indent=2)
print()
