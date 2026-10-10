#!/usr/bin/env python3
"""Build a paired arithmetic benchmark against a pinned legacy source archive."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import statistics
import subprocess

ROOT = Path(__file__).resolve().parents[2]
REVISION = "80d39d9b1c41ce6c21c87f53c42deb317ce06e84"


def environment():
    state = {"time": datetime.now(timezone.utc).isoformat()}
    if platform.system() == "Darwin":
        for name, args in (("power", ["pmset", "-g", "batt"]),
                           ("thermal", ["pmset", "-g", "therm"])):
            result = subprocess.run(args, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, check=False)
            state[name] = result.stdout
    return state


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--build-only", action="store_true")
    parser.add_argument("--measure-only", action="store_true")
    parser.add_argument("--blocks", type=int, default=4)
    parser.add_argument("--control-control", action="store_true")
    args = parser.parse_args()
    if args.blocks < 1:
        parser.error("--blocks must be positive")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    binary = output / "arithmetic-bench"
    fixture = ROOT / "tools/orchard-preparation/fixtures/key-agreement.bin"
    if not args.measure_only:
        source = output / "legacy"
        source.mkdir(exist_ok=True)
        archive = output / "source.tar"
        subprocess.run(["git", "archive", REVISION, "-o", str(archive)], cwd=ROOT, check=True)
        subprocess.run(["tar", "-xf", str(archive), "-C", str(source)], check=True)
        project = output / "benchmark"
        (project / "src").mkdir(parents=True, exist_ok=True)
        shutil.copy2(Path(__file__).with_name("bench.rs"), project / "src/main.rs")
        (project / "Cargo.toml").write_text(f'''[package]
name = "orchard-arithmetic-bench"
version = "0.0.0"
edition = "2024"
[workspace]
[dependencies]
ff = "0.14"
group = "0.14"
pasta_curves = {{ package = "zakura-pasta-curves", path = "{source}/crates/pasta_curves", features = ["glv"] }}
udon = {{ package = "zakura-udon", path = "{ROOT}/crates/udon" }}
''')
        shutil.copy2(source / "Cargo.lock", project / "Cargo.lock")
        subprocess.run(["cargo", "build", "--release", "--offline", "--manifest-path", str(project / "Cargo.toml")], cwd=ROOT, check=True)
        shutil.copy2(project / "target/release/orchard-arithmetic-bench", binary)
        metadata = {"revision": REVISION, "platform": platform.platform(), "workers": 1,
                    "backend": "default portable ARM64; neither crate enables aarch64-asm",
                    "rustc": subprocess.check_output(["rustc", "-Vv"], text=True),
                    "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
                    "fixture_sha256": hashlib.sha256(fixture.read_bytes()).hexdigest()}
        (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
        paths = [p for p in (ROOT / "crates/udon").rglob("*") if p.is_file()]
        paths += [Path(__file__), Path(__file__).with_name("bench.rs"), ROOT / "Cargo.lock"]
        (output / "source-hashes.json").write_text(json.dumps({
            str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)
        }, indent=2) + "\n")
        (output / "candidate.diff").write_bytes(subprocess.check_output(["git", "diff", "HEAD"], cwd=ROOT))
    if args.build_only:
        return
    rows = []
    name = "noise" if args.control_control else "paired"
    environments = []
    for block in range(args.blocks):
        for position, variant in enumerate("ABBA"):
            mode = "control" if variant == "A" or args.control_control else "candidate"
            before = environment()
            raw = subprocess.check_output([str(binary), mode, str(fixture)], text=True)
            environments.append({"block": block, "position": position, "variant": variant,
                                 "before": before, "after": environment()})
            (output / f"{name}-environment.json").write_text(json.dumps(environments, indent=2) + "\n")
            (output / f"{'noise' if args.control_control else 'paired'}-{block}-{position}.csv").write_text(raw)
            for line in raw.splitlines():
                case, n, iterations, ns = line.split(",")
                rows.append({"block": block, "position": position, "variant": variant, "case": case, "n": int(n), "ns": int(ns) / int(iterations)})
    summary = []
    for case, n in sorted({(r["case"], r["n"]) for r in rows}):
        values = {v: statistics.median(r["ns"] for r in rows if r["case"] == case and r["n"] == n and r["variant"] == v) for v in "AB"}
        pairs = []
        for block in range(args.blocks):
            pair = {v: statistics.mean(r["ns"] for r in rows if r["case"] == case
                                      and r["n"] == n and r["variant"] == v
                                      and r["block"] == block) for v in "AB"}
            pairs.append(pair["B"] / pair["A"])
        summary.append({"case": case, "n": n, **values,
                        "paired_ratios": pairs, "ratio": statistics.median(pairs)})
    (output / f"{name}.json").write_text(json.dumps({"rows": rows, "summary": summary}, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
