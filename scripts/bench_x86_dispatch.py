#!/usr/bin/env python3
"""Compare warmed automatic dispatch, forced assembly, and portable arithmetic.

Build existing Criterion targets before timing, rotate mode order across three
rounds, and save raw samples plus a CSV of medians and ranges. Measurements
require an isolated Linux x86-64 host with BMI2 and ADX. --smoke only exercises
portable workloads, without producing timing results, and works on other hosts.
"""

import argparse
import csv
import json
import os
import platform
import statistics
import subprocess
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODES = {"automatic": [], "forced": ["x86_64-asm"], "portable": ["portable"]}
PASTA_FILTER = (
    r"^F[qp]/(add_assign|mul_assign(/dependent-chain)?|"
    r"square(/dependent-chain)?|invert)$"
)
UDON_FILTER = (
    r"^F[qp]/(arithmetic/(add|mul|square)|"
    r"corpus/mul_(dependent|independent)|ProductSum/finish)$"
)
TARGETS = [
    ("zakura-pasta-curves", "fp", PASTA_FILTER, 6),
    ("zakura-pasta-curves", "fq", PASTA_FILTER, 6),
    ("zakura-udon", "field", UDON_FILTER, 12),
]


def require_supported_cpu():
    """Check every advertised processor before executing forced assembly."""
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise ValueError("timing requires native Linux x86-64; use --smoke elsewhere")
    cpuinfo = Path("/proc/cpuinfo").read_text()
    flags = [line.split(":", 1)[1].split() for line in cpuinfo.splitlines()
             if line.startswith("flags")]
    if not flags or any(not {"bmi2", "adx"}.issubset(row) for row in flags):
        raise ValueError("all processors must expose BMI2 and ADX for forced assembly")
    return cpuinfo


def command(arguments, *, environment, log, deadline):
    """Retain command output and stop at the experiment's one-hour budget."""
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise TimeoutError("one-hour benchmark budget exhausted")
    print("Running:", " ".join(map(str, arguments)), flush=True)
    with log.open("w") as handle:
        result = subprocess.run(arguments, cwd=ROOT, env=environment, text=True,
                                stdout=handle, stderr=subprocess.STDOUT,
                                timeout=min(600, remaining))
    if result.returncode:
        raise RuntimeError(f"command failed; inspect {log}")
    return log.read_text()


def collect_estimates(directory, expected_count):
    """Fail if a filter silently selected fewer workloads or duplicated an ID."""
    estimates = {}
    for path in directory.glob("**/new/estimates.json"):
        identity = json.loads(path.with_name("benchmark.json").read_text())["full_id"]
        if identity in estimates:
            raise ValueError(f"duplicate benchmark: {identity}")
        estimates[identity] = json.loads(path.read_text())["median"]["point_estimate"]
    if len(estimates) != expected_count:
        raise ValueError(f"expected {expected_count} workloads, found {len(estimates)}")
    return estimates


def summarize(samples, rounds):
    """Report ns per workload; percentages compare automatic to each alternative."""
    by_workload = {}
    for sample in samples:
        key = (sample["target"], sample["workload"])
        modes = by_workload.setdefault(key, {mode: [] for mode in MODES})
        modes[sample["mode"]].append(sample["nanoseconds"])
    if not by_workload:
        raise ValueError("no benchmark measurements")
    rows = []
    for (target, workload), modes in sorted(by_workload.items()):
        row = {"target": target, "workload": workload}
        for mode, values in modes.items():
            if len(values) != rounds:
                raise ValueError(f"incomplete runs for {target}/{workload}/{mode}")
            row[f"{mode}_median_ns"] = statistics.median(values)
            row[f"{mode}_min_ns"] = min(values)
            row[f"{mode}_max_ns"] = max(values)
        automatic = row["automatic_median_ns"]
        for baseline in ("forced", "portable"):
            row[f"automatic_vs_{baseline}_percent"] = (
                100 * (automatic / row[f"{baseline}_median_ns"] - 1)
            )
        rows.append(row)
    return rows


def benchmark(output, *, smoke, isolated):
    if not smoke and not isolated:
        raise ValueError("use --isolated only on a host reserved for this measurement")
    cpuinfo = None if smoke else require_supported_cpu()
    output = output.resolve()
    if output.is_relative_to(ROOT):
        raise ValueError("write benchmark results outside the repository")
    output.mkdir(parents=True, exist_ok=False)
    deadline = time.monotonic() + 3600
    environment = os.environ.copy()
    # Baseline code generation is essential: enabling these CPU instructions
    # globally would fold away detection and invalidate the comparison.
    for name in ("CARGO_ENCODED_RUSTFLAGS", "RUSTFLAGS", "RUSTC_BOOTSTRAP"):
        environment.pop(name, None)
    environment["CARGO_INCREMENTAL"] = "0"
    host = subprocess.check_output(["rustc", "-vV"], text=True)
    triple = next(line.removeprefix("host: ") for line in host.splitlines()
                  if line.startswith("host: "))
    environment["CARGO_BUILD_TARGET"] = triple
    environment["RUSTFLAGS"] = "-C target-cpu=x86-64" if not smoke else ""
    environment["CARGO_PROFILE_BENCH_DEBUG_ASSERTIONS"] = "false"
    environment["CARGO_PROFILE_BENCH_LTO"] = "false"
    environment["CARGO_PROFILE_BENCH_CODEGEN_UNITS"] = "1"
    environment["CARGO_PROFILE_BENCH_OPT_LEVEL"] = "3"
    metadata = {
        "started_unix_seconds": time.time(),
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT)),
        "host": platform.node(), "cpuinfo": cpuinfo, "rustc": host,
        "cargo": subprocess.check_output(["cargo", "--version"], text=True).strip(),
        "smoke": smoke, "rounds": 0 if smoke else 3,
        "rustflags": environment["RUSTFLAGS"], "mode_order": [],
        "profile": {"optimization": 3, "lto": False, "codegen_units": 1, "debug_assertions": False},
    }
    metadata_path = output / "metadata.json"
    metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")
    if metadata["dirty"] and not smoke:
        raise ValueError("commit the benchmark source before collecting measurements")

    # All compilation finishes before measurement, with separate artifacts per
    # feature mode so Cargo feature unification cannot mix implementations.
    executables = {}
    for mode in (["portable"] if smoke else MODES):
        environment["CARGO_TARGET_DIR"] = str(output / "build" / mode)
        for package, target, _, _ in TARGETS:
            arguments = ["cargo", "bench", "--locked", "--no-run", "--message-format=json",
                         "--target", triple, "-p", package, "--bench", target]
            if MODES[mode]:
                arguments += ["--features", ",".join(MODES[mode])]
            built = command(arguments, environment=environment,
                            log=output / f"build-{mode}-{target}.log", deadline=deadline)
            artifacts = [json.loads(line) for line in built.splitlines() if line.startswith("{")]
            executables[mode, target] = next(
                item["executable"] for item in artifacts
                if item.get("reason") == "compiler-artifact"
                and item["target"]["name"] == target and item.get("executable")
            )

    samples = []
    for repeat in range(1 if smoke else 3):
        modes = ["portable"] if smoke else list(MODES)
        modes = modes[repeat:] + modes[:repeat]
        metadata["mode_order"].append(modes)
        metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")
        for mode in modes:
            for _, target, workload_filter, expected_count in TARGETS:
                raw = output / f"run-{repeat + 1}" / mode / target
                environment["CRITERION_HOME"] = str(raw)
                arguments = [executables[mode, target], workload_filter]
                arguments += (["--test"] if smoke else [
                    "--bench", "--noplot", "--sample-size", "30",
                    "--warm-up-time", "1", "--measurement-time", "2",
                ])
                text = command(arguments, environment=environment,
                               log=output / f"run-{repeat + 1}-{mode}-{target}.log", deadline=deadline)
                if smoke:
                    if text.count("Success") != expected_count:
                        raise ValueError(f"smoke test did not exercise all {target} workloads")
                    continue
                for workload, nanoseconds in collect_estimates(raw, expected_count).items():
                    samples.append(dict(target=target, workload=workload, mode=mode,
                                        repeat=repeat + 1, nanoseconds=nanoseconds))
                (output / "samples.json").write_text(json.dumps(samples, indent=2) + "\n")
    if smoke:
        print("Portable workload smoke test passed; no timing results were collected.")
        return
    current_commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if current_commit != metadata["commit"] or subprocess.check_output(
        ["git", "status", "--porcelain"], cwd=ROOT
    ):
        raise ValueError("source changed during measurement; discard these timing results")
    rows = summarize(samples, 3)
    with (output / "summary.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(f"Results: {output / 'summary.csv'} (positive percentages mean automatic is slower)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="new directory outside the repository")
    parser.add_argument("--isolated", action="store_true", help="confirm this host is reserved for measurement")
    parser.add_argument("--smoke", action="store_true", help="portable correctness check; no timing claims")
    args = parser.parse_args()
    benchmark(args.output, smoke=args.smoke, isolated=args.isolated)


if __name__ == "__main__":
    main()
