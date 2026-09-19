#!/usr/bin/env python3
"""Run semver checks with named feature removals accepted in minor releases."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys


ALLOWLIST = Path(".github/semver-feature-removals.json")


def load_allowlist(path):
    """Require an exact package, feature, and nonempty reason for each entry."""
    policy = json.loads(path.read_text())
    if not isinstance(policy, dict):
        raise ValueError("feature removal allowlist must be an object")
    for package, features in policy.items():
        if not package or not isinstance(features, dict):
            raise ValueError(f"invalid feature removal entries for {package!r}")
        for feature, reason in features.items():
            if not feature or not isinstance(reason, str) or not reason.strip():
                raise ValueError(f"missing reason for {package}/{feature}")
    return policy


def accepted_removals(package, report, allowed):
    """Accept only a complete report whose sole failure is approved feature names.

    There is no stable structured report. Cross-check the failure count and
    summary, and reject unknown finding text. Warning sections are irrelevant.
    """
    checking = re.findall(
        r"^\s*Checking (\S+) v\S+ -> v\S+ \((\w+) change\)$", report, re.M
    )
    failures = re.findall(r"^--- failure (\S+): .* ---$", report, re.M)
    counts = re.findall(
        r"^\s*Checked \[[^\]\n]+\] \d+ checks: \d+ pass, (\d+) fail, \d+ warn, \d+ skip$",
        report,
        re.M,
    )
    summary = (
        "Summary semver requires new major version: 1 major and 0 minor checks failed"
    )
    footer = r"Finished \[[^\]\n]+\] " + re.escape(package)
    if len(checking) != 1 or len(counts) != 1 or int(counts[0]) != len(failures):
        raise ValueError("missing or inconsistent check results")
    if checking[0] != (package, "minor") or failures != ["feature_missing"]:
        return []
    if re.findall(r"^[ \t]*(Summary .*)$", report, re.M) != [summary]:
        raise ValueError("unexpected failure summary")
    if not re.fullmatch(footer, report.rstrip().splitlines()[-1].strip()):
        raise ValueError("missing report footer")

    body = report.split("--- failure feature_missing:", 1)[1]
    body = re.split(r"^--- warning \S+: .* ---$", body, flags=re.M)[0]
    parts = body.split("Failed in:\n")
    if len(parts) != 2:
        raise ValueError("missing feature findings")
    # Status lines use stderr and may arrive between stdout findings.
    findings = re.sub(
        r"^[ \t]*(?:"
        + re.escape(summary)
        + "|"
        + footer
        + r"|Warning produced \d+ major and \d+ minor level warnings"
        + r"|produced warnings suggest new (?:major|minor) version)\n?",
        "",
        parts[1],
        flags=re.M,
    )
    lines = [line.strip() for line in findings.splitlines() if line.strip()]
    features = re.findall(
        r"^\s*feature (\S+) in the package's Cargo.toml$", findings, re.M
    )
    if not features or len(features) != len(lines):
        raise ValueError("unrecognized feature findings")
    return features if set(features).issubset(allowed) else []


def check_result(package, status, report, allowed):
    """Override only exit 100, which denotes completed, denied semver checks."""
    if status != 100 or not allowed:
        return status
    try:
        accepted = accepted_removals(package, report, allowed)
    except ValueError as error:
        print(
            f"Semver report format not recognized: {error}. Check the tool version above.",
            file=sys.stderr,
        )
        return status
    if not accepted:
        print(
            "Semver failure is not covered by the feature removal allowlist.",
            file=sys.stderr,
        )
        return status
    for feature in accepted:
        print(
            f"Accepted minor-release removal: {package}/{feature}: {allowed[feature]}"
        )
    return 0


def main():
    """Stream the checker log and apply policy to its completed report."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", required=True)
    parser.add_argument("--baseline-version")
    parser.add_argument("--default-features", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    policy = load_allowlist(root / ALLOWLIST)
    subprocess.run(["cargo", "semver-checks", "--version"], cwd=root, check=True)
    command = ["cargo", "semver-checks", "--package", args.package, "--color", "never"]
    if args.baseline_version:
        command.extend(["--baseline-version", args.baseline_version])
    if args.default_features:
        command.append("--default-features")
    # Keep Cargo in the foreground process group. CI owns the job timeout and
    # cancellation, and a local Ctrl-C reaches Cargo and its compiler children.
    with subprocess.Popen(
        command,
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        errors="replace",
    ) as process:
        report = []
        for line in process.stdout:
            print(line, end="", flush=True)
            report.append(line)
        return check_result(
            args.package, process.wait(), "".join(report), policy.get(args.package, {})
        )


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        sys.exit(f"Semver check failed: {error}")
    except KeyboardInterrupt:
        sys.exit(130)
