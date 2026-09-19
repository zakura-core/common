#!/usr/bin/env python3
"""Run semver checks with named feature removals accepted in minor releases."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys


ALLOWLIST = Path(".github/semver-feature-removals.json")


def unique_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate allowlist key: {key}")
        result[key] = value
    return result


def load_allowlist(path):
    """Require a reason for every exact package and feature pair."""
    allowlist = json.loads(path.read_text(), object_pairs_hook=unique_keys)
    if not isinstance(allowlist, dict):
        raise ValueError("feature removal allowlist must be an object")
    for package, features in allowlist.items():
        if not package or not isinstance(features, dict) or not features:
            raise ValueError(f"invalid feature removal entries for {package!r}")
        for feature, reason in features.items():
            if not feature or not isinstance(reason, str) or not reason.strip():
                raise ValueError(f"missing reason for {package}/{feature}")
    return allowlist


def accepted_removals(package, output, allowed_features):
    """Accept only a complete, recognized report with one feature_missing failure.

    cargo-semver-checks has no stable structured diagnostics interface. Require
    matching check counts, failure headers, summary, and every finding rather
    than accepting an exit code or a substring. An unknown format stays red.
    """
    if not allowed_features:
        return []

    checking = re.findall(
        r"^\s*Checking (\S+) v\S+ -> v\S+ \(([^)]+) change\)\s*$",
        output,
        re.MULTILINE,
    )
    if checking != [(package, "minor")]:
        return []

    counts = re.findall(
        r"^\s*Checked \[[^\]\n]+\] \d+ checks: \d+ pass, (\d+) fail, "
        r"\d+ warn, \d+ skip\s*$",
        output,
        re.MULTILINE,
    )
    headers = re.findall(r"^--- failure (\S+): .* ---$", output, re.MULTILINE)
    if counts != ["1"] or headers != ["feature_missing"]:
        return []

    summaries = re.findall(r"^\s*Summary (.*)$", output, re.MULTILINE)
    if summaries != [
        "semver requires new major version: 1 major and 0 minor checks failed"
    ]:
        return []

    # Findings may straddle the summary when stdout and stderr are buffered.
    # Accept no other content after "Failed in:" except the known footer.
    failure = output.split("--- failure feature_missing: ", 1)[1]
    sections = failure.split("Failed in:")
    if len(sections) != 2:
        return []
    findings = []
    finished = 0
    for line in sections[1].splitlines():
        line = line.strip()
        if not line or line == "Summary " + summaries[0]:
            continue
        if re.fullmatch(r"Finished \[[^\]\n]+\] " + re.escape(package), line):
            finished += 1
            continue
        finding = re.fullmatch(r"feature (\S+) in the package's Cargo.toml", line)
        if finding is None:
            return []
        findings.append(finding[1])

    if (
        finished != 1
        or not findings
        or len(findings) != len(set(findings))
        or not set(findings).issubset(allowed_features)
    ):
        return []
    return findings


def check_package(package, allowlist, repo_root):
    result = subprocess.run(
        [
            "cargo",
            "semver-checks",
            "--package",
            package,
            "--default-features",
            "--color",
            "never",
        ],
        cwd=repo_root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=25 * 60,
    )
    print(result.stdout, end="", flush=True)
    # 100 means completed checks found denied semver violations. Compilation,
    # resolution, and other tool failures must retain their original status.
    if result.returncode != 100:
        return result.returncode

    allowed_features = allowlist.get(package, {})
    accepted = accepted_removals(package, result.stdout, allowed_features)
    if not accepted:
        print(
            "Semver failure is not covered by the feature removal allowlist.",
            file=sys.stderr,
        )
        return result.returncode

    for feature in accepted:
        print(
            f"Accepted minor-release removal: {package}/{feature}: {allowed_features[feature]}"
        )
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", required=True)
    args = parser.parse_args()
    repo_root = Path(__file__).resolve().parents[2]
    try:
        allowlist = load_allowlist(repo_root / ALLOWLIST)
        return check_package(args.package, allowlist, repo_root)
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"Semver check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
