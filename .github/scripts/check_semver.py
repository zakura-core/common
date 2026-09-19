#!/usr/bin/env python3
"""Run semver checks with named feature removals accepted in minor releases."""

import argparse
import codecs
import contextlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import threading
import time


ALLOWLIST = Path(".github/semver-feature-removals.json")


class ReportFormatError(ValueError):
    """The checker report cannot be safely matched to an exception."""


def unique_keys(pairs):
    """Reject duplicate keys instead of silently replacing policy entries."""
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
        if not package or not isinstance(features, dict):
            raise ValueError(f"invalid feature removal entries for {package!r}")
        for feature, reason in features.items():
            if not feature or not isinstance(reason, str) or not reason.strip():
                raise ValueError(f"missing reason for {package}/{feature}")
    return allowlist


def accepted_removals(package, output, allowed_features):
    """Match one feature_missing failure, allowing unrelated warning sections.

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
    if len(checking) != 1 or checking[0][0] != package:
        raise ReportFormatError("expected one package version comparison")
    if checking[0][1] not in {"no", "patch", "minor", "major"}:
        raise ReportFormatError("unrecognized version change type")
    if checking[0][1] != "minor":
        return []

    counts = re.findall(
        r"^\s*Checked \[[^\]\n]+\] (\d+) checks: (\d+) pass, (\d+) fail, "
        r"(\d+) warn, \d+ skip\s*$",
        output,
        re.MULTILINE,
    )
    headers = re.findall(r"^--- failure (\S+): .* ---$", output, re.MULTILINE)
    warnings = re.findall(r"^--- warning (\S+): .* ---$", output, re.MULTILINE)
    if len(counts) != 1:
        raise ReportFormatError("missing or repeated check counts")
    total, passed, failed, warned = map(int, counts[0])
    if (
        total != passed + failed + warned
        or failed != len(headers)
        or warned != len(warnings)
        or len(set(headers + warnings)) != failed + warned
    ):
        raise ReportFormatError("check counts do not match diagnostic sections")
    if headers != ["feature_missing"]:
        return []

    summaries = re.findall(r"^\s*Summary (.*)$", output, re.MULTILINE)
    if summaries != [
        "semver requires new major version: 1 major and 0 minor checks failed"
    ]:
        raise ReportFormatError("unexpected failure summary")

    warning_counts = re.findall(
        r"^\s*Warning produced (\d+) major and (\d+) minor level warnings$",
        output,
        re.MULTILINE,
    )
    if (
        warned
        and (len(warning_counts) != 1 or sum(map(int, warning_counts[0])) != warned)
    ) or (not warned and warning_counts):
        raise ReportFormatError("unexpected warning summary")

    finished_pattern = r"[ \t]*Finished \[[^\]\n]+\] " + re.escape(package)
    if len(
        re.findall("^" + finished_pattern + "$", output, re.MULTILINE)
    ) != 1 or not re.fullmatch(finished_pattern, output.rstrip().splitlines()[-1]):
        raise ReportFormatError("missing or unexpected report footer")

    # Status lines can appear between findings because they use stderr.
    # Remove only recognized status lines before separating lint sections.
    report = re.sub(
        r"^[ \t]*(?:Summary "
        + re.escape(summaries[0])
        + r"|Warning produced \d+ major and \d+ minor level warnings"
        + r"|produced warnings suggest new (?:major|minor) version)\n",
        "",
        output,
        flags=re.MULTILINE,
    )
    report = re.sub("^" + finished_pattern + r"\n?", "", report, flags=re.MULTILINE)
    sections = re.split(
        r"^--- (failure|warning) (\S+): .* ---$", report, flags=re.MULTILINE
    )
    findings = []
    for index in range(1, len(sections), 3):
        kind, _, body = sections[index : index + 3]
        parts = body.split("Failed in:")
        if len(parts) != 2 or not parts[1].strip():
            raise ReportFormatError("missing or repeated findings section")
        if kind == "warning":
            continue
        findings = [line.strip() for line in parts[1].splitlines() if line.strip()]

    features = []
    for line in findings:
        finding = re.fullmatch(r"feature (\S+) in the package's Cargo.toml", line)
        if finding is None:
            raise ReportFormatError("unrecognized feature removal finding")
        features.append(finding[1])

    if not features or len(features) != len(set(features)):
        raise ReportFormatError("missing or repeated feature removal finding")
    if not set(features).issubset(allowed_features):
        return []
    return features


def run_command(command, cwd, timeout):
    """Stream decoded output and bound the lifetime of the command and its pipes."""
    process = subprocess.Popen(
        command,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        start_new_session=os.name == "posix",
    )
    output, read_errors = [], []

    def stream_output():
        """Decode across chunk boundaries without losing logs to invalid bytes."""
        decoder = codecs.getincrementaldecoder("utf-8")(errors="replace")
        try:
            while chunk := process.stdout.read1(8192):
                text = decoder.decode(chunk)
                output.append(text)
                print(text, end="", flush=True)
            text = decoder.decode(b"", final=True)
            output.append(text)
            print(text, end="", flush=True)
        except Exception as error:
            read_errors.append(error)

    reader = threading.Thread(target=stream_output, daemon=True)
    try:
        reader.start()
        deadline = time.monotonic() + timeout
        process.wait(timeout=timeout)
        reader.join(timeout=max(0, deadline - time.monotonic()))
        if reader.is_alive():
            raise subprocess.TimeoutExpired(command, timeout)
        if read_errors:
            raise read_errors[0]
    except BaseException:
        # A compiler child can retain the pipe after Cargo exits. On CI and
        # macOS, kill the whole session on timeout or cancellation.
        with contextlib.suppress(ProcessLookupError):
            if os.name == "posix":
                os.killpg(process.pid, signal.SIGKILL)
            else:
                process.kill()
        process.wait(timeout=5)
        if reader.ident is not None:
            reader.join(timeout=5)
        raise
    finally:
        if not reader.is_alive():
            process.stdout.close()
    return subprocess.CompletedProcess(command, process.returncode, "".join(output))


def check_package(
    package, allowlist, repo_root, *, baseline_version=None, default_features=False
):
    """Keep tool failures intact and apply policy only to completed semver checks."""
    version = run_command(
        ["cargo", "semver-checks", "--version"], repo_root, timeout=30
    )
    if version.returncode:
        return version.returncode
    command = ["cargo", "semver-checks", "--package", package, "--color", "never"]
    if default_features:
        command.append("--default-features")
    if baseline_version:
        command.extend(["--baseline-version", baseline_version])
    result = run_command(command, repo_root, timeout=25 * 60)
    # 100 means completed checks found denied semver violations. Compilation,
    # resolution, and other tool failures must retain their original status.
    if result.returncode != 100:
        return result.returncode

    allowed_features = allowlist.get(package, {})
    try:
        accepted = accepted_removals(package, result.stdout, allowed_features)
    except ReportFormatError as error:
        print(
            f"Semver report format not recognized: {error}. Check the tool version printed above.",
            file=sys.stderr,
        )
        return result.returncode
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


def handle_termination(signum, _frame):
    """Let command cleanup run when CI terminates the wrapper."""
    raise SystemExit(128 + signum)


def main():
    """Load the policy and run a bounded check from the repository root."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", required=True)
    parser.add_argument(
        "--baseline-version", help="Published baseline for release checks"
    )
    parser.add_argument(
        "--default-features", action="store_true", help="Match CI's feature selection"
    )
    args = parser.parse_args()
    repo_root = Path(__file__).resolve().parents[2]
    previous_handler = signal.signal(signal.SIGTERM, handle_termination)
    try:
        allowlist = load_allowlist(repo_root / ALLOWLIST)
        return check_package(
            args.package,
            allowlist,
            repo_root,
            baseline_version=args.baseline_version,
            default_features=args.default_features,
        )
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"Semver check failed: {error}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("Semver check interrupted.", file=sys.stderr)
        return 130
    finally:
        signal.signal(signal.SIGTERM, previous_handler)


if __name__ == "__main__":
    sys.exit(main())
