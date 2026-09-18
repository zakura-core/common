#!/usr/bin/env python3
"""Check the default public API with exact exceptions for unused features."""

import argparse
from contextlib import contextmanager
import json
from pathlib import Path
import re
import subprocess
import tomllib


POLICY = Path(__file__).resolve().parents[1] / "semver-feature-exceptions.toml"


def excluded_features(policy, packages):
    if set(policy) != {"excluded_features"}:
        raise ValueError("policy must contain only an excluded_features table")
    exclusions = policy["excluded_features"]
    if not isinstance(exclusions, dict):
        raise ValueError("excluded_features must be a table")
    for name, features in exclusions.items():
        if name not in packages:
            raise ValueError(f"unknown workspace package: {name}")
        if not isinstance(features, dict):
            raise ValueError(f"{name}: expected a feature-to-reason table")
        for feature, reason in features.items():
            if not re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_+.-]*", feature):
                raise ValueError(f"{name}: expected an exact feature name: {feature}")
            if (
                feature == "default"
                or not isinstance(reason, str)
                or not reason.strip()
            ):
                raise ValueError(
                    f"{name}/{feature}: default cannot be excluded; a reason is required"
                )

        # Follow local feature aliases so an indirect default cannot be excluded.
        definitions = packages[name]["features"]
        pending = ["default"]
        enabled = set()
        while pending:
            feature = pending.pop()
            if feature not in enabled:
                enabled.add(feature)
                pending.extend(definitions.get(feature, []))
        if enabled.intersection(features):
            raise ValueError(
                f"{name}: excluded features must not be enabled by default"
            )
    return exclusions


@contextmanager
def feature_name_exceptions(manifest, features):
    """Temporarily restore only removed feature names, never their code or activation."""
    original = manifest.read_bytes()
    document = tomllib.loads(original.decode())
    missing = sorted(set(features).difference(document.get("features", {})))
    if not missing:
        yield
        return

    text = original.decode()
    entries = "".join(f"{json.dumps(feature)} = []\n" for feature in missing)
    header = re.search(r"(?m)^\[features\][ \t]*(?:#[^\n]*)?$", text)
    if header:
        text = text[: header.end()] + "\n" + entries + text[header.end() :]
    elif "features" not in document:
        text += "\n[features]\n" + entries
    else:
        raise ValueError(f"{manifest}: expected an explicit [features] table")

    print(
        f"Semver feature-name exceptions in {manifest}: {', '.join(missing)}",
        flush=True,
    )
    try:
        manifest.write_text(text)
        yield
    finally:
        manifest.write_bytes(original)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", required=True)
    parser.add_argument("--policy", type=Path, default=POLICY)
    parser.add_argument(
        "--baseline-root", type=Path, help="local baseline for regression tests"
    )
    args = parser.parse_args()

    metadata = json.loads(
        subprocess.check_output(
            ["cargo", "metadata", "--no-deps", "--locked", "--format-version", "1"],
            text=True,
        )
    )
    packages = {
        p["name"]: p
        for p in metadata["packages"]
        if p["id"] in metadata["workspace_members"]
    }
    exclusions = excluded_features(tomllib.loads(args.policy.read_text()), packages)
    package = packages[args.package]
    command = [
        "cargo",
        "semver-checks",
        "--package",
        args.package,
        "--default-features",
    ]
    if args.baseline_root:
        command.extend(["--baseline-root", str(args.baseline_root.resolve())])
    with feature_name_exceptions(
        Path(package["manifest_path"]), exclusions.get(args.package, {})
    ):
        return subprocess.run(command, check=False).returncode


if __name__ == "__main__":
    raise SystemExit(main())
