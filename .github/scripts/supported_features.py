#!/usr/bin/env python3
"""List CI features with the default cryptographic implementations selected."""
import json
import subprocess
import sys


def supported_features(metadata, selected):
    members = set(metadata["workspace_members"])
    defaults = {"backend-halo2", "pallas-pasta"}
    packages = [package for package in metadata["packages"]
                if package["id"] in members
                and ("--workspace" in selected or package["name"] in selected)]
    if not packages:
        raise ValueError("no workspace packages found for the selection")
    return sorted(
        f"{package['name']}/{feature}"
        for package in packages
        for feature in package["features"]
        if not feature.startswith(("backend-", "pallas-")) or feature in defaults
    )


if __name__ == "__main__":
    metadata = json.loads(subprocess.check_output([
        "cargo", "metadata", "--no-deps", "--format-version", "1", "--locked"
    ], text=True))
    try:
        features = supported_features(metadata, set(sys.argv[1:]))
    except ValueError as error:
        raise SystemExit(str(error)) from error
    print(",".join(features))
