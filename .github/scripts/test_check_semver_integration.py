#!/usr/bin/env python3
"""Prove the exception boundary with cargo-semver-checks on tiny local crates."""

from pathlib import Path
import subprocess
import sys
import tempfile


WRAPPER = Path(__file__).with_name("check_semver.py").resolve()


def crate(root, features, source):
    root.mkdir()
    (root / "src").mkdir()
    manifest = root / "Cargo.toml"
    manifest.write_text(
        '[package]\nname = "semver-policy-fixture"\nversion = "1.0.0"\nedition = "2021"\n'
        + "[features]\ndefault = []\n"
        + features
    )
    (root / "src/lib.rs").write_text(source)
    subprocess.run(["cargo", "generate-lockfile", "--offline"], cwd=root, check=True)
    return manifest


def main():
    cases = [
        ("allowed-feature", "supported = []\n", "pub fn supported() {}\n", True, None),
        ("unlisted-feature", "", "pub fn supported() {}\n", False, "feature_missing"),
        ("supported-api", "supported = []\n", "", False, "function_missing"),
    ]
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        baseline = root / "baseline"
        crate(
            baseline,
            "unused = []\nsupported = []\n",
            'pub fn supported() {}\n#[cfg(feature = "unused")]\npub fn experimental() {}\n',
        )
        policy = root / "policy.toml"
        policy.write_text(
            '[excluded_features.semver-policy-fixture]\nunused = "Unused experimental API"\n'
        )

        for name, features, source, expected_success, expected_lint in cases:
            current = root / name
            manifest = crate(current, features, source)
            original = manifest.read_bytes()
            result = subprocess.run(
                [
                    sys.executable,
                    str(WRAPPER),
                    "--package",
                    "semver-policy-fixture",
                    "--policy",
                    str(policy),
                    "--baseline-root",
                    str(baseline),
                ],
                cwd=current,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
            )
            if (result.returncode == 0) != expected_success or (
                expected_lint and expected_lint not in result.stdout
            ):
                print(result.stdout)
                raise RuntimeError(
                    f"{name}: unexpected semver result {result.returncode}"
                )
            if manifest.read_bytes() != original:
                raise RuntimeError(f"{name}: the wrapper did not restore the manifest")
            print(f"PASS: {name}", flush=True)


if __name__ == "__main__":
    main()
