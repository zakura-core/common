#!/usr/bin/env python3
"""Check that a validator consumer resolves without FF1, including test helpers."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parent.parent
DEPENDENCIES = {
    "orchard": ("zakura-orchard", "orchard", ["circuit", "multicore", "std", "test-dependencies"]),
    "sapling": ("zakura-sapling-crypto", "sapling-crypto", ["circuit", "multicore", "test-dependencies"]),
    "keys": ("zakura-keys", "zcash_keys", ["std", "orchard", "sapling", "test-dependencies"]),
    "primitives": ("zakura-primitives", "zcash_primitives", ["circuits", "multicore", "std", "test-dependencies"]),
    "proofs": ("zakura-proofs", "zcash_proofs", ["multicore"]),
}


def main():
    with tempfile.TemporaryDirectory(prefix="common-without-fpe-") as directory:
        consumer = Path(directory)
        lines = [
            '[package]',
            'name = "validator-without-fpe"',
            'version = "0.0.0"',
            'edition = "2024"',
            '',
            '[workspace]',
            '',
            '[dependencies]',
        ]
        for alias, (package, crate, features) in DEPENDENCIES.items():
            path = json.dumps(str(ROOT / "crates" / crate))
            lines.append(
                f'{alias} = {{ package = "{package}", path = {path}, '
                f'default-features = false, features = {json.dumps(features)} }}'
            )
        (consumer / "Cargo.toml").write_text("\n".join(lines) + "\n")
        (consumer / "src").mkdir()
        (consumer / "src" / "main.rs").write_text("fn main() {}\n")
        # Share the normal Cargo cache, but never join the Common workspace:
        # its default-enabled wallet features legitimately retain FF1.
        env = dict(os.environ)
        env.setdefault("CARGO_TARGET_DIR", str(ROOT / "target"))
        subprocess.run(
            ["cargo", "generate-lockfile", "--manifest-path", str(consumer / "Cargo.toml")],
            check=True, env=env,
        )
        packages = tomllib.loads((consumer / "Cargo.lock").read_text())["package"]
        forbidden = {"fpe", "cbc"} & {package["name"] for package in packages}
        if forbidden:
            raise SystemExit(f"unexpected validator dependencies: {sorted(forbidden)}")
        subprocess.run(
            ["cargo", "check", "--locked", "--manifest-path", str(consumer / "Cargo.toml")],
            check=True, env=env,
        )
        print("Validator dependencies and test helpers compile without fpe or cbc.")


if __name__ == "__main__":
    main()
