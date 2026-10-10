#!/usr/bin/env python3
"""Export compatibility bytes using the pinned Pasta and Poseidon crates."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import shutil
import tempfile

REVISION = "80d39d9b1c41ce6c21c87f53c42deb317ce06e84"
ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    output = args.output.resolve()
    with tempfile.TemporaryDirectory(prefix="orchard-compatibility-") as work:
        work = Path(work)
        archive = work / "source.tar"
        subprocess.run(["git", "archive", REVISION, "-o", str(archive)], cwd=ROOT, check=True)
        source = work / "source"
        source.mkdir()
        subprocess.run(["tar", "-xf", str(archive), "-C", str(source)], check=True)
        exporter = work / "exporter"
        (exporter / "src").mkdir(parents=True)
        (exporter / "src/main.rs").write_bytes(Path(__file__).with_name("export.rs").read_bytes())
        dependencies = {
            "pasta_curves": ("zakura-pasta-curves", "pasta_curves", '["glv"]'),
            "halo2_poseidon": ("zakura-halo2-poseidon", "halo2_poseidon", '[]'),
        }
        manifest = '[package]\nname = "orchard-compatibility-export"\nversion = "0.0.0"\nedition = "2024"\n[workspace]\n[dependencies]\nff = "0.14"\ngroup = "0.14"\nrand = "0.10"\nrand_chacha = "0.10"\n'
        for alias, (package, directory, features) in dependencies.items():
            manifest += f'{alias} = {{ package = "{package}", path = "{source}/crates/{directory}", features = {features} }}\n'
        (exporter / "Cargo.toml").write_text(manifest)
        shutil.copy2(source / "Cargo.lock", exporter / "Cargo.lock")
        subprocess.run(["cargo", "run", "--release", "--offline", "--manifest-path", str(exporter / "Cargo.toml"), "--", str(output)], cwd=ROOT, check=True)
    files = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(output.glob("*.bin"))}
    (output / "manifest.json").write_text(json.dumps({"revision": REVISION, "rng": "ChaCha20Rng; seed [42; 32]", "files": files}, indent=2) + "\n")


if __name__ == "__main__":
    main()
