#!/usr/bin/env python3
"""Build pinned Charon with checked trait-bound and nested-constant fixes."""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
PIN = json.loads((HERE / "provenance.json").read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_manifest(directory):
    """Bind the extraction binaries to a recorded build of the pinned recipe."""
    manifest = json.loads((directory / "manifest.json").read_text())
    expected = PIN["charon_native"]
    if manifest["pin"] != expected or manifest["rust_toolchain"] != PIN["rust_toolchain"]:
        raise RuntimeError("Native Charon build has different source or compiler pins")
    for name, expected_hash in expected["patches"].items():
        if digest(HERE / name) != expected_hash:
            raise RuntimeError("Native Charon patch differs from the pin: " + name)
    tree = manifest["source_hashes"]
    tree_hash = hashlib.sha256(json.dumps(tree, sort_keys=True).encode()).hexdigest()
    if tree_hash != expected["source_tree_sha256"]:
        raise RuntimeError("Native Charon source manifest differs from the patched archive")
    for relative, value in tree.items():
        path = directory / "source" / relative
        if digest(path) != value:
            raise RuntimeError("Native Charon source changed: " + relative)
    for relative, target in expected["source_links"].items():
        path = directory / "source" / relative
        if not path.is_symlink() or os.readlink(path) != target:
            raise RuntimeError("Native Charon source link changed: " + relative)
    for relative, value in manifest["tool_hashes"].items():
        if relative not in ["build/release/charon", "build/release/charon-driver"]:
            raise RuntimeError("Unexpected native Charon binary: " + relative)
        if digest(directory / relative) != value:
            raise RuntimeError("Native Charon binary differs from its recorded build")
    if set(manifest["tool_hashes"]) != {"build/release/charon", "build/release/charon-driver"}:
        raise RuntimeError("Incomplete native Charon tool manifest")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True, help="Pinned Charon source tar.gz")
    parser.add_argument("--output", type=Path, required=True, help="New directory for source and binaries")
    parser.add_argument("--offline", action="store_true")
    args = parser.parse_args()
    archive = args.archive.resolve()
    output = args.output.resolve()
    expected = PIN["charon_native"]
    if digest(archive) != expected["archive_sha256"]:
        raise RuntimeError("Charon source archive differs from the pin")
    for name, expected_hash in expected["patches"].items():
        if digest(HERE / name) != expected_hash:
            raise RuntimeError("Native Charon patch differs from the pin: " + name)
    output.mkdir(parents=True, exist_ok=False)
    source = output / "source"
    source.mkdir()
    original = {}
    links = {}
    prefix = "charon-" + PIN["charon_revision"]
    with tarfile.open(archive) as stream:
        for member in stream.getmembers():
            parts = PurePosixPath(member.name).parts
            if not parts or parts[0] != prefix or ".." in parts or member.name.startswith("/"):
                raise RuntimeError("Unexpected source archive path: " + member.name)
            relative = PurePosixPath(*parts[1:])
            path = source / relative
            if member.isdir():
                path.mkdir(parents=True, exist_ok=True)
            elif member.isfile():
                path.parent.mkdir(parents=True, exist_ok=True)
                contents = stream.extractfile(member).read()
                path.write_bytes(contents)
                path.chmod(member.mode & 0o777)
                original[str(relative)] = hashlib.sha256(contents).hexdigest()
            elif member.issym():
                target = (path.parent / member.linkname).resolve()
                if not target.is_relative_to(source.resolve()):
                    raise RuntimeError("Source link escapes the archive: " + member.name)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.symlink_to(member.linkname)
                links[str(relative)] = member.linkname
            else:
                raise RuntimeError("Unexpected source archive member: " + member.name)
    if links != expected["source_links"]:
        raise RuntimeError("Unexpected Charon source links")
    for name in expected["patches"]:
        subprocess.run(["patch", "--batch", "--forward", "-p1", "-i", str(HERE / name)],
                       cwd=source, check=True)
    tree = {relative: digest(source / relative) for relative in original}
    for relative, expected_hash in expected["patched_sources"].items():
        if tree[relative] != expected_hash:
            raise RuntimeError("Native Charon patch produced a different source: " + relative)
    if {relative for relative in tree if tree[relative] != original[relative]} != set(expected["patched_sources"]):
        raise RuntimeError("Patches changed unexpected Charon sources")
    tree_hash = hashlib.sha256(json.dumps(tree, sort_keys=True).encode()).hexdigest()
    if tree_hash != expected["source_tree_sha256"]:
        raise RuntimeError("Patched Charon source tree differs from the pin")
    toolchain = "+" + PIN["rust_toolchain"]
    sysroot = subprocess.check_output(["rustc", toolchain, "--print", "sysroot"], text=True).strip()
    rustc_version = subprocess.check_output(["rustc", toolchain, "--version", "--verbose"], text=True).strip()
    environment = os.environ.copy()
    environment["CARGO_TARGET_DIR"] = str(output / "build")
    environment["CHARON_GIT_COMMIT"] = expected["revision_label"]
    environment["RUST_MIN_STACK"] = "67108864"
    offline = ["--offline"] if args.offline else []
    commands = [
        ["cargo", toolchain, "build", "--release", "--locked", *offline, "--bin", "charon"],
        ["cargo", toolchain, "rustc", "--release", "--locked", *offline, "--bin", "charon-driver",
         "--", "-L", "native=" + str(Path(sysroot) / "lib")],
    ]
    for number, command in enumerate(commands):
        log = output / f"build-{number}.log"
        with log.open("w") as target:
            subprocess.run(command, cwd=source / "charon", env=environment, stdout=target,
                           stderr=subprocess.STDOUT, check=True)
        print("Built", command[command.index("--bin") + 1], flush=True)
    tools = {relative: digest(output / relative) for relative in
             ["build/release/charon", "build/release/charon-driver"]}
    manifest = {"pin": expected, "source_hashes": tree, "tool_hashes": tools,
                "rust_toolchain": PIN["rust_toolchain"], "rustc_version": rustc_version,
                "commands": commands}
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    verify_manifest(output)
    print("Verified pinned source, two-file patch, and both built binaries:", output, flush=True)


if __name__ == "__main__":
    main()
