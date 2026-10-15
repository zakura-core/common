#!/usr/bin/env python3
"""Verify unpublished versions against registry dependencies, then upload with a matching receipt."""

import argparse
import graphlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
REPOSITORY = "zakura-core/common"


class ReleaseError(Exception):
    pass


def git(root, *args):
    return subprocess.check_output(["git", *args], cwd=root, text=True).strip()


def check_checkout(root, head):
    if git(root, "rev-parse", "HEAD") != head:
        raise ReleaseError("The checkout changed; use the original release commit.")
    if git(root, "status", "--porcelain", "--untracked-files=normal"):
        raise ReleaseError("Use a clean checkout with all release changes committed.")


def ordered_packages(metadata, root):
    """Include every publishable member and all local edges, even optional/dev edges."""
    members = {p["id"]: p for p in metadata["packages"]
               if p["id"] in metadata["workspace_members"]}
    selected = {p["name"]: p for p in members.values()
                if p["publish"] is None or "crates-io" in p["publish"]}
    paths = {Path(p["manifest_path"]).resolve().parent: p for p in members.values()}
    graph = {}
    for name, package in sorted(selected.items()):
        dependencies = set()
        for dep in package["dependencies"]:
            if not dep.get("path"):
                continue
            local = paths.get(Path(dep["path"]).resolve())
            if local is None or local["name"] not in selected:
                raise ReleaseError(f"{name} depends on a local crate excluded from crates.io publication: {dep['name']}")
            if dep["req"] == "*":
                raise ReleaseError(f"{name} needs a registry version for {dep['name']}.")
            dependencies.add(local["name"])
        graph[name] = sorted(dependencies)
    try:
        order = list(graphlib.TopologicalSorter(graph).static_order())
    except graphlib.CycleError as error:
        raise ReleaseError(f"Publication dependency cycle: {error}") from error
    if not order:
        raise ReleaseError("No workspace crates allow crates.io publication.")
    return [{"name": name, "version": selected[name]["version"],
             "manifest": Path(selected[name]["manifest_path"]).resolve().relative_to(root.resolve()).as_posix(),
             "dependencies": graph[name]} for name in order]


def release_packages(root):
    metadata = json.loads(subprocess.check_output(
        ["cargo", "metadata", "--locked", "--no-deps", "--format-version", "1"],
        cwd=root, text=True))
    return ordered_packages(metadata, root)


def request_json(url, absent_ok=False):
    request = urllib.request.Request(url, headers={
        "User-Agent": "common-release (https://github.com/zakura-core/common)"})
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            return json.load(response)
    except urllib.error.HTTPError as error:
        if error.code == 404 and absent_ok:
            return None
        # These requests never authenticate. Preserve the entire registry error.
        body = error.read().decode("utf-8", errors="replace")
        raise ReleaseError(f"Registry HTTP {error.code} at {url}: {body}") from error
    except (urllib.error.URLError, TimeoutError, ValueError) as error:
        raise ReleaseError(f"Registry request failed at {url}: {error}") from error


def registry_record(name, version):
    data = request_json(f"https://crates.io/api/v1/crates/{name}/{version}", absent_ok=True)
    if data is None:
        return None
    record = data.get("version") if isinstance(data, dict) else None
    if not isinstance(record, dict) or type(record.get("yanked")) is not bool or record.get("num") != version:
        raise ReleaseError(f"Invalid registry response for {name} {version}: {data}")
    if record["yanked"]:
        raise ReleaseError(f"{name} {version} is yanked; prepare a new version.")
    return record


def checked_registry_status(package, expected=None):
    """Read availability, rejecting a change from the dependency source we verified."""
    record = registry_record(package["name"], package["version"])
    status = "available" if record is not None else "absent"
    if expected is not None and status != expected:
        raise ReleaseError(f"Registry availability changed after verification for {package['name']} {package['version']}; rerun verification before publishing.")
    return status


def index_available(name, version):
    lower = name.lower()
    if len(lower) == 1:
        path = f"1/{lower}"
    elif len(lower) == 2:
        path = f"2/{lower}"
    elif len(lower) == 3:
        path = f"3/{lower[0]}/{lower}"
    else:
        path = f"{lower[:2]}/{lower[2:4]}/{lower}"
    request = urllib.request.Request(f"https://index.crates.io/{path}", headers={
        "User-Agent": "common-release", "Cache-Control": "no-cache"})
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            records = [json.loads(line) for line in response if line.strip()]
    except urllib.error.HTTPError as error:
        if error.code == 404:
            return False
        raise ReleaseError(f"Registry index HTTP {error.code}: {error.read().decode('utf-8', errors='replace')}") from error
    except (urllib.error.URLError, TimeoutError, ValueError) as error:
        raise ReleaseError(f"Registry index failed: {error}") from error
    for record in records:
        if record.get("vers") == version:
            if type(record.get("yanked")) is not bool or record["yanked"]:
                raise ReleaseError(f"Index rejects {name} {version}: {record}")
            return True
    return False


def require_attribution(record, run_id, head):
    attestation = record.get("trustpub_data") or {}
    actual = (attestation.get("provider"), attestation.get("repository"),
              str(attestation.get("run_id")), attestation.get("sha"))
    if actual != ("github", REPOSITORY, str(run_id), head):
        raise ReleaseError(f"Publication attribution does not match this workflow run and commit: {attestation}")


def wait_available(name, version, run_id=None, head=None, timeout=300):
    deadline = time.monotonic() + timeout
    while True:
        record = registry_record(name, version)
        if record is not None and index_available(name, version):
            if run_id is not None:
                require_attribution(record, run_id, head)
            return
        if time.monotonic() >= deadline:
            raise ReleaseError(f"Timed out waiting for {name} {version}; inspect crates.io before resuming.")
        time.sleep(5)


def save_receipt(path, receipt):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(receipt, indent=2) + "\n")
    temporary.replace(path)


def read_verified(path, root, head, packages):
    check_checkout(root, head)
    try:
        receipt = json.loads(Path(path).read_text())
        actual = [{key: p[key] for key in ("name", "version", "manifest", "dependencies")}
                  for p in receipt["packages"]]
        valid = (receipt["schema_version"] == 1 and receipt["repository"] == REPOSITORY
                 and receipt["commit"] == head and receipt["tree"] == git(root, "rev-parse", "HEAD^{tree}")
                 and receipt["verification_passed"] is True and actual == packages
                 and all(p["registry_status"] in ("available", "absent")
                         and p["result"] == "verified" for p in receipt["packages"]))
    except (OSError, ValueError, KeyError, TypeError):
        valid = False
    if not valid:
        raise ReleaseError("Verification receipt must match this clean commit and ordered package versions and dependencies.")
    return receipt


def run_release(root, mode, output, verified=None, run_id=None):
    head = git(root, "rev-parse", "HEAD")
    check_checkout(root, head)
    packages = release_packages(root)
    output = Path(output).resolve()
    if output.is_relative_to(root.resolve()):
        raise ReleaseError("Save receipts outside the checkout.")
    if verified is not None and output == Path(verified).resolve():
        raise ReleaseError("Do not overwrite the verification receipt with progress.")
    if mode in ("validate", "publish"):
        if verified is None:
            raise ReleaseError("A successful verification receipt is required.")
        verification = read_verified(verified, root, head, packages)
        if mode == "validate":
            print("Verified receipt matches the clean checkout.")
            return
        if not run_id:
            raise ReleaseError("Publication requires the GitHub run ID for attribution.")
        verified_statuses = {p["name"]: p["registry_status"] for p in verification["packages"]}
    receipt = {"schema_version": 1, "repository": REPOSITORY, "commit": head,
               "tree": git(root, "rev-parse", "HEAD^{tree}"),
               "verification_passed": mode == "publish", "run_id": run_id,
               "packages": [dict(p, registry_status="unknown", result="remaining") for p in packages]}
    save_receipt(output, receipt)
    current = None
    try:
        # Check all versions for yanks/errors before any irreversible upload.
        for current in receipt["packages"]:
            expected = verified_statuses[current["name"]] if mode == "publish" else None
            current["registry_status"] = checked_registry_status(current, expected)
            save_receipt(output, receipt)
        with tempfile.TemporaryDirectory(prefix="common-crate-release-") as target:
            if mode == "verify":
                current = None
                command = ["cargo", "publish", "--registry", "crates-io", "--locked",
                           "--dry-run", "--keep-going", "--target-dir", target]
                unpublished = [p for p in receipt["packages"] if p["registry_status"] == "absent"]
                for package in unpublished:
                    command.extend(["--package", package["name"]])
                check_checkout(root, head)
                # Overlay only versions we will upload. Already published dependencies
                # must resolve from crates.io, rather than potentially changed local code.
                # Without a selection Cargo would verify the workspace default members.
                if unpublished:
                    subprocess.run(command, cwd=root, check=True)
                check_checkout(root, head)
                receipt["verification_passed"] = True
                for current in receipt["packages"]:
                    current["result"] = "verified"
                save_receipt(output, receipt)
                return
            for current in receipt["packages"]:
                check_checkout(root, head)
                name, version = current["name"], current["version"]
                # A version appearing since verification changes Cargo's dependency
                # source. Reruns verify again before skipping previous uploads.
                if checked_registry_status(current, current["registry_status"]) == "available":
                    current["registry_status"] = "available"
                    current["result"] = "previously_available"
                    save_receipt(output, receipt)
                    wait_available(name, version)
                    continue
                current["result"] = "upload_started"
                save_receipt(output, receipt)
                # Cargo stderr remains intact in Actions, including registry error bodies.
                subprocess.run(["cargo", "publish", "--manifest-path", str(root / current["manifest"]),
                                "--registry", "crates-io", "--locked", "--no-verify",
                                "--target-dir", target], cwd=root, check=True)
                current["result"] = "uploaded_unconfirmed"
                save_receipt(output, receipt)
                wait_available(name, version, run_id, head)
                check_checkout(root, head)
                current["registry_status"] = "available"
                current["result"] = "published"
                save_receipt(output, receipt)
    except (ReleaseError, subprocess.CalledProcessError, OSError) as error:
        receipt["error"] = str(error)
        if current is not None:
            current["error"] = str(error)
        save_receipt(output, receipt)
        raise


def summarize(receipt):
    rows = ["## Crates.io release", "", f"Commit: `{receipt['commit']}`", "",
            "Verification: " + ("passed" if receipt["verification_passed"] else "not completed"), "",
            "| Crate | Version | Registry | Result |", "| --- | --- | --- | --- |"]
    for package in receipt["packages"]:
        rows.append(f"| `{package['name']}` | `{package['version']}` | {package['registry_status']} | {package['result']} |")
    if "error" in receipt:
        rows.extend(["", "Release stopped. The receipt and failed step retain the full error."])
    return "\n".join(rows) + "\n"


def confirm(receipt, run_id, head):
    if receipt["repository"] != REPOSITORY or receipt["commit"] != head or str(receipt["run_id"]) != str(run_id):
        raise ReleaseError("Publication receipt must match this repository, run and commit.")
    errors = []
    for p in receipt["packages"]:
        try:
            if p["result"] == "previously_available":
                wait_available(p["name"], p["version"])
            elif p["result"] in ("published", "uploaded_unconfirmed", "upload_started"):
                wait_available(p["name"], p["version"], run_id, head)
            else:
                raise ReleaseError(f"Publication not completed: {p['result']}")
        except ReleaseError as error:
            errors.append(f"{p['name']} {p['version']}: {error}")
    if errors:
        raise ReleaseError("Publication confirmation failed:\n" + "\n".join(errors))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("verify", "validate", "publish", "summary", "confirm"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--run-id")
    parser.add_argument("--commit")
    args = parser.parse_args()
    try:
        if args.mode in ("summary", "confirm"):
            if args.receipt is None:
                parser.error("--receipt is required")
            receipt = json.loads(args.receipt.read_text())
            if args.mode == "summary":
                print(summarize(receipt), end="")
            else:
                if not args.run_id or not args.commit:
                    parser.error("--run-id and --commit are required")
                confirm(receipt, args.run_id, args.commit)
        else:
            if args.output is None:
                parser.error("--output is required (outside the checkout)")
            run_release(ROOT, args.mode, args.output, args.receipt, args.run_id)
    except (ReleaseError, subprocess.CalledProcessError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"Release stopped: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
