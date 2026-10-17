#!/usr/bin/env python3
"""Compile the supported backend matrix and run the proof roles in isolated builds.

Proofs are exchanged between a prover-only producer and a verifier-only consumer, and
the immutable pre-migration fixtures are verified in a verifier-only build.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile
from itertools import permutations

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--interop-only", action="store_true")
args = parser.parse_args()

def run(*arguments, **kwargs):
    return subprocess.run(arguments, check=True, **kwargs)

def cargo(operation, backend, capabilities, *extra, package="zakura-orchard", **kwargs):
    features = ",".join(filter(None, [f"backend-{backend}", capabilities]))
    return run("cargo", operation, "--locked", "--offline", "-p", package,
               "--no-default-features", "--features", features, *extra, **kwargs)

metadata = json.loads(subprocess.check_output([
    "cargo", "metadata", "--locked", "--no-deps", "--format-version", "1"
], text=True))
features = next(package["features"] for package in metadata["packages"]
                if package["name"] == "zakura-orchard")
backends = sorted(feature.removeprefix("backend-") for feature in features
                  if feature.startswith("backend-"))
if not backends:
    raise SystemExit("no Orchard backend features found")

if not args.interop_only:
    for backend in backends:
        for capabilities in ["", "std", "prover", "verifier", "circuit", "circuit,multicore,zip32-addresses,test-dependencies,weighted-merkle"]:
            cargo("check", backend, capabilities)
        cargo("check", backend, "circuit,multicore,zip32-addresses,test-dependencies", "--all-targets")
        # Default-shaped features without test-dependencies: catches targets
        # that require test-only APIs without declaring the feature.
        cargo("check", backend, "circuit,multicore,zip32-addresses,std", "--all-targets")
        cargo("check", backend, "std,circuits,pczt,multicore", package="zakura-primitives")
        cargo("check", backend, "orchard,sapling,std,zip32-addresses", package="zakura-keys")
        cargo("check", backend, "multicore", package="zakura-proofs")
    invalid = [("", "select an Orchard backend:")]
    if len(backends) > 1:
        invalid.append((",".join(f"backend-{backend}" for backend in backends),
                        "select exactly one Orchard backend"))
    for features, expected in invalid:
        result = subprocess.run(["cargo", "check", "--locked", "--offline", "-p", "zakura-orchard", "--no-default-features", "--features", features, "--message-format=json"], capture_output=True, text=True)
        messages = [json.loads(line) for line in result.stdout.splitlines()]
        errors = [message["message"]["message"] for message in messages
                  if message.get("reason") == "compiler-message"
                  and message["message"]["level"] == "error"]
        # Require the actionable guard even when rustc also reports unresolved
        # backend-dependent items in an invalid configuration.
        assert result.returncode and any(error.startswith(expected) for error in errors), f"missing backend selection diagnostic: {errors}\n{result.stderr}"

def test(backend, capabilities, selection, *extra, **kwargs):
    """Run one lib test selection and require that it ran: a filter matching nothing passes vacuously."""
    result = cargo("test", backend, capabilities, "--release", "--lib", selection, "--", *extra,
                   stdout=subprocess.PIPE, text=True, **kwargs)
    print(result.stdout, flush=True)
    if "test result: ok." not in result.stdout or "running 0 tests" in result.stdout:
        raise SystemExit(f"test selection did not run as expected: {selection}")

# Each proof exchange runs in separately selected producer and consumer builds, and each
# build links only the proof role it exercises.
with tempfile.TemporaryDirectory(prefix="orchard-interop-") as temporary:
    for producer, consumer in (list(permutations(backends, 2)) if len(backends) > 1
                               else [(backends[0], backends[0])]):
        directory = Path(temporary) / producer
        env = dict(os.environ, ORCHARD_INTEROP_DIR=str(directory))
        for backend, role, name in [(producer, "prover", "export_backend_proofs"),
                                    (consumer, "verifier", "verify_backend_proofs")]:
            test(backend, f"{role},multicore,zip32-addresses,test-dependencies",
                 f"circuit::interop::{name}", "--ignored", "--exact", env=env)

# The immutable pre-migration fixtures must verify in a build that links only the verifier.
for backend in backends:
    test(backend, "verifier", "circuit::compatibility::")
