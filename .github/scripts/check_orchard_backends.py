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
parser.add_argument("--composition-api-only", action="store_true")
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

def check_composition_visibility():
    """Compile external snippets against the exact metadata from each feature build."""
    orchard_id = next(package["id"] for package in metadata["packages"]
                      if package["name"] == "zakura-orchard")
    public = {
        "module": "use orchard::circuit::composition::CommitIvkChip;",
        "viewing witness": "fn witness(f: &orchard::keys::FullViewingKey) { let _ = orchard::circuit::composition::witness::NullifierDerivingKey::from(f); }",
        "signing witness": "fn witness(k: &orchard::keys::SpendAuthorizingKey) { let _ = orchard::circuit::composition::witness::SpendAuthorizingKey::from(k); }",
        "note witness": "use orchard::circuit::composition::witness::NotePsi;",
    }
    private = {
        "payment circuit": "use orchard::circuit::Circuit;",
        "payment configuration": "use orchard::circuit::Config;",
        "payment implementation": "use orchard::circuit::halo2;",
        "constant implementation": "use orchard::constants;",
        "specification implementation": "use orchard::spec;",
        "ordinary viewing accessor": "fn raw(f: &orchard::keys::FullViewingKey) { let _ = f.nk(); }",
        "ordinary address accessor": "fn raw(a: &orchard::Address) { let _ = a.g_d(); }",
        "ordinary note derivation": "fn raw(s: &orchard::note::RandomSeed, r: &orchard::note::Rho) { let _ = s.rcm_v2(r); }",
        "ordinary signing encoding": "fn raw(k: &orchard::keys::SpendAuthorizingKey) { let _ = k.to_bytes(); }",
        "raw spending derivation": "fn raw(k: &orchard::keys::SpendingKey) { let _ = orchard::keys::SpendAuthorizingKey::derive_inner(k); }",
    }
    with tempfile.TemporaryDirectory(prefix="orchard-composition-api-") as temporary:
        source = Path(temporary) / "consumer.rs"
        for selected in [None, "prover", "verifier", "circuit-composition"]:
            command = ["cargo", "check", "--locked", "--offline", "-p", "zakura-orchard", "--lib", "--message-format=json"]
            if selected is not None:
                command.extend(["--no-default-features", "--features", f"backend-halo2,{selected}"])
            build = subprocess.run(command, check=True, stdout=subprocess.PIPE, text=True)
            artifacts = [json.loads(line) for line in build.stdout.splitlines()]
            artifact = next(Path(filename) for item in reversed(artifacts)
                            if item.get("reason") == "compiler-artifact" and item.get("package_id") == orchard_id
                            for filename in item["filenames"] if filename.endswith(".rmeta"))
            snippets = [(name, code, selected == "circuit-composition") for name, code in public.items()]
            snippets.extend((name, code, False) for name, code in private.items())
            if selected == "circuit-composition":
                snippets.append(("raw viewing field", "fn raw(f: &orchard::keys::FullViewingKey) { let _ = orchard::circuit::composition::witness::NullifierDerivingKey::from(f).inner(); }", False))
            for name, code, allowed in snippets:
                source.write_text(code)
                result = subprocess.run([
                    "rustc", "--edition=2024", "--crate-type=lib", "--emit=metadata", "--error-format=json",
                    "--out-dir", temporary, "--extern", f"orchard={artifact}",
                    "-L", f"dependency={artifact.parent}", str(source),
                ], capture_output=True, text=True)
                diagnostics = [json.loads(line) for line in result.stderr.splitlines() if line.startswith("{")]
                errors = [item for item in diagnostics if item.get("level") == "error" and item.get("code")]
                if allowed:
                    assert result.returncode == 0, f"{selected}: {name} must be usable: {result.stderr}"
                else:
                    # A missing dependency, syntax error, or unrelated unresolved type must
                    # not masquerade as proof that this API is private.
                    assert result.returncode != 0 and errors, f"{selected}: {name} unexpectedly compiled"
                    assert all(item["code"]["code"] in {"E0432", "E0433", "E0603", "E0624", "E0599"}
                               for item in errors), f"{selected}: unrelated failure for {name}: {result.stderr}"
                    assert any(any(span.get("is_primary") and Path(span["file_name"]) == source for span in item.get("spans", []))
                               for item in errors), f"{selected}: failure did not point at the consumer: {result.stderr}"
                    assert all(any(word in item["message"] for word in
                                   ("private", "unresolved import `orchard::", "could not find", "cannot find", "no method named"))
                               for item in errors), result.stderr
            print(f"composition visibility passed: {selected or 'default'}", flush=True)

if args.composition_api_only:
    check_composition_visibility()
    raise SystemExit(0)

if not args.interop_only:
    check_composition_visibility()
    for backend in backends:
        for capabilities in ["", "std", "prover", "verifier", "circuit", "circuit,multicore,zip32-addresses,test-dependencies,weighted-merkle"]:
            cargo("check", backend, capabilities)
        cargo("check", backend, "circuit,multicore,zip32-addresses,test-dependencies,sensei-bench", "--all-targets")
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
