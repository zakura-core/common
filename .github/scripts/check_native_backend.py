#!/usr/bin/env python3
"""Reject legacy packages in every supported native consumer dependency closure.

The workspace and lockfile deliberately retain the independently selected legacy
backend. Only the closure selected for each consumer belongs in this assertion.
"""
import subprocess

LEGACY = {"pasta_curves", "pasta-curves", "sinsemilla", "orchard-legacy"}

def check(package, features):
    args = ["cargo", "tree", "--locked", "--offline", "-p", package,
            "--no-default-features", "--edges", "normal,build,dev", "--target", "all",
            "--prefix", "none"]
    if features:
        args += ["--features", features]
    tree = subprocess.check_output(args, text=True)
    forbidden = []
    for line in tree.splitlines():
        name = line.split()[0].removeprefix("zakura-")
        if name in LEGACY or name.startswith(("halo2-", "halo2_")):
            forbidden.append(line)
    if forbidden:
        raise SystemExit(f"{package} [{features}] links legacy packages:\n" + "\n".join(forbidden))
    print(f"isolated: {package} [{features}]", flush=True)

for capabilities in ["", "prover", "verifier", "prover,verifier", "prover,verifier,multicore"]:
    check("zakura-sensei", capabilities)
    check("zakura-orchard", ",".join(filter(None, ["backend-sensei", capabilities])))
check("zakura-orchard", "backend-sensei,circuit,multicore,zip32-addresses,test-dependencies,weighted-merkle,verifier-fingerprint,prover-fingerprint,circuit-fixtures,portable")
for capabilities in ["", "std", "std,circuits,pczt,multicore,test-dependencies"]:
    check("zakura-primitives", ",".join(filter(None, ["backend-sensei", capabilities])))
check("zakura-keys", "backend-sensei,orchard,sapling,std,test-dependencies,zip32-addresses")
for package in ["zakura-reddsa", "zakura-reddsa-frost"]:
    for features in ["", "std", "pallas-sensei", "pallas-sensei,std"]:
        check(package, features)
