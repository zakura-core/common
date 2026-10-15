#!/usr/bin/env python3
"""Require Common's CI and its aggregate job on the exact main push commit."""

import argparse
import json
import re
import subprocess
import sys

REPOSITORY = "zakura-core/common"


def gh_pages(endpoint):
    return json.loads(subprocess.check_output(
        ["gh", "api", "--paginate", "--slurp", endpoint], text=True))


def require_ci(repository, commit):
    if repository != REPOSITORY or not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("CI requires zakura-core/common and a full commit SHA.")
    pages = gh_pages(f"repos/{repository}/actions/workflows/ci.yml/runs"
                     f"?head_sha={commit}&branch=main&event=push&per_page=100")
    runs = [run for page in pages for run in page["workflow_runs"]
            if run["head_sha"] == commit and run["head_branch"] == "main"
            and run["event"] == "push" and run["name"] == "CI"]
    if not runs:
        raise ValueError(f"CI has no main push run for {commit}.")
    latest = max(runs, key=lambda run: (run["run_number"], run["run_attempt"]))
    if latest["status"] != "completed" or latest["conclusion"] != "success":
        raise ValueError("CI must finish successfully for this commit: " + latest["html_url"])
    pages = gh_pages(f"repos/{repository}/actions/runs/{latest['id']}/attempts/{latest['run_attempt']}/jobs?per_page=100")
    gates = [job for page in pages for job in page["jobs"] if job["name"] == "test success"]
    if len(gates) != 1 or gates[0]["status"] != "completed" or gates[0]["conclusion"] != "success":
        raise ValueError("CI's test success job must pass in the successful run attempt.")
    print("Required CI passed: " + latest["html_url"])



def require_environment(repository):
    if repository != REPOSITORY:
        raise ValueError("Release environment requires zakura-core/common.")
    endpoint = f"repos/{repository}/environments/crates-io"
    environment = gh_pages(endpoint)[0]
    rules = environment["protection_rules"]
    reviewers = [r for r in rules if r["type"] == "required_reviewers"]
    policy = environment.get("deployment_branch_policy") or {}
    branches = [branch for page in gh_pages(endpoint + "/deployment-branch-policies?per_page=100")
                for branch in page["branch_policies"]]
    valid = (environment.get("can_admins_bypass") is False
             and len(reviewers) == 1 and reviewers[0].get("prevent_self_review") is False
             and [(r["type"], r["reviewer"]["login"]) for r in reviewers[0]["reviewers"]] == [("User", "ebfull")]
             and policy == {"protected_branches": False, "custom_branch_policies": True}
             and [(b["name"], b["type"]) for b in branches] == [("main", "branch")])
    if not valid:
        raise ValueError("Configure crates-io for main only, ebfull approval, self approval allowed, and no admin bypass.")
    print("Required release environment protections confirmed.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--check-environment", action="store_true")
    args = parser.parse_args()
    try:
        if args.check_environment:
            require_environment(args.repository)
        require_ci(args.repository, args.commit)
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        print(f"Release CI stopped: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
