#!/usr/bin/env python3
"""Regression tests for the named feature removal policy."""

import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_semver


# cargo-semver-checks 0.50.0 report for the accepted removal in #458.
REPORT = """    Checking zakura-primitives v1.2.0 -> v1.3.0-alpha.1 (minor change)
     Checked [   0.168s] 196 checks: 195 pass, 1 fail, 0 warn, 58 skip

--- failure feature_missing: package feature removed or renamed ---

Description:
A feature has been removed from this package's Cargo.toml. This will break downstream crates which enable that feature.
        ref: https://doc.rust-lang.org/cargo/reference/semver.html#cargo-feature-remove
       impl: https://github.com/obi1kenobi/cargo-semver-checks/tree/v0.50.0/src/lints/feature_missing.ron

Failed in:

  feature zip-233 in the package's Cargo.toml
     Summary semver requires new major version: 1 major and 0 minor checks failed
    Finished [  46.700s] zakura-primitives
"""
ALLOWLIST = {"zakura-primitives": {"zip-233": "Accepted unused feature removal."}}


class SemverPolicyTest(unittest.TestCase):
    def accepted(self, output=REPORT, features=None, package="zakura-primitives"):
        if features is None:
            features = ALLOWLIST["zakura-primitives"]
        return check_semver.accepted_removals(package, output, features)

    def test_accepts_named_removal_with_minor_bump(self):
        self.assertEqual(self.accepted(), ["zip-233"])
        self.assertEqual(
            self.accepted(REPORT.replace("1.3.0-alpha.1", "1.3.0")), ["zip-233"]
        )

    def test_requires_every_removal_to_be_allowed(self):
        output = REPORT.replace(
            "     Summary",
            "  feature multicore in the package's Cargo.toml\n     Summary",
        )
        self.assertEqual(self.accepted(output), [])
        self.assertEqual(
            self.accepted(output, {"zip-233": "Accepted", "multicore": "Accepted"}),
            ["zip-233", "multicore"],
        )

    def test_requires_exact_package_and_feature_names(self):
        self.assertEqual(self.accepted(features={"zip-23": "Typo"}), [])
        self.assertEqual(self.accepted(features={}), [])
        self.assertEqual(self.accepted(package="zakura-orchard"), [])

    def test_patch_and_unchanged_versions_do_not_get_exception(self):
        for bump in ["patch", "no"]:
            with self.subTest(bump=bump):
                self.assertEqual(
                    self.accepted(REPORT.replace("minor change", f"{bump} change")), []
                )

    def test_other_failures_are_not_hidden(self):
        with_other = (
            REPORT.replace("1 fail", "2 fail")
            .replace(
                "     Summary",
                "--- failure function_missing: function removed ---\n"
                "Failed in:\n  function example\n     Summary",
            )
            .replace("1 major and", "2 major and")
        )
        self.assertEqual(self.accepted(with_other), [])
        self.assertEqual(
            self.accepted(REPORT.replace("feature_missing", "function_missing")), []
        )

    def test_rejects_incomplete_or_unrecognized_reports(self):
        variants = [
            REPORT.replace("1 fail", "2 fail"),
            REPORT.replace("1 major and", "2 major and"),
            REPORT.replace("0 minor checks", "1 minor checks"),
            REPORT.replace("Failed in:", "Findings:"),
            REPORT.replace("  feature zip-233 in the package's Cargo.toml\n", ""),
            REPORT.replace("    Finished [  46.700s] zakura-primitives\n", ""),
            REPORT.replace("  feature zip-233", "  unexpected feature zip-233"),
            REPORT.replace("     Summary", "  field example was removed\n     Summary"),
            REPORT + "error: could not complete the check\n",
            REPORT + REPORT,
        ]
        for output in variants:
            with self.subTest(output=output):
                self.assertEqual(self.accepted(output), [])

    def test_accepts_summary_before_findings_due_to_buffering(self):
        summary = "     Summary semver requires new major version: 1 major and 0 minor checks failed\n"
        output = REPORT.replace(summary, "").replace(
            "  feature zip-233", summary + "  feature zip-233"
        )
        self.assertEqual(self.accepted(output), ["zip-233"])

    def test_old_entries_are_harmless_after_baseline_advances(self):
        result = subprocess.CompletedProcess([], 0, "All checks passed.\n")
        with patch("check_semver.subprocess.run", return_value=result):
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(
                    check_semver.check_package(
                        "zakura-primitives", ALLOWLIST, Path.cwd()
                    ),
                    0,
                )

    def test_wrapper_preserves_errors_and_only_accepts_semver_exit_code(self):
        for code, expected in [(0, 0), (100, 0), (101, 101), (1, 1)]:
            result = subprocess.CompletedProcess([], code, REPORT)
            with self.subTest(code=code):
                with patch("check_semver.subprocess.run", return_value=result) as run:
                    with contextlib.redirect_stdout(io.StringIO()) as output:
                        status = check_semver.check_package(
                            "zakura-primitives", ALLOWLIST, Path.cwd()
                        )
                    self.assertEqual(status, expected)
                    self.assertIn(REPORT, output.getvalue())
                    self.assertEqual(
                        run.call_args.args[0],
                        [
                            "cargo",
                            "semver-checks",
                            "--package",
                            "zakura-primitives",
                            "--default-features",
                            "--color",
                            "never",
                        ],
                    )

    def test_unlisted_package_and_feature_fail_through_wrapper(self):
        for package, allowlist in [
            ("zakura-primitives", {}),
            ("zakura-orchard", ALLOWLIST),
        ]:
            result = subprocess.CompletedProcess([], 100, REPORT)
            with self.subTest(package=package):
                with patch("check_semver.subprocess.run", return_value=result):
                    with (
                        contextlib.redirect_stdout(io.StringIO()),
                        contextlib.redirect_stderr(io.StringIO()),
                    ):
                        self.assertEqual(
                            check_semver.check_package(package, allowlist, Path.cwd()),
                            100,
                        )

    def test_allowlist_validation(self):
        invalid = [
            "[]",
            '{"crate": []}',
            '{"crate": {}}',
            '{"crate": {"feature": ""}}',
            '{"crate": {"feature": 1}}',
            '{"crate": {"feature": "first", "feature": "second"}}',
            '{"crate": {"feature": "first"}, "crate": {"another": "second"}}',
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "allowlist.json"
            path.write_text(json.dumps(ALLOWLIST))
            self.assertEqual(check_semver.load_allowlist(path), ALLOWLIST)
            for contents in invalid:
                with self.subTest(contents=contents):
                    path.write_text(contents)
                    with self.assertRaises(ValueError):
                        check_semver.load_allowlist(path)

    def test_repository_allowlist_is_valid(self):
        root = Path(__file__).resolve().parents[2]
        allowlist = check_semver.load_allowlist(root / check_semver.ALLOWLIST)
        self.assertIn("zip-233", allowlist["zakura-primitives"])


if __name__ == "__main__":
    unittest.main()
