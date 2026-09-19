#!/usr/bin/env python3
"""Regression tests for the named feature removal policy."""

import contextlib
import io
from pathlib import Path
import tempfile
import unittest

import check_semver


# cargo-semver-checks 0.50.0 output, with descriptive boilerplate abbreviated.
REPORT = """    Checking zakura-primitives v1.2.0 -> v1.3.0-alpha.1 (minor change)
     Checked [   0.168s] 196 checks: 195 pass, 1 fail, 0 warn, 58 skip
--- failure feature_missing: package feature removed or renamed ---
Description:
A feature has been removed from this package's Cargo.toml.
Failed in:
  feature zip-233 in the package's Cargo.toml
     Summary semver requires new major version: 1 major and 0 minor checks failed
    Finished [  46.700s] zakura-primitives
"""
ALLOWED = {"zip-233": "Approved unused feature removal."}


class SemverPolicyTest(unittest.TestCase):
    def check(self, report=REPORT, status=100, allowed=ALLOWED):
        with (
            contextlib.redirect_stdout(io.StringIO()),
            contextlib.redirect_stderr(io.StringIO()) as errors,
        ):
            result = check_semver.check_result(
                "zakura-primitives", status, report, allowed
            )
        return result, errors.getvalue()

    def test_approvals_and_failures(self):
        extra = REPORT.replace(
            "     Summary",
            "  feature multicore in the package's Cargo.toml\n     Summary",
        )
        cases = [
            (REPORT, ALLOWED, 0),
            (REPORT.replace("1.3.0-alpha.1", "1.3.0"), ALLOWED, 0),
            (REPORT, {}, 100),
            (REPORT, {"zip-23": "Typo"}, 100),
            (extra, ALLOWED, 100),
            (extra, {**ALLOWED, "multicore": "Approved"}, 0),
            (REPORT.replace("zakura-primitives", "another-crate"), ALLOWED, 100),
            (REPORT.replace("minor change", "patch change"), ALLOWED, 100),
            (REPORT.replace("minor change", "no change"), ALLOWED, 100),
            (REPORT.replace("feature_missing", "function_missing"), ALLOWED, 100),
        ]
        for report, allowed, expected in cases:
            with self.subTest(report=report, allowed=allowed):
                self.assertEqual(self.check(report, allowed=allowed)[0], expected)
        for status in [0, 1, 101]:
            self.assertEqual(self.check(status=status)[0], status)

    def test_warnings_and_interleaved_status_lines(self):
        warning = "--- warning function_must_use_added: function is now must_use ---\nFailed in:\n  function example\n"
        report = REPORT.replace(
            "195 pass, 1 fail, 0 warn", "194 pass, 1 fail, 1 warn"
        ).replace("     Summary", warning + "     Summary")
        self.assertEqual(self.check(report)[0], 0)
        self.assertEqual(
            self.check(report.replace("feature zip-233", "feature multicore"))[0], 100
        )
        self.assertEqual(
            self.check(
                report.replace("--- warning", "--- failure")
                .replace("1 fail", "2 fail")
                .replace("1 major and", "2 major and")
            )[0],
            100,
        )
        summary = next(line for line in REPORT.splitlines(True) if "Summary" in line)
        self.assertEqual(
            self.check(
                REPORT.replace(summary, "").replace("  feature", summary + "  feature")
            )[0],
            0,
        )

    def test_unknown_reports_fail_with_distinct_diagnostic(self):
        for report in [
            REPORT.replace("1 fail", "2 fail"),
            REPORT.replace("1 major and", "2 major and"),
            REPORT.replace("Failed in:", "Findings:"),
            REPORT.replace("  feature zip-233 in the package's Cargo.toml\n", ""),
            REPORT.replace("  feature zip-233", "  unexpected feature zip-233"),
            REPORT.replace("     Summary", "  field example removed\n     Summary"),
            REPORT.rsplit("    Finished", 1)[0],
            REPORT + "error: incomplete check\n",
            REPORT + REPORT,
        ]:
            with self.subTest(report=report):
                status, error = self.check(report)
                self.assertEqual(status, 100)
                self.assertIn("report format not recognized", error)
        self.assertIn(
            "not covered", self.check(REPORT.replace("zip-233", "multicore"))[1]
        )

    def test_policy_validation_including_empty_allowlist(self):
        check_semver.load_allowlist(
            Path(__file__).resolve().parents[2] / check_semver.ALLOWLIST
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "policy.json"
            for contents in [
                "{}",
                '{"crate": {}}',
                '{"crate": {"feature": "Approved"}}',
            ]:
                path.write_text(contents)
                check_semver.load_allowlist(path)
            for contents in [
                "[]",
                '{"crate": []}',
                '{"crate": {"feature": ""}}',
                '{"crate": {"feature": 1}}',
            ]:
                with self.subTest(contents=contents), self.assertRaises(ValueError):
                    path.write_text(contents)
                    check_semver.load_allowlist(path)


if __name__ == "__main__":
    unittest.main()
