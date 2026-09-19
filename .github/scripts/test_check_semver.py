#!/usr/bin/env python3
"""Regression tests for the named feature removal policy."""

import contextlib
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
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
        try:
            return check_semver.accepted_removals(package, output, features)
        except check_semver.ReportFormatError:
            return []

    def run_check(
        self,
        report=REPORT,
        code=100,
        package="zakura-primitives",
        allowlist=None,
        **options,
    ):
        if allowlist is None:
            allowlist = ALLOWLIST
        results = iter(
            [
                subprocess.CompletedProcess([], 0, "cargo-semver-checks 0.50.0\n"),
                subprocess.CompletedProcess([], code, report),
            ]
        )

        def runner(*_args, **_kwargs):
            result = next(results)
            print(result.stdout, end="")
            return result

        with patch("check_semver.run_command", side_effect=runner) as run:
            with (
                contextlib.redirect_stdout(io.StringIO()) as out,
                contextlib.redirect_stderr(io.StringIO()) as err,
            ):
                status = check_semver.check_package(
                    package, allowlist, Path.cwd(), **options
                )
        return status, out.getvalue(), err.getvalue(), run

    def with_warning(self, report=REPORT):
        return (
            report.replace("195 pass, 1 fail, 0 warn", "194 pass, 1 fail, 1 warn")
            .replace(
                "     Summary",
                "--- warning function_must_use_added: function is now must_use ---\n"
                "Description:\nA configured warning.\n"
                "Failed in:\n  function example\n\n     Summary",
            )
            .replace(
                "    Finished",
                "     Warning produced 1 major and 0 minor level warnings\n    Finished",
            )
        )

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
            REPORT.replace("195 pass, 1 fail", "194 pass, 2 fail")
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

    def test_warnings_do_not_block_an_approved_removal(self):
        report = self.with_warning()
        self.assertEqual(self.accepted(report), ["zip-233"])
        status, output, error, _ = self.run_check(report)
        self.assertEqual(status, 0)
        self.assertIn("--- warning function_must_use_added:", output)
        self.assertEqual(error, "")

    def test_warnings_do_not_hide_unapproved_removals_or_other_failures(self):
        report = self.with_warning(
            REPORT.replace(
                "  feature zip-233 in the package's Cargo.toml",
                "  feature zip-233 in the package's Cargo.toml\n  feature multicore in the package's Cargo.toml",
            )
        )
        self.assertEqual(self.accepted(report), [])
        self.assertEqual(self.run_check(report)[0], 100)
        self.assertEqual(
            self.run_check(
                self.with_warning().replace("feature_missing", "function_missing")
            )[0],
            100,
        )

    def test_malformed_warning_reports_are_not_approved(self):
        report = self.with_warning()
        for malformed in [
            report.replace("1 warn", "0 warn"),
            report.replace("--- warning", "--- unknown"),
            report.replace(
                "1 major and 0 minor level warnings",
                "2 major and 0 minor level warnings",
            ),
            report.replace(
                "Failed in:\n  function example", "Unknown:\n  function example"
            ),
            report + "error: incomplete check\n",
        ]:
            with self.subTest(report=malformed):
                with self.assertRaises(check_semver.ReportFormatError):
                    check_semver.accepted_removals(
                        "zakura-primitives", malformed, ALLOWLIST["zakura-primitives"]
                    )

    def test_rejects_incomplete_or_unrecognized_reports(self):
        variants = [
            REPORT.replace("minor change", "unknown change"),
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
        self.assertEqual(self.run_check("All checks passed.\n", code=0)[0], 0)

    def test_wrapper_preserves_errors_and_only_accepts_semver_exit_code(self):
        for code, expected in [(0, 0), (100, 0), (101, 101), (1, 1)]:
            with self.subTest(code=code):
                status, output, _, run = self.run_check(
                    code=code, default_features=True
                )
                self.assertEqual(status, expected)
                self.assertIn(REPORT, output)
                self.assertIn("cargo-semver-checks 0.50.0", output)
                self.assertEqual(
                    run.call_args.args[0],
                    [
                        "cargo",
                        "semver-checks",
                        "--package",
                        "zakura-primitives",
                        "--color",
                        "never",
                        "--default-features",
                    ],
                )

    def test_release_baseline_and_feature_selection_are_preserved(self):
        status, _, _, run = self.run_check(baseline_version="1.2.0")
        self.assertEqual(status, 0)
        self.assertEqual(
            run.call_args.args[0],
            [
                "cargo",
                "semver-checks",
                "--package",
                "zakura-primitives",
                "--color",
                "never",
                "--baseline-version",
                "1.2.0",
            ],
        )

    def test_format_error_is_distinct_from_unapproved_removal(self):
        status, _, error, _ = self.run_check(REPORT.replace("Failed in:", "Findings:"))
        self.assertEqual(status, 100)
        self.assertIn("report format not recognized", error)
        self.assertNotIn("not covered", error)
        status, _, error, _ = self.run_check(
            REPORT.replace("feature zip-233 ", "feature multicore ")
        )
        self.assertEqual(status, 100)
        self.assertIn("not covered", error)
        self.assertNotIn("report format not recognized", error)

    def test_unlisted_package_and_feature_fail_through_wrapper(self):
        for package, allowlist in [
            ("zakura-primitives", {}),
            ("zakura-orchard", ALLOWLIST),
        ]:
            with self.subTest(package=package):
                self.assertEqual(
                    self.run_check(package=package, allowlist=allowlist)[0], 100
                )

    def test_allowlist_validation(self):
        invalid = [
            "[]",
            '{"crate": []}',
            '{"crate": {"feature": ""}}',
            '{"crate": {"feature": 1}}',
            '{"crate": {"feature": "first", "feature": "second"}}',
            '{"crate": {"feature": "first"}, "crate": {"another": "second"}}',
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "allowlist.json"
            path.write_text(json.dumps(ALLOWLIST))
            self.assertEqual(check_semver.load_allowlist(path), ALLOWLIST)
            for contents in ["{}", '{"crate": {}}']:
                path.write_text(contents)
                self.assertEqual(
                    check_semver.load_allowlist(path), json.loads(contents)
                )
            for contents in invalid:
                with self.subTest(contents=contents):
                    path.write_text(contents)
                    with self.assertRaises(ValueError):
                        check_semver.load_allowlist(path)

    def test_repository_allowlist_is_valid(self):
        root = Path(__file__).resolve().parents[2]
        check_semver.load_allowlist(root / check_semver.ALLOWLIST)


class CommandRunnerTest(unittest.TestCase):
    def test_streams_before_exit_and_replaces_invalid_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "continue"

            class Output(io.StringIO):
                def write(self, text):
                    result = super().write(text)
                    if "ready" in self.getvalue():
                        marker.touch()
                    return result

            program = """
import pathlib, sys, time
sys.stdout.buffer.write(b'ready\\xff\\n')
sys.stdout.flush()
deadline = time.monotonic() + 3
while not pathlib.Path(sys.argv[1]).exists():
    if time.monotonic() > deadline:
        sys.exit(2)
    time.sleep(0.01)
sys.stdout.write('finished\\n')
"""
            with contextlib.redirect_stdout(Output()) as output:
                result = check_semver.run_command(
                    [sys.executable, "-c", program, str(marker)], directory, timeout=5
                )
            self.assertEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "ready\ufffd\nfinished\n")
            self.assertEqual(output.getvalue(), result.stdout)

    @unittest.skipUnless(os.name == "posix", "process group cleanup on CI and macOS")
    def test_timeout_preserves_partial_output_and_stops_descendants(self):
        with tempfile.TemporaryDirectory() as directory:
            heartbeat = Path(directory) / "heartbeat"
            child = "import pathlib,sys,time\np=pathlib.Path(sys.argv[1])\nwhile True:\n p.write_text(str(time.monotonic_ns()))\n time.sleep(0.01)"
            program = "import subprocess,sys,time\nsubprocess.Popen([sys.executable,'-c',sys.argv[1],sys.argv[2]])\nprint('partial output',flush=True)\ntime.sleep(60)"
            with contextlib.redirect_stdout(io.StringIO()) as output:
                with self.assertRaises(subprocess.TimeoutExpired):
                    check_semver.run_command(
                        [sys.executable, "-c", program, child, str(heartbeat)],
                        directory,
                        timeout=1,
                    )
            self.assertIn("partial output", output.getvalue())
            last_heartbeat = heartbeat.read_text()
            time.sleep(0.1)
            self.assertEqual(heartbeat.read_text(), last_heartbeat)

    @unittest.skipUnless(os.name == "posix", "SIGTERM cleanup on CI and macOS")
    def test_sigterm_cleans_up_the_active_command(self):
        with tempfile.TemporaryDirectory() as directory:
            heartbeat = Path(directory) / "heartbeat"
            child = "import pathlib,sys,time\np=pathlib.Path(sys.argv[1])\nprint('partial output',flush=True)\nwhile True:\n p.write_text(str(time.monotonic_ns()))\n time.sleep(0.01)"
            program = """
import signal, sys
sys.path.insert(0, sys.argv[1])
import check_semver
signal.signal(signal.SIGTERM, check_semver.handle_termination)
check_semver.run_command([sys.executable, '-c', sys.argv[2], sys.argv[3]], '.', timeout=10)
"""
            process = subprocess.Popen(
                [
                    sys.executable,
                    "-B",
                    "-c",
                    program,
                    str(Path(check_semver.__file__).parent),
                    child,
                    str(heartbeat),
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
            )
            try:
                deadline = time.monotonic() + 5
                while not heartbeat.exists() and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue(
                    heartbeat.exists(), "child must start before cancellation"
                )
                process.send_signal(signal.SIGTERM)
                output, _ = process.communicate(timeout=5)
                self.assertEqual(process.returncode, 143)
                self.assertIn("partial output", output)
                last_heartbeat = heartbeat.read_text()
                time.sleep(0.1)
                self.assertEqual(heartbeat.read_text(), last_heartbeat)
            finally:
                if process.poll() is None:
                    process.send_signal(signal.SIGTERM)
                    process.communicate(timeout=5)


if __name__ == "__main__":
    unittest.main()
