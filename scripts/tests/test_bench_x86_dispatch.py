"""Check benchmark reporting and missing-workload failures without timing code."""

import importlib.util
import json
import os
import sys
import tempfile
import time
import unittest
from pathlib import Path


SPEC = importlib.util.spec_from_file_location(
    "bench_x86_dispatch", Path(__file__).resolve().parents[1] / "bench_x86_dispatch.py"
)
benchmark = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(benchmark)


class ReportingTests(unittest.TestCase):
    def test_command_preserves_stdout_and_stderr_in_the_log(self):
        with tempfile.TemporaryDirectory() as temporary:
            log = Path(temporary) / "command.log"
            output = benchmark.command(
                [sys.executable, "-c", "import sys; print('out'); print('err', file=sys.stderr)"],
                environment=os.environ.copy(), log=log, deadline=time.monotonic() + 10,
            )
            self.assertIn("out", output)
            self.assertIn("err", output)
            self.assertEqual(output, log.read_text())

    def test_failed_command_retains_its_output_and_stops_the_run(self):
        with tempfile.TemporaryDirectory() as temporary:
            log = Path(temporary) / "command.log"
            with self.assertRaisesRegex(RuntimeError, "command failed"):
                benchmark.command(
                    [sys.executable, "-c", "raise SystemExit('benchmark failed')"],
                    environment=os.environ.copy(), log=log, deadline=time.monotonic() + 10,
                )
            self.assertIn("benchmark failed", log.read_text())

    def test_comparison_uses_median_of_each_mode_and_retains_spread(self):
        samples = [
            dict(target="field", workload="Fp/ProductSum/finish", mode=mode, nanoseconds=value)
            for mode, values in {
                "automatic": [12, 11, 100], "forced": [10, 9, 50], "portable": [20, 18, 40]
            }.items()
            for value in values
        ]
        row, = benchmark.summarize(samples, 3)
        self.assertEqual(row["automatic_median_ns"], 12)
        self.assertEqual(row["automatic_min_ns"], 11)
        self.assertEqual(row["automatic_max_ns"], 100)
        self.assertAlmostEqual(row["automatic_vs_forced_percent"], 20)
        self.assertAlmostEqual(row["automatic_vs_portable_percent"], -40)

    def test_missing_mode_does_not_produce_a_comparison(self):
        with self.assertRaisesRegex(ValueError, "incomplete runs"):
            benchmark.summarize([
                dict(target="fp", workload="Fp/square", mode="automatic", nanoseconds=12)
            ], 3)

    def test_no_measurements_is_an_error(self):
        with self.assertRaisesRegex(ValueError, "no benchmark measurements"):
            benchmark.summarize([], 3)

    def test_reads_criterion_median_and_rejects_missing_workloads(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            result = root / "Fp" / "mul" / "new"
            result.mkdir(parents=True)
            (result / "benchmark.json").write_text(json.dumps({"full_id": "Fp/mul"}))
            (result / "estimates.json").write_text(json.dumps({
                "median": {"point_estimate": 17.5}, "mean": {"point_estimate": 99}
            }))
            self.assertEqual(benchmark.collect_estimates(root, 1), {"Fp/mul": 17.5})
            with self.assertRaisesRegex(ValueError, "expected 2 workloads, found 1"):
                benchmark.collect_estimates(root, 2)


if __name__ == "__main__":
    unittest.main()
