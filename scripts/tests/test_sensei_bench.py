"""Protocol and statistical checks without expensive cryptographic proving."""

import contextlib
import importlib.machinery
import importlib.util
import io
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch


SCRIPT = Path(__file__).resolve().parents[1] / "sensei-bench"
LOADER = importlib.machinery.SourceFileLoader("sensei_bench", str(SCRIPT))
SPEC = importlib.util.spec_from_loader(LOADER.name, LOADER)
bench = importlib.util.module_from_spec(SPEC)
LOADER.exec_module(bench)


def events(leg, args, workers=2):
    return [
        {"type": "metadata", "protocol": bench.PROTOCOL_VERSION, "backend": leg["backend"],
         "mode": "verifier" if args.verifier else "prover",
         "portable": not args.asm, "workers": workers,
         "corpus_blake2b": leg.get("corpus_blake2b"), "corpus_proofs": leg.get("corpus_proofs", 0),
         "actions": leg["actions"], "sequence": leg["sequence"],
         "batch_size": leg["batch_size"],
         "samples": args.samples_per_leg, "warmup_seconds": args.warmup_seconds},
        {"type": "warmup", "ns": [1_000_000_000] * 10, "stable": True},
        *({"type": "sample", "index": index, "ns": 1_000_000}
          for index in range(args.samples_per_leg)),
        {"type": "complete", "samples": args.samples_per_leg},
    ]


def synthetic_legs(args, drift=False):
    legs = list(bench.schedule(args.rounds, args.batch_sizes))
    for leg in legs:
        native = 100_000_000
        if drift and leg["round"] > args.rounds // 2:
            native *= 1.2
        ns = int(native * (0.8 if leg["backend"] == "sensei" else 1))
        leg.update(workers=2, ns=[ns] * args.samples_per_leg, warmup={"stable": True})
    return legs


ARCHITECTURES = ("aarch64", "x86_64")


def host(machine):
    """Pin the host machine name that `--asm` maps to an assembly backend."""
    return patch.object(bench.platform, "machine", return_value=machine)


def pasta_artifacts(architecture=None):
    """Cargo records for the native build's Pasta library and build script.

    A target-specific dependency may force `aarch64-asm` on; `portable` must
    override it, and the build script's cfgs record the actual selection.
    """
    artifacts = [
        {"reason": "compiler-artifact", "package_id": "pasta-id",
         "target": {"name": "pasta_curves", "kind": ["lib"]},
         "features": ["aarch64-asm", "portable"]},
        {"reason": "build-script-executed", "package_id": "pasta-id", "cfgs": []},
    ]
    if architecture:
        artifacts[0]["features"] = [f"{architecture}-asm"]
        artifacts[1]["cfgs"].append(f"pasta_curves_{architecture}_asm")
    return artifacts


def udon_artifacts(architecture=None):
    """Udon's host unit and runtime unit for the sensei build.

    Sensei forwards its arithmetic features to both Udon units; only the
    runtime unit carries Sensei's `sqrt-table-large` dependency feature.
    """
    artifacts = [
        {"reason": "compiler-artifact", "package_id": "udon-id",
         "target": {"name": "zakura_udon", "kind": ["lib"]}, "features": ["portable"]},
        {"reason": "compiler-artifact", "package_id": "udon-id",
         "target": {"name": "zakura_udon", "kind": ["lib"]},
         "features": ["aarch64-asm", "portable", "sqrt-table-large"]},
        {"reason": "build-script-executed", "package_id": "udon-id", "cfgs": []},
        {"reason": "build-script-executed", "package_id": "udon-id", "cfgs": []},
    ]
    if architecture:
        artifacts[0]["features"] = [f"{architecture}-asm"]
        artifacts[1]["features"] = [f"{architecture}-asm", "sqrt-table-large"]
        for script in artifacts[2:]:
            script["cfgs"].extend([f"udon_{architecture}_asm", "udon_asm"])
    return artifacts


class BuildTests(unittest.TestCase):
    def test_backend_feature_isolation(self):
        for backend, selected, other in (("native", "backend-halo2", "backend-sensei"),
                                         ("sensei", "backend-sensei", "backend-halo2")):
            event = {"reason": "compiler-artifact",
                     "target": {"name": "orchard", "kind": ["lib"]}, "features": [selected]}
            bench.check_backend([event], backend)
            for features in ([selected, other], [other], []):
                event["features"] = features
                with self.subTest(backend=backend, features=features), \
                        self.assertRaisesRegex(ValueError, "backend features"):
                    bench.check_backend([event], backend)
            with self.assertRaisesRegex(ValueError, "backend features"):
                bench.check_backend([], backend)

    def test_build_selects_whole_binary_backends(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            source = directory / "worker"
            source.write_bytes(b"executable")
            for architecture in (None, *ARCHITECTURES):
                arch_feature = f"{architecture}-asm" if architecture else "portable"
                for backend in bench.BACKENDS:
                    if backend == "sensei":
                        expected = ["backend-sensei", "circuit", "multicore", "std",
                                    "zip32-addresses", "test-dependencies", "sensei-bench",
                                    arch_feature]
                    else:
                        expected = ["sensei-bench", "test-dependencies", arch_feature]

                    def run(command, output, _errors):
                        self.assertEqual(command[command.index("--features") + 1], ",".join(expected))
                        self.assertEqual("--no-default-features" in command, backend == "sensei")
                        artifacts = (udon_artifacts(architecture) if backend == "sensei"
                                     else pasta_artifacts(architecture))
                        artifacts.extend([
                            {"reason": "compiler-artifact", "target": {"name": "orchard", "kind": ["lib"]},
                             "features": ["backend-sensei"] if backend == "sensei"
                                         else ["backend-halo2", "default"]},
                            {"reason": "compiler-artifact", "target": {"name": "sensei_compare", "kind": ["bench"]},
                             "executable": str(source)},
                        ])
                        output.write("\n".join(map(json.dumps, artifacts)))

                    with self.subTest(architecture=architecture, backend=backend), \
                            patch.object(bench, "run_process", side_effect=run), \
                            contextlib.redirect_stdout(io.StringIO()):
                        bench.build(backend, directory, architecture)

    def test_arithmetic_audit_records_resolved_features(self):
        self.assertEqual(bench.check_arithmetic(pasta_artifacts(), "native"), {
            "pasta_features": [["aarch64-asm", "portable"]], "pasta_cfgs": [],
            "udon_features": [], "udon_cfgs": [],
        })
        self.assertEqual(bench.check_arithmetic(udon_artifacts(), "sensei"), {
            "pasta_features": [], "pasta_cfgs": [],
            "udon_features": [["portable"], ["aarch64-asm", "portable", "sqrt-table-large"]],
            "udon_cfgs": [],
        })
        for architecture in ARCHITECTURES:
            with self.subTest(architecture=architecture):
                self.assertEqual(
                    bench.check_arithmetic(pasta_artifacts(architecture), "native", architecture), {
                        "pasta_features": [[f"{architecture}-asm"]],
                        "pasta_cfgs": [f"pasta_curves_{architecture}_asm"],
                        "udon_features": [], "udon_cfgs": [],
                    })
                self.assertEqual(
                    bench.check_arithmetic(udon_artifacts(architecture), "sensei", architecture), {
                        "pasta_features": [], "pasta_cfgs": [],
                        "udon_features": [[f"{architecture}-asm"], [f"{architecture}-asm", "sqrt-table-large"]],
                        "udon_cfgs": sorted([f"udon_{architecture}_asm", "udon_asm"]),
                    })

    def test_arithmetic_audit_rejects_foreign_backend_crates(self):
        # Backend selection is per binary; even one library from the other
        # backend's stack invalidates the comparison.
        for extra in ("zakura_sensei", "zakura-udon", "bento"):
            artifacts = pasta_artifacts()
            artifacts.append({"reason": "compiler-artifact", "package_id": "foreign-id",
                              "target": {"name": extra, "kind": ["lib"]}, "features": []})
            with self.subTest(extra=extra), \
                    self.assertRaisesRegex(ValueError, "other backend"):
                bench.check_arithmetic(artifacts, "native")
        for extra in ("pasta_curves", "halo2_proofs", "orchard_legacy", "sinsemilla"):
            artifacts = udon_artifacts()
            artifacts.append({"reason": "compiler-artifact", "package_id": "foreign-id",
                              "target": {"name": extra, "kind": ["lib"]}, "features": []})
            with self.subTest(extra=extra), \
                    self.assertRaisesRegex(ValueError, "other backend"):
                bench.check_arithmetic(artifacts, "sensei")

    def test_arithmetic_audit_rejects_assembly_and_missing_evidence(self):
        # Build scripts report selected assembly whether a Cargo feature or
        # RUSTFLAGS chose it, in the host unit as well as the runtime unit.
        for cfg in ("udon_aarch64_asm", "udon_x86_64_asm", "udon_asm"):
            for index in (2, 3):
                artifacts = udon_artifacts()
                artifacts[index]["cfgs"].append(cfg)
                with self.subTest(index=index, cfg=cfg), self.assertRaisesRegex(ValueError, "Udon assembly"):
                    bench.check_arithmetic(artifacts, "sensei")
        for cfg in ("pasta_curves_aarch64_asm", "pasta_curves_x86_64_asm"):
            artifacts = pasta_artifacts()
            artifacts[1]["cfgs"].append(cfg)
            with self.subTest(cfg=cfg), self.assertRaisesRegex(ValueError, "Pasta assembly"):
                bench.check_arithmetic(artifacts, "native")
        artifacts = pasta_artifacts()
        artifacts[0]["features"].remove("portable")
        with self.assertRaisesRegex(ValueError, "enable portable"):
            bench.check_arithmetic(artifacts, "native")
        artifacts = udon_artifacts()
        artifacts[1]["features"].remove("portable")
        with self.assertRaisesRegex(ValueError, "enable portable"):
            bench.check_arithmetic(artifacts, "sensei")
        with self.assertRaises(ValueError):
            bench.check_arithmetic(pasta_artifacts()[:1], "native")
        with self.assertRaises(ValueError):
            bench.check_arithmetic([], "native")
        complete = udon_artifacts()
        missing = [[], complete[:2], complete[:1] + complete[2:]]
        for artifacts in missing:
            with self.subTest(artifacts=artifacts), self.assertRaises(ValueError):
                bench.check_arithmetic(artifacts, "sensei")

    def test_asm_audit_requires_the_runtime_backends(self):
        for architecture in ARCHITECTURES:
            other, = set(ARCHITECTURES) - {architecture}
            for cfgs in ([], [f"pasta_curves_{other}_asm"],
                         [f"pasta_curves_{architecture}_asm", f"pasta_curves_{other}_asm"]):
                artifacts = pasta_artifacts(architecture)
                artifacts[1]["cfgs"] = cfgs
                with self.subTest(architecture=architecture, cfgs=cfgs), \
                        self.assertRaisesRegex(ValueError, "requires active"):
                    bench.check_arithmetic(artifacts, "native", architecture)
            artifacts = pasta_artifacts(architecture)
            artifacts.append({"reason": "build-script-executed", "package_id": "pasta-id", "cfgs": []})
            with self.subTest(architecture=architecture), self.assertRaisesRegex(ValueError, "every build"):
                bench.check_arithmetic(artifacts, "native", architecture)
            artifacts = pasta_artifacts(architecture)
            artifacts[0]["features"].append("portable")
            with self.subTest(architecture=architecture), self.assertRaisesRegex(ValueError, "disable portable"):
                bench.check_arithmetic(artifacts, "native", architecture)
            # The host unit's features alone never prove the runtime selection.
            for host_asm in (False, True):
                artifacts = udon_artifacts(architecture)
                artifacts[0]["features"] = [f"{architecture}-asm"] if host_asm else []
                artifacts[1]["features"].remove(f"{architecture}-asm")
                with self.subTest(architecture=architecture, host_asm=host_asm), \
                        self.assertRaisesRegex(ValueError, "runtime build"):
                    bench.check_arithmetic(artifacts, "sensei", architecture)
            for cfgs in ([], ["udon_asm"], [f"udon_{other}_asm", "udon_asm"]):
                artifacts = udon_artifacts(architecture)
                for script in artifacts[2:]:
                    script["cfgs"] = list(cfgs)
                with self.subTest(architecture=architecture, cfgs=cfgs), \
                        self.assertRaisesRegex(ValueError, "runtime build"):
                    bench.check_arithmetic(artifacts, "sensei", architecture)
            artifacts = udon_artifacts(architecture)
            artifacts[1]["features"].append("portable")
            with self.subTest(architecture=architecture), self.assertRaisesRegex(ValueError, "without portable"):
                bench.check_arithmetic(artifacts, "sensei", architecture)
            with self.subTest(architecture=architecture), self.assertRaisesRegex(ValueError, "missing Udon"):
                bench.check_arithmetic([], "sensei", architecture)
            complete = udon_artifacts(architecture)
            with self.subTest(architecture=architecture), self.assertRaisesRegex(ValueError, "runtime build"):
                bench.check_arithmetic(complete[:1] + complete[2:], "sensei", architecture)


class ArgumentTests(unittest.TestCase):
    def test_explicit_mode_selection(self):
        self.assertFalse(bench.arguments(["--prover"]).verifier)
        self.assertTrue(bench.arguments(["--verifier"]).verifier)

    def test_missing_or_conflicting_modes_fail_before_work(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "results"
            for flags in ([], ["--prover", "--verifier"], ["--verifier", "--prover"]):
                with self.subTest(flags=flags), patch.object(bench, "build") as build, \
                        contextlib.redirect_stderr(io.StringIO()), \
                        self.assertRaises(SystemExit) as error:
                    bench.main([*flags, "--output", str(output)])
                self.assertEqual(error.exception.code, 2)
                build.assert_not_called()
                self.assertFalse(output.exists())

    def test_help_does_not_require_a_mode(self):
        with contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit) as error:
            bench.arguments(["--help"])
        self.assertEqual(error.exception.code, 0)

    def test_asm_selects_the_host_assembly_backend(self):
        for machine, architecture in (("arm64", "aarch64"), ("aarch64", "aarch64"),
                                      ("x86_64", "x86_64"), ("AMD64", "x86_64")):
            with self.subTest(machine=machine), host(machine):
                self.assertEqual(bench.arguments(["--prover", "--asm"]).architecture, architecture)
                self.assertIsNone(bench.arguments(["--prover"]).architecture)
        with host("riscv64"), contextlib.redirect_stderr(io.StringIO()), \
                self.assertRaises(SystemExit) as error:
            bench.arguments(["--prover", "--asm"])
        self.assertEqual(error.exception.code, 2)

    def test_x86_64_asm_requires_cpu_extensions_before_any_work(self):
        self.assertIn(bench.x86_64_extensions_available(), (True, False, None))
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "results"
            with host("x86_64"), patch.object(bench, "x86_64_extensions_available", return_value=False), \
                    patch.object(bench, "build") as build, contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(bench.main(["--prover", "--asm", "--output", str(output)]), 2)
            build.assert_not_called()
            self.assertFalse(output.exists())


class ScheduleTests(unittest.TestCase):
    def test_verifier_schedules_individual_and_distinct_batch_sizes(self):
        args = bench.arguments(["--verifier"])
        self.assertEqual(args.batch_sizes, [1, 2, 16, 64])
        legs = list(bench.schedule(args.rounds, args.batch_sizes))
        for actions in (1, 2):
            for size in args.batch_sizes:
                group = [leg for leg in legs if leg["actions"] == actions and leg["batch_size"] == size]
                self.assertEqual(len(group), 4 * (args.rounds + 1))
                seeds = {b: [leg["sequence"] for leg in group if leg["backend"] == b] for b in bench.BACKENDS}
                self.assertEqual(seeds["native"], seeds["sensei"])
        self.assertEqual(bench.arguments(["--verifier", "--batch-sizes"]).batch_sizes, [1])
        for argv in (["--prover", "--batch-sizes", "2"], ["--verifier", "--batch-sizes", "1"],
                     ["--verifier", "--batch-sizes", "2", "2"]):
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                bench.arguments(argv)

    def test_quick_and_thorough_budgets_and_explicit_overrides(self):
        quick = bench.arguments(["--prover"])
        self.assertFalse(quick.asm)
        self.assertFalse(quick.verifier)
        with host("arm64"):
            self.assertTrue(bench.arguments(["--verifier", "--asm", "--thorough"]).verifier)
        self.assertEqual((quick.rounds, quick.samples_per_leg, quick.warmup_seconds), (2, 5, 1.0))
        self.assertEqual(len(list(bench.schedule(quick.rounds))), 24)
        for result in bench.summarize(synthetic_legs(quick), quick, resamples=10)["results"]:
            self.assertTrue(result["provisional"])
            self.assertEqual(result["backends"]["native"]["samples"], 20)
        thorough = bench.arguments(["--prover", "--thorough"])
        self.assertEqual((thorough.rounds, thorough.samples_per_leg, thorough.warmup_seconds), (10, 20, 5.0))
        for argv in (["--thorough", "--rounds", "4", "--samples-per-leg", "3", "--warmup-seconds", "0"],
                     ["--rounds", "4", "--samples-per-leg", "3", "--warmup-seconds", "0", "--thorough"]):
            custom = bench.arguments(["--prover", *argv])
            self.assertEqual((custom.rounds, custom.samples_per_leg, custom.warmup_seconds), (4, 3, 0.0))

    def test_balance_sample_counts_seeds_and_linear_drift(self):
        args = bench.arguments(["--prover", "--thorough"])
        legs = list(bench.schedule(args.rounds))
        measured = [leg for leg in legs if not leg["settling"]]
        self.assertEqual(len(legs), 88)
        for actions in (1, 2):
            for backend in bench.BACKENDS:
                chosen = [leg for leg in measured if leg["actions"] == actions and leg["backend"] == backend]
                self.assertEqual(len(chosen) * args.samples_per_leg, 400)
                self.assertEqual({position: sum(leg["position"] == position for leg in chosen)
                                  for position in range(4)}, dict.fromkeys(range(4), 5))
        for round_index in range(args.rounds + 1):
            ordered = [leg for leg in legs if leg["round"] == round_index]
            self.assertEqual(ordered[0]["actions"], 2 if round_index % 2 else 1)
            for actions in (1, 2):
                group = [leg for leg in ordered if leg["actions"] == actions]
                seeds = {backend: [leg["sequence"] for leg in group if leg["backend"] == backend]
                         for backend in bench.BACKENDS}
                self.assertEqual(seeds["native"], seeds["sensei"])
                # Equal sums of positions cancel any additive linear leg drift.
                self.assertEqual(sum(leg["position"] for leg in group if leg["backend"] == "native"),
                                 sum(leg["position"] for leg in group if leg["backend"] == "sensei"))


class StatisticsTests(unittest.TestCase):
    def test_verifier_summary_identifies_operation(self):
        args = bench.arguments(["--verifier"])
        summary = bench.summarize(synthetic_legs(args), args, resamples=10)
        self.assertEqual(summary["mode"], "verifier")
        self.assertIn("Warm verification times", bench.format_summary(summary))

    def test_summary_identifies_arithmetic_mode(self):
        for argv, machine, mode, label in (
                (["--prover"], "x86_64", "portable", "assembly disabled"),
                (["--prover", "--asm"], "x86_64", "asm", "x86-64 assembly enabled"),
                (["--prover", "--asm", "--thorough"], "arm64", "asm", "AArch64 assembly enabled")):
            with host(machine):
                args = bench.arguments(argv)
            summary = bench.summarize(synthetic_legs(args), args, resamples=10)
            with self.subTest(argv=argv):
                self.assertEqual(summary["arithmetic_mode"], mode)
                self.assertIn(f"Pasta/Udon {label} in both builds", bench.format_summary(summary))

    def test_percentages_express_time_saved_and_time_added(self):
        self.assertEqual(bench.savings(100, 75), 25)
        self.assertEqual(bench.savings(100, 125), -25)
        self.assertEqual(bench.comparison(25), "25.00% less time")
        self.assertEqual(bench.comparison(-25), "25.00% more time")

    def test_bootstrap_preserves_pairing_and_round_clusters(self):
        rounds = [{"native": [100] * 40, "sensei": [80] * 40},
                  {"native": [200] * 40, "sensei": [160] * 40}]
        result = bench.bootstrap(rounds, resamples=1000)
        self.assertEqual(result, bench.bootstrap(rounds, resamples=1000))
        self.assertEqual(result["paired_savings_pct"], [20, 20])
        # Individual-sample resampling would spuriously narrow these intervals.
        self.assertEqual(result["median_ns"]["native"], [100, 200])

    def test_summary_drift_precision_and_warmup(self):
        args = bench.arguments(["--prover", "--thorough"])
        good = synthetic_legs(args)
        summary = bench.summarize(good, args, resamples=100)
        for result in summary["results"]:
            self.assertFalse(result["provisional"])
            self.assertFalse(result["inconclusive"])
            self.assertEqual(result["median_savings_pct"], 20)
            self.assertEqual(result["backends"]["native"]["samples"], 400)
        noisy = synthetic_legs(args, drift=True)
        noisy[-1]["warmup"]["stable"] = False
        warnings = [warning for result in bench.summarize(noisy, args, resamples=100)["results"]
                    for warning in result["warnings"]]
        self.assertTrue(any("drift" in warning for warning in warnings))
        self.assertTrue(any("confidence" in warning for warning in warnings))
        self.assertTrue(any("warmup" in warning for warning in warnings))

    def test_inconclusive_reduced_and_incomplete_runs(self):
        args = bench.arguments(["--prover", "--rounds", "1", "--samples-per-leg", "1"])
        legs = synthetic_legs(args)
        for leg in legs:
            leg["ns"] = [100]
        for result in bench.summarize(legs, args, resamples=10)["results"]:
            self.assertTrue(result["provisional"])
            self.assertTrue(result["inconclusive"])
        with self.assertRaisesRegex(ValueError, "incomplete paired round"):
            bench.summarize(legs[:-1], args, resamples=10)


class ProtocolTests(unittest.TestCase):
    def test_verifier_rejects_wrong_mode_or_corpus(self):
        args = bench.arguments(["--verifier"])
        leg = dict(next(bench.schedule(1)), corpus_blake2b="recorded-hash", corpus_proofs=10)
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "worker.jsonl"
            records = events(leg, args)
            path.write_text("\n".join(map(json.dumps, records)))
            self.assertEqual(bench.parse_leg(path, leg, args)["workers"], 2)
            for key, value in (("mode", "prover"), ("batch_size", 2), ("corpus_blake2b", "changed"),
                               ("corpus_proofs", 1)):
                records = events(leg, args)
                records[0][key] = value
                path.write_text("\n".join(map(json.dumps, records)))
                with self.subTest(key=key), self.assertRaisesRegex(ValueError, key):
                    bench.parse_leg(path, leg, args)

    def test_verifier_run_generates_once_and_shares_recorded_corpus(self):
        with tempfile.TemporaryDirectory() as temporary:
            argv = ["--verifier", "--output", temporary, "--rounds", "1", "--samples-per-leg", "1"]
            args = bench.arguments(argv)
            pending = iter(bench.schedule(args.rounds, args.batch_sizes))
            generated = []

            def run(command, output, _errors):
                if command[1] == "--generate-verifier-fixtures":
                    self.assertEqual(command[0], "/native")
                    generated.append(command)
                    for actions in (1, 2):
                        corpus = {"version": bench.CORPUS_VERSION, "actions": actions,
                                  "proofs": [[index] for index in range(int(command[3]))]}
                        (Path(command[2]) / f"verifier-{actions}.json").write_text(json.dumps(corpus))
                    return
                self.assertEqual(command[1], "verifier")
                leg = next(pending)
                path = Path(command[-1])
                self.assertEqual(path.name, f"verifier-{leg['actions']}.json")
                leg.update(corpus_blake2b=hashlib.blake2b(path.read_bytes(), digest_size=32).hexdigest(),
                           corpus_proofs=max(args.batch_sizes))
                output.write("\n".join(map(json.dumps, events(leg, args))))

            with patch.object(bench, "build", side_effect=lambda backend, *_: {"binary": f"/{backend}"}), \
                    patch.object(bench, "probe", return_value={}), \
                    patch.object(bench, "telemetry", return_value={}), \
                    patch.object(bench, "run_process", side_effect=run), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(bench.main(argv), 0)
            self.assertEqual(len(generated), 1)
            run_file, = Path(temporary).glob("*/run.json")
            state = json.loads(run_file.read_text())
            self.assertEqual(state["status"], "complete")
            self.assertEqual(state["mode"], "verifier")
            self.assertEqual(len(state["legs"]), len(list(bench.schedule(1, args.batch_sizes))))
            self.assertTrue((run_file.parent / "samples.csv").read_text().startswith("mode,"))

    def test_worker_output_validation(self):
        args = bench.arguments(["--prover", "--workers", "2", "--samples-per-leg", "2"])
        leg = next(bench.schedule(1))
        valid = events(leg, args)
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "worker.jsonl"

            def parse(records):
                path.write_text("\n".join(json.dumps(record) for record in records))
                return bench.parse_leg(path, leg, args)

            self.assertEqual(parse(valid)["workers"], 2)
            broken = [valid[:-1], events(leg, args, workers=1)]
            for key, value in [("protocol", 1), ("backend", "sensei"), ("portable", False), ("sequence", 42)]:
                copy = events(leg, args)
                copy[0][key] = value
                broken.append(copy)
            for section, key, value in [(1, "stable", False), (1, "ns", [1]),
                                        (2, "ns", 0), (2, "index", True), (-1, "samples", 0),
                                        (-1, "samples", True)]:
                copy = events(leg, args)
                copy[section][key] = value
                broken.append(copy)
            for records in broken:
                with self.subTest(records=records), self.assertRaises(ValueError):
                    parse(records)
            leg["backend"] = "sensei"
            self.assertEqual(parse(events(leg, args))["workers"], 2)
            assembly_allowed = events(leg, args)
            assembly_allowed[0]["portable"] = False
            with self.assertRaisesRegex(ValueError, "portable"):
                parse(assembly_allowed)
            args.asm = True
            for backend in bench.BACKENDS:
                leg["backend"] = backend
                self.assertEqual(parse(events(leg, args))["workers"], 2)
                portable = events(leg, args)
                portable[0]["portable"] = True
                with self.subTest(backend=backend), self.assertRaisesRegex(ValueError, "portable"):
                    parse(portable)

    def test_interruption_keeps_completed_legs_and_partial_logs(self):
        with tempfile.TemporaryDirectory() as temporary:
            argv = ["--prover", "--output", temporary, "--rounds", "1", "--samples-per-leg", "1"]
            args = bench.arguments(argv)
            first = next(bench.schedule(1))
            calls = 0

            def run(_command, output, _errors):
                nonlocal calls
                calls += 1
                if calls == 1:
                    output.write("\n".join(json.dumps(event) for event in events(first, args)))
                else:
                    output.write('{"partial": true}\n')
                    raise KeyboardInterrupt

            with patch.object(bench, "build", return_value={"binary": "/unused"}), \
                    patch.object(bench, "probe", return_value={}), \
                    patch.object(bench, "telemetry", return_value={}), \
                    patch.object(bench, "run_process", side_effect=run), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(bench.main(argv), 130)
            run_file, = Path(temporary).glob("*/run.json")
            state = json.loads(run_file.read_text())
            self.assertEqual(state["status"], "interrupted")
            self.assertEqual(len(state["legs"]), 1)
            self.assertIn("active_leg", state)
            self.assertTrue(any("partial" in path.read_text() for path in run_file.parent.glob("*.jsonl")))

    def test_interruption_terminates_active_process(self):
        process = Mock(pid=12345)
        process.wait.side_effect = [KeyboardInterrupt, 0]
        process.poll.return_value = None
        with patch.object(bench.subprocess, "Popen", return_value=process), \
                patch.object(bench.os, "killpg", create=True) as kill:
            with self.assertRaises(KeyboardInterrupt):
                bench.run_process(["unused"], None, None)
            if bench.os.name == "posix":
                kill.assert_called_once_with(process.pid, bench.signal.SIGTERM)
            else:
                process.terminate.assert_called_once()


if __name__ == "__main__":
    unittest.main()
