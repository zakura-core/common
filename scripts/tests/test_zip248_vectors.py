import contextlib
import importlib.util
import io
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).parents[2]
SCRIPT = ROOT / "scripts" / "zip248" / "oracle.py"
TESTS = ROOT / "crates" / "zcash_primitives" / "src" / "transaction" / "v7" / "tests"
VECTORS = TESTS / "vectors.rs"
ENVELOPE_VECTORS = TESTS / "envelope_vectors.rs"
SPEC = importlib.util.spec_from_file_location("zip248_oracle", SCRIPT)
assert SPEC and SPEC.loader
oracle = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = oracle
SPEC.loader.exec_module(oracle)


class FrozenVectorsTest(unittest.TestCase):
    def test_oracle_agrees_with_the_frozen_vectors(self):
        vectors = oracle.read_vectors(str(VECTORS))
        self.assertGreaterEqual(len(vectors), 5)
        checked = 0
        for vector in vectors:
            with self.subTest(txid=vector["txid"]):
                checked += oracle.check_vector(vector)
        self.assertGreater(checked, 0)

    def test_oracle_rejects_a_changed_digest(self):
        vector = oracle.read_vectors(str(VECTORS))[0]
        vector["txid"] = "00" * 32
        with self.assertRaises(AssertionError):
            oracle.check_vector(vector)

    def test_oracle_agrees_with_the_envelope_vectors(self):
        vectors = oracle.envelope_vectors_from_rust(ENVELOPE_VECTORS.read_text())
        self.assertEqual(len(vectors), 6)
        for vector in vectors:
            with self.subTest(scenario=vector["scenario"]):
                oracle.check_envelope_vector(vector)

    def test_sighash_scenarios_need_other_variants(self):
        """The oracle's variant 0 check rejects each scenario with another sighashInfo."""
        vectors = oracle.envelope_vectors_from_rust(ENVELOPE_VECTORS.read_text())
        variant_scenarios = [v for v in vectors if "sighash variant" in v["scenario"]
                             or "associated data" in v["scenario"]]
        self.assertEqual(len(variant_scenarios), 3)
        for vector in variant_scenarios:
            with self.subTest(scenario=vector["scenario"]):
                with self.assertRaises(AssertionError):
                    oracle.digests(bytes.fromhex(vector["tx"]))

    def test_oracle_prints_the_envelope_digests(self):
        vector = oracle.envelope_vectors_from_rust(ENVELOPE_VECTORS.read_text())[0]
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            oracle.main(["--envelope-digests", vector["tx"]])
        self.assertEqual(
            out.getvalue(), f"txid {vector['txid']}\nauth_digest {vector['auth']}\n"
        )

    def test_oracle_rejects_a_changed_envelope_digest(self):
        vector = oracle.envelope_vectors_from_rust(ENVELOPE_VECTORS.read_text())[0]
        vector["auth"] = "00" * 32
        with self.assertRaises(AssertionError):
            oracle.check_envelope_vector(vector)


if __name__ == "__main__":
    unittest.main()
