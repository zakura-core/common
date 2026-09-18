#!/usr/bin/env python3
"""Unit tests for semver feature exception validation and manifest restoration."""

from pathlib import Path
import tempfile
import tomllib
import unittest

import check_semver


class FeatureExceptionsTest(unittest.TestCase):
    def policy(self, features):
        return {"excluded_features": {"example": features}}

    def packages(self, features=None):
        return {"example": {"features": features or {}}}

    def test_exact_removed_feature_is_allowed(self):
        self.assertEqual(
            check_semver.excluded_features(
                self.policy({"unused": "Never used"}), self.packages()
            ),
            {"example": {"unused": "Never used"}},
        )

    def test_rejects_default_and_transitive_default_features(self):
        for definitions in (
            {"default": ["unused"]},
            {"default": ["alias"], "alias": ["unused"]},
        ):
            with self.subTest(definitions=definitions), self.assertRaises(ValueError):
                check_semver.excluded_features(
                    self.policy({"unused": "Never used"}), self.packages(definitions)
                )

    def test_rejects_wildcards_missing_reasons_and_default(self):
        for feature, reason in (
            ("*", "all"),
            ("zip-*", "all"),
            ("unused", ""),
            ("unused", True),
            ("default", "all"),
        ):
            with (
                self.subTest(feature=feature, reason=reason),
                self.assertRaises(ValueError),
            ):
                check_semver.excluded_features(
                    self.policy({feature: reason}), self.packages()
                )

    def test_rejects_unknown_packages_and_invalid_policy(self):
        for policy in (
            {"excluded_features": {"typo": {}}},
            {"excluded_features": []},
            {"excluded_features": {}, "typo": {}},
            self.policy([]),
        ):
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                check_semver.excluded_features(policy, self.packages())

    def test_restores_manifest_after_check_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / "Cargo.toml"
            original = b'[package]\nname = "example"\n[features]\ndefault = []\n[dependencies]\n'
            manifest.write_bytes(original)
            with self.assertRaisesRegex(RuntimeError, "check failed"):
                with check_semver.feature_name_exceptions(manifest, ["unused"]):
                    features = tomllib.loads(manifest.read_text())["features"]
                    self.assertEqual(features, {"default": [], "unused": []})
                    raise RuntimeError("check failed")
            self.assertEqual(manifest.read_bytes(), original)

    def test_preserves_existing_feature_definitions(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / "Cargo.toml"
            original = b'[features]\nunused = ["other"]\nother = []\n'
            manifest.write_bytes(original)
            with check_semver.feature_name_exceptions(manifest, ["unused"]):
                self.assertEqual(manifest.read_bytes(), original)
            self.assertEqual(manifest.read_bytes(), original)

    def test_supports_manifest_without_features(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / "Cargo.toml"
            original = b'[package]\nname = "example"\n'
            manifest.write_bytes(original)
            with check_semver.feature_name_exceptions(manifest, ["unused"]):
                self.assertEqual(
                    tomllib.loads(manifest.read_text())["features"], {"unused": []}
                )
            self.assertEqual(manifest.read_bytes(), original)


if __name__ == "__main__":
    unittest.main()
