#!/usr/bin/env python3
"""Check feature selection without invoking Cargo or depending on the workspace."""
import unittest
from supported_features import supported_features


class SupportedFeaturesTests(unittest.TestCase):
    def setUp(self):
        self.metadata = {
            "workspace_members": ["a-id", "b-id", "c-id"],
            "packages": [
                {"id": "a-id", "name": "a", "features": {
                    "std": [], "default": [], "backend-halo2": [], "backend-alternate": []}},
                {"id": "b-id", "name": "b", "features": {
                    "alloc": [], "pallas-pasta": [], "pallas-alternate": []}},
                {"id": "c-id", "name": "c", "features": {}},
                {"id": "external", "name": "external", "features": {"unrelated": []}},
            ],
        }

    def test_selected_package_retains_capabilities_and_default_backend(self):
        self.assertEqual(supported_features(self.metadata, {"a"}),
                         ["a/backend-halo2", "a/default", "a/std"])

    def test_workspace_excludes_alternate_selectors_and_external_packages(self):
        self.assertEqual(supported_features(self.metadata, {"--workspace"}),
                         ["a/backend-halo2", "a/default", "a/std", "b/alloc", "b/pallas-pasta"])

    def test_unknown_package_does_not_enable_workspace_features(self):
        with self.assertRaises(ValueError):
            supported_features(self.metadata, {"unknown"})

    def test_featureless_package_needs_no_feature_arguments(self):
        self.assertEqual(supported_features(self.metadata, {"c"}), [])


if __name__ == "__main__":
    unittest.main()
