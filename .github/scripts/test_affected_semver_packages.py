#!/usr/bin/env python3
"""Tests for affected_semver_packages.py."""

from pathlib import Path
import subprocess
import tempfile
import unittest

import affected_semver_packages


class AffectedSemverPackagesTest(unittest.TestCase):
    def setUp(self):
        self.temporary_directory = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary_directory.name).resolve()

    def tearDown(self):
        self.temporary_directory.cleanup()

    def package(self, name, *, publish=None, dependencies=None, target_kinds=None):
        package_root = self.root / name
        package = {
            "id": name,
            "name": name,
            "manifest_path": str(package_root / "Cargo.toml"),
            "dependencies": dependencies or [],
            "targets": [
                {"name": name, "kind": kinds}
                for kinds in (target_kinds if target_kinds is not None else [["lib"]])
            ],
        }
        if publish is not None:
            package["publish"] = publish
        return package

    def dependency(self, name, *, kind=None):
        return {
            "name": name,
            "kind": kind,
            "path": str(self.root / name),
        }

    def metadata(self, packages):
        return {
            "workspace_root": str(self.root),
            "workspace_members": [package["id"] for package in packages],
            "packages": packages,
        }

    def git(self, *args):
        return subprocess.run(
            ["git", *args],
            cwd=self.root,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout.strip()

    def test_includes_publishable_reverse_dependencies(self):
        packages = [
            self.package("base"),
            self.package(
                "dependent",
                dependencies=[self.dependency("base")],
            ),
            self.package(
                "transitive",
                dependencies=[self.dependency("dependent", kind="build")],
            ),
            self.package(
                "dev-only",
                dependencies=[self.dependency("base", kind="dev")],
            ),
            self.package(
                "private-middle",
                publish=[],
                dependencies=[self.dependency("base")],
            ),
            self.package(
                "public-after-private",
                dependencies=[self.dependency("private-middle")],
            ),
        ]

        affected = affected_semver_packages.affected_publishable_packages(
            self.metadata(packages),
            changed_files=["base/src/lib.rs"],
        )

        self.assertEqual(
            affected,
            ["base", "dependent", "public-after-private", "transitive"],
        )

    def test_root_manifest_selects_every_publishable_package(self):
        packages = [
            self.package("z-last"),
            self.package("a-first"),
            self.package("private", publish=[]),
        ]

        affected = affected_semver_packages.affected_publishable_packages(
            self.metadata(packages),
            changed_files=["Cargo.toml"],
        )

        self.assertEqual(affected, ["a-first", "z-last"])

    def test_policy_changes_select_every_publishable_package(self):
        packages = [
            self.package("z-last"),
            self.package("a-first"),
            self.package("private", publish=[]),
        ]

        for policy_file in affected_semver_packages.SEMVER_POLICY_FILES:
            with self.subTest(policy_file=policy_file):
                affected = affected_semver_packages.affected_publishable_packages(
                    self.metadata(packages),
                    changed_files=[str(policy_file)],
                )

                self.assertEqual(affected, ["a-first", "z-last"])

    def test_ignores_lockfiles_and_non_rust_package_files(self):
        packages = [self.package("base")]

        affected = affected_semver_packages.affected_publishable_packages(
            self.metadata(packages),
            changed_files=["Cargo.lock", "base/README.md"],
        )

        self.assertEqual(affected, [])

    def test_package_manifest_selects_that_package(self):
        registry_dependency = {
            "name": "registry-package",
            "kind": None,
        }
        packages = [
            self.package("base", dependencies=[registry_dependency]),
            self.package("other"),
        ]

        affected = affected_semver_packages.affected_publishable_packages(
            self.metadata(packages),
            changed_files=["base/Cargo.toml"],
        )

        self.assertEqual(affected, ["base"])

    def test_explicit_publish_settings(self):
        packages = [
            self.package("default"),
            self.package("explicit", publish=True),
            self.package("private", publish=False),
            self.package("no-registry", publish=[]),
            self.package("registry", publish=["crates-io"]),
        ]

        affected = affected_semver_packages.affected_publishable_packages(
            self.metadata(packages),
            check_all=True,
        )

        self.assertEqual(affected, ["default", "explicit", "registry"])

    def test_skips_packages_without_a_library_target(self):
        packages = [
            self.package("macros", target_kinds=[["proc-macro"]]),
            self.package(
                "consumer",
                dependencies=[self.dependency("macros")],
            ),
            self.package("binary-only", target_kinds=[["bin"]]),
            self.package("c-library", target_kinds=[["cdylib", "rlib"]]),
        ]

        affected = affected_semver_packages.affected_publishable_packages(
            self.metadata(packages),
            changed_files=[
                "macros/src/lib.rs",
                "binary-only/src/main.rs",
                "c-library/src/lib.rs",
            ],
        )

        self.assertEqual(affected, ["c-library", "consumer"])

    def test_diff_reports_both_sides_of_a_rename(self):
        old_path = self.root / "source" / "src" / "lib.rs"
        new_path = self.root / "destination" / "src" / "lib.rs"
        old_path.parent.mkdir(parents=True)
        old_path.write_text("pub fn moved() {}\n", encoding="utf-8")

        self.git("init", "--quiet")
        self.git("config", "user.email", "ci@example.invalid")
        self.git("config", "user.name", "CI fixture")
        self.git("config", "diff.renames", "true")
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "base")
        base = self.git("rev-parse", "HEAD")

        new_path.parent.mkdir(parents=True)
        old_path.rename(new_path)
        self.git("add", "--all")
        self.git("commit", "--quiet", "-m", "rename")
        head = self.git("rev-parse", "HEAD")

        changed = affected_semver_packages.diff_changed_files(self.root, base, head)

        self.assertEqual(
            set(changed),
            {"source/src/lib.rs", "destination/src/lib.rs"},
        )


if __name__ == "__main__":
    unittest.main()
