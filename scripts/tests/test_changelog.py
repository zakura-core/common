import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


SCRIPT = Path(__file__).parents[1] / "changelog.py"
SPEC = importlib.util.spec_from_file_location("libraries_changelog", SCRIPT)
assert SPEC and SPEC.loader
changelog = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = changelog
SPEC.loader.exec_module(changelog)


WORKSPACE_MANIFEST = """\
[workspace]
members = ["crates/alpha", "crates/beta"]
"""

MEMBER_MANIFEST = """\
[package]
name = "{name}"
"""

SEEDED_CHANGELOG = """\
# Changelog

## [Unreleased]
{unreleased}{versions}
## Record of Fork

`{name}` began as a fork.
"""

CHANGELOG_WITH_CANDIDATES = """\
# Changelog

## [Unreleased]

## [1.0.0-rc.2] - 2026-07-21

### Fixed

- Second candidate fix.

## [1.0.0-rc.1] - 2026-07-20

### Added

- First candidate feature.

## Record of Fork

`{name}` began as a fork.
"""


CHANGELOG_WITH_PRERELEASES = """\
# Changelog

## [Unreleased]

## [1.3.0-rc.1] - 2026-07-22

### Fixed

- Candidate fix.

## [1.3.0-alpha.1] - 2026-07-21

### Added

- Alpha feature.

## [1.2.0] - 2026-07-20

### Added

- Previous stable feature.

## Record of Fork

`{name}` began as a fork.
"""


def seeded_changelog(name: str, unreleased: str = "", versions: str = "") -> str:
    return SEEDED_CHANGELOG.format(
        name=name, unreleased=unreleased, versions=versions
    )


class ChangelogTests(unittest.TestCase):
    def setUp(self):
        self.temporary_directory = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary_directory.name)
        self.fragments = self.root / "docs" / "changelog" / "unreleased"
        self.fragments.mkdir(parents=True)
        (self.fragments / "README.md").write_text("# Fragments\n")
        (self.root / "Cargo.toml").write_text(WORKSPACE_MANIFEST)
        for member, name in (("alpha", "zakura-alpha"), ("beta", "zakura-beta")):
            directory = self.root / "crates" / member
            directory.mkdir(parents=True)
            (directory / "Cargo.toml").write_text(MEMBER_MANIFEST.format(name=name))
            (directory / "CHANGELOG.md").write_text(seeded_changelog(name))

    def tearDown(self):
        self.temporary_directory.cleanup()

    def write_fragment(self, name: str, text: str) -> Path:
        path = self.fragments / name
        path.write_text(text)
        return path

    def member_changelog(self, member: str) -> Path:
        return self.root / "crates" / member / "CHANGELOG.md"

    def test_maps_package_names_to_changelogs(self):
        changelogs = changelog.workspace_changelogs(self.root)

        self.assertEqual(
            changelogs,
            {
                "zakura-alpha": self.member_changelog("alpha"),
                "zakura-beta": self.member_changelog("beta"),
            },
        )

    def test_parses_multi_crate_fragment(self):
        self.write_fragment(
            "123.md",
            "## zakura-alpha\n\n### Fixed\n\n- Fixed a bug.\n\n"
            "### Added\n\n- Added a feature.\n\n"
            "## zakura-beta\n\n### Changed\n\n- Changed behavior.\n",
        )

        fragment = changelog.load_fragments(self.root)[0]

        self.assertEqual(fragment.entries["zakura-alpha"]["Fixed"], "- Fixed a bug.")
        self.assertEqual(
            fragment.entries["zakura-alpha"]["Added"], "- Added a feature."
        )
        self.assertEqual(
            fragment.entries["zakura-beta"]["Changed"], "- Changed behavior."
        )

    def test_rejects_unknown_crate(self):
        self.write_fragment("123.md", "## zakura-gamma\n\n### Fixed\n\n- Fix.\n")

        with self.assertRaisesRegex(changelog.ChangelogError, "unknown crate"):
            changelog.load_fragments(self.root)

    def test_rejects_category_outside_crate_section(self):
        self.write_fragment("123.md", "### Fixed\n\n- Fix.\n")

        with self.assertRaisesRegex(changelog.ChangelogError, "inside a crate"):
            changelog.load_fragments(self.root)

    def test_rejects_invalid_category(self):
        self.write_fragment("123.md", "## zakura-alpha\n\n### Improved\n\n- Fix.\n")

        with self.assertRaisesRegex(changelog.ChangelogError, "invalid category"):
            changelog.load_fragments(self.root)

    def test_rejects_crate_section_without_entries(self):
        self.write_fragment(
            "123.md",
            "## zakura-alpha\n\n## zakura-beta\n\n### Fixed\n\n- Fix.\n",
        )

        with self.assertRaisesRegex(changelog.ChangelogError, "no entries"):
            changelog.load_fragments(self.root)

    def test_requires_reason_for_no_changelog_fragment(self):
        self.write_fragment("123.md", "<!-- changelog: none -->\n<!-- nope -->\n")

        with self.assertRaisesRegex(changelog.ChangelogError, "explain why"):
            changelog.load_fragments(self.root)

    def test_accepts_no_changelog_fragment_with_reason(self):
        self.write_fragment(
            "123.md", "<!-- changelog: none -->\n\nThis PR only changes tests.\n"
        )

        fragment = changelog.load_fragments(self.root)[0]

        self.assertEqual(fragment.entries, {})

    def test_rejects_fragment_without_pull_request_number(self):
        self.write_fragment("my-change.md", "## zakura-alpha\n\n### Fixed\n\n- F.\n")

        with self.assertRaisesRegex(changelog.ChangelogError, "pull request number"):
            changelog.load_fragments(self.root)

    def test_rejects_nested_fragment_directory(self):
        (self.fragments / "123").mkdir()

        with self.assertRaisesRegex(changelog.ChangelogError, "Markdown files"):
            changelog.load_fragments(self.root)

    def test_seed_check_requires_fork_section(self):
        self.member_changelog("beta").write_text("# Changelog\n\n## [Unreleased]\n")

        with self.assertRaisesRegex(changelog.ChangelogError, "Record of Fork"):
            changelog.check_seeds(self.root)

    def test_seed_check_requires_unreleased_section(self):
        self.member_changelog("beta").write_text(
            "# Changelog\n\n## Record of Fork\n\ntext\n"
        )

        with self.assertRaisesRegex(changelog.ChangelogError, "Unreleased"):
            changelog.check_seeds(self.root)

    def test_pull_request_owns_its_numbered_fragment(self):
        self.write_fragment(
            "123.md", "<!-- changelog: none -->\n\nThis PR only changes tests.\n"
        )

        with mock.patch.object(
            changelog,
            "run_git",
            return_value="A\tdocs/changelog/unreleased/123.md\n",
        ) as run_git:
            changelog.check_pull_request(self.root, "base", "head", "123", False, False)

        run_git.assert_called_once_with(
            self.root,
            ["diff", "--name-status", "--find-renames=100%", "base...head"],
        )

    def test_pull_request_cannot_delete_another_fragment(self):
        self.write_fragment(
            "123.md", "<!-- changelog: none -->\n\nThis PR only changes tests.\n"
        )

        with mock.patch.object(
            changelog,
            "run_git",
            return_value=(
                "A\tdocs/changelog/unreleased/123.md\n"
                "D\tdocs/changelog/unreleased/122.md\n"
            ),
        ):
            with self.assertRaisesRegex(changelog.ChangelogError, "unexpected"):
                changelog.check_pull_request(
                    self.root, "base", "head", "123", False, False
                )

    def test_pull_request_may_move_fragments_without_content_changes(self):
        with mock.patch.object(
            changelog,
            "run_git",
            return_value=(
                "R100\told-fragments/122.md\tdocs/changelog/unreleased/122.md\n"
                "R100\told-fragments/README.md\tdocs/changelog/unreleased/README.md\n"
            ),
        ):
            changelog.check_pull_request(self.root, "base", "head", "123", False, False)

    def test_rust_pull_request_requires_fragment(self):
        with mock.patch.object(
            changelog,
            "run_git",
            return_value="M\tcrates/alpha/src/lib.rs\n",
        ):
            with self.assertRaisesRegex(changelog.ChangelogError, "add .*123.md"):
                changelog.check_pull_request(
                    self.root, "base", "head", "123", False, False
                )

    def test_cargo_toml_pull_request_requires_fragment(self):
        with mock.patch.object(
            changelog,
            "run_git",
            return_value="M\tcrates/alpha/Cargo.toml\n",
        ):
            with self.assertRaisesRegex(changelog.ChangelogError, "add .*123.md"):
                changelog.check_pull_request(
                    self.root, "base", "head", "123", False, False
                )

    def test_non_rust_pull_request_does_not_require_fragment(self):
        with mock.patch.object(
            changelog,
            "run_git",
            return_value="M\t.github/workflows/changelog.yml\nM\tCargo.lock\n",
        ):
            changelog.check_pull_request(self.root, "base", "head", "123", False, False)

    def test_release_pr_requires_all_fragments_consumed(self):
        self.write_fragment(
            "123.md", "<!-- changelog: none -->\n\nThis PR only changes tests.\n"
        )

        with self.assertRaisesRegex(changelog.ChangelogError, "must consume"):
            changelog.check_pull_request(self.root, "base", "head", "124", True, False)

    def test_release_folds_fragments_into_their_crates(self):
        self.write_fragment(
            "123.md",
            "## zakura-alpha\n\n### Fixed\n\n"
            "- Fixed a bug ([#123](https://example.invalid/123)).\n",
        )
        self.write_fragment(
            "124.md",
            "## zakura-alpha\n\n### Added\n\n- Added a feature.\n\n"
            "## zakura-beta\n\n### Fixed\n\n- Fixed beta.\n",
        )

        writes, removals = changelog.release_plan(self.root, "v1.1.0", "2026-08-28")

        alpha = writes[self.member_changelog("alpha")]
        beta = writes[self.member_changelog("beta")]
        self.assertIn("## [1.1.0] - 2026-08-28", alpha)
        self.assertIn(
            "### Added\n\n- Added a feature.\n\n### Fixed\n\n- Fixed a bug", alpha
        )
        self.assertIn("## [1.1.0] - 2026-08-28", beta)
        self.assertIn("### Fixed\n\n- Fixed beta.", beta)
        self.assertIn("## [Unreleased]\n\n## [1.1.0]", alpha)
        self.assertEqual(
            sorted(path.name for path in removals), ["123.md", "124.md"]
        )

    def test_release_skips_crates_without_entries(self):
        self.write_fragment(
            "123.md", "## zakura-alpha\n\n### Fixed\n\n- Fixed a bug.\n"
        )

        writes, _ = changelog.release_plan(self.root, "v1.1.0", "2026-08-28")

        self.assertIn(self.member_changelog("alpha"), writes)
        self.assertNotIn(self.member_changelog("beta"), writes)

    def test_release_merges_handwritten_unreleased_entries(self):
        self.member_changelog("beta").write_text(
            seeded_changelog(
                "zakura-beta", unreleased="\n### Changed\n\n- Hand-written change.\n"
            )
        )

        writes, _ = changelog.release_plan(self.root, "v1.1.0", "2026-08-28")

        beta = writes[self.member_changelog("beta")]
        self.assertIn("## [1.1.0] - 2026-08-28", beta)
        self.assertIn("### Changed\n\n- Hand-written change.", beta)
        unreleased = beta.split("## [1.1.0]")[0]
        self.assertNotIn("Hand-written", unreleased)

    def test_stable_release_combines_and_removes_release_candidates(self):
        self.member_changelog("alpha").write_text(
            CHANGELOG_WITH_CANDIDATES.format(name="zakura-alpha")
        )
        self.write_fragment(
            "125.md", "## zakura-alpha\n\n### Fixed\n\n- Final fix.\n"
        )

        writes, _ = changelog.release_plan(self.root, "v1.0.0", "2026-08-28")

        alpha = writes[self.member_changelog("alpha")]
        self.assertIn("## [1.0.0] - 2026-08-28", alpha)
        self.assertNotIn("1.0.0-rc", alpha)
        self.assertTrue(
            alpha.endswith("## Record of Fork\n\n`zakura-alpha` began as a fork.\n")
        )
        added = alpha.index("First candidate feature")
        early_fix = alpha.index("Second candidate fix")
        late_fix = alpha.index("Final fix")
        self.assertLess(early_fix, late_fix)
        self.assertTrue(added)

    def test_stable_release_combines_alpha_and_candidate_prereleases(self):
        self.member_changelog("alpha").write_text(
            CHANGELOG_WITH_PRERELEASES.format(name="zakura-alpha")
        )
        self.write_fragment(
            "126.md", "## zakura-alpha\n\n### Fixed\n\n- Final fix.\n"
        )

        writes, _ = changelog.release_plan(self.root, "v1.3.0", "2026-08-28")

        alpha = writes[self.member_changelog("alpha")]
        self.assertIn("## [1.3.0] - 2026-08-28", alpha)
        self.assertNotIn("1.3.0-alpha", alpha)
        self.assertNotIn("1.3.0-rc", alpha)
        # Only pre-releases of 1.3.0 fold in; the earlier stable stays put.
        self.assertIn("## [1.2.0] - 2026-07-20\n\n### Added\n\n- Previous stable", alpha)
        self.assertIn("### Added\n\n- Alpha feature.\n\n### Fixed", alpha)
        self.assertLess(alpha.index("Candidate fix"), alpha.index("Final fix"))
        self.assertLess(alpha.index("## [1.3.0]"), alpha.index("## [1.2.0]"))

    def test_release_rejects_existing_version_with_new_entries(self):
        self.member_changelog("alpha").write_text(
            seeded_changelog(
                "zakura-alpha",
                versions="\n## [1.1.0] - 2026-08-01\n\n### Fixed\n\n- Old fix.\n",
            )
        )
        self.write_fragment(
            "123.md", "## zakura-alpha\n\n### Fixed\n\n- New fix.\n"
        )

        with self.assertRaisesRegex(changelog.ChangelogError, "already exists"):
            changelog.release_plan(self.root, "v1.1.0", "2026-08-28")

    def test_release_rejects_empty_release(self):
        with self.assertRaisesRegex(changelog.ChangelogError, "no pending fragments"):
            changelog.release_plan(self.root, "v1.1.0", "2026-08-28")

    def test_release_check_passes_after_assembly(self):
        fragment = self.write_fragment(
            "123.md", "## zakura-alpha\n\n### Fixed\n\n- Fixed a bug.\n"
        )
        writes, removals = changelog.release_plan(self.root, "v1.1.0", "2026-08-28")
        for path, rendered in writes.items():
            path.write_text(rendered)
        for path in removals:
            path.unlink()
        self.assertEqual(removals, [fragment])

        # Re-running the same release against the assembled state is the
        # --check gate: it must succeed with nothing left to write.
        writes, removals = changelog.release_plan(self.root, "v1.1.0", "2026-08-28")

        self.assertEqual(writes, {})
        self.assertEqual(removals, [])

    def test_release_rejects_invalid_tag(self):
        with self.assertRaisesRegex(changelog.ChangelogError, "invalid release tag"):
            changelog.release_plan(self.root, "1.1.0", "2026-08-28")

    def test_release_rejects_invalid_date(self):
        with self.assertRaisesRegex(changelog.ChangelogError, "invalid changelog date"):
            changelog.release_plan(self.root, "v1.1.0", "2026-8-28")


if __name__ == "__main__":
    unittest.main()
