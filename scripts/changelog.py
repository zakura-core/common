#!/usr/bin/env python3
"""Validate and assemble per-crate changelog fragments.

Adapted from zakura-core/zakura's scripts/changelog.py for a workspace that
maintains one CHANGELOG.md per published crate. Fragments live in
docs/changelog/unreleased/<PR-number>.md and scope their entries to crates:

    ## zakura-orchard

    ### Fixed

    - Fixed the consumer-visible behavior
      ([#123](https://github.com/zakura-core/common/pull/123)).

Release assembly folds every fragment's entries into the matching crate's
CHANGELOG.md under a new version section and deletes the consumed fragments.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tomllib
from collections import defaultdict
from dataclasses import dataclass
from datetime import date
from pathlib import Path


FRAGMENT_DIRECTORY = "docs/changelog/unreleased"
NO_CHANGELOG_MARKER = "<!-- changelog: none -->"
FORK_SEED_HEADING = "## Record of Fork"
STANDARD_CATEGORIES = (
    "Added",
    "Changed",
    "Deprecated",
    "Removed",
    "Fixed",
    "Security",
)
CRATE_HEADING = re.compile(r"^## (\S+)\s*$")
CATEGORY_HEADING = re.compile(r"^### (.+?)\s*$")
VERSION_HEADING = re.compile(
    r"^## \[([0-9]+\.[0-9]+\.[0-9]+(?:-[0-9A-Za-z.-]+)?)\]"
    r" - ([0-9]{4}-[0-9]{2}-[0-9]{2})$",
    re.MULTILINE,
)
RELEASE_TAG = re.compile(r"^v([0-9]+\.[0-9]+\.[0-9]+(?:-[0-9A-Za-z.-]+)?)$")


class ChangelogError(Exception):
    """A changelog fragment or release invariant is invalid."""


@dataclass(frozen=True)
class Fragment:
    path: Path
    # crate package name -> category -> rendered list body
    entries: dict[str, dict[str, str]]


def workspace_changelogs(repo_root: Path) -> dict[str, Path]:
    """Map each member's package name to its CHANGELOG.md path."""
    manifest = repo_root / "Cargo.toml"
    with manifest.open("rb") as handle:
        workspace = tomllib.load(handle)
    members = workspace.get("workspace", {}).get("members", [])
    if not members:
        raise ChangelogError(f"{manifest}: no workspace members found")

    changelogs: dict[str, Path] = {}
    for member in members:
        member_manifest = repo_root / member / "Cargo.toml"
        with member_manifest.open("rb") as handle:
            package = tomllib.load(handle).get("package", {})
        name = package.get("name")
        if not isinstance(name, str):
            raise ChangelogError(f"{member_manifest}: missing package name")
        changelogs[name] = repo_root / member / "CHANGELOG.md"
    return changelogs


def fragment_paths(repo_root: Path) -> list[Path]:
    directory = repo_root / FRAGMENT_DIRECTORY
    if not directory.is_dir():
        raise ChangelogError(f"missing fragment directory: {directory}")

    invalid = sorted(
        path.name
        for path in directory.iterdir()
        if path.name != "README.md"
        and (not path.is_file() or path.is_symlink() or path.suffix != ".md")
    )
    if invalid:
        raise ChangelogError(
            "changelog fragments must be Markdown files: " + ", ".join(invalid)
        )

    return sorted(path for path in directory.glob("*.md") if path.name != "README.md")


def parse_fragment(path: Path, crate_names: set[str]) -> Fragment:
    if not path.stem.isdigit():
        raise ChangelogError(
            f"{path}: fragment name must be a pull request number, for example 123.md"
        )

    text = path.read_text()
    if NO_CHANGELOG_MARKER in text:
        if "## " in text:
            raise ChangelogError(
                f"{path}: a no-changelog fragment cannot also contain entries"
            )
        reason = text.replace(NO_CHANGELOG_MARKER, "")
        reason = re.sub(r"<!--.*?-->", "", reason, flags=re.DOTALL).strip()
        if not reason:
            raise ChangelogError(f"{path}: explain why no changelog entry is required")
        return Fragment(path, {})

    entries: dict[str, dict[str, str]] = {}
    crate: str | None = None
    category: str | None = None
    body: list[str] = []

    def store_body() -> None:
        nonlocal body
        if category is None:
            return
        rendered = "\n".join(body).strip()
        if not rendered:
            raise ChangelogError(f"{path}: {crate} / {category} is empty")
        if not rendered.startswith("- "):
            raise ChangelogError(
                f"{path}: {crate} / {category} must start with a Markdown list item"
            )
        entries[crate][category] = rendered
        body = []

    for line in text.splitlines():
        crate_match = CRATE_HEADING.match(line)
        category_match = CATEGORY_HEADING.match(line)
        if crate_match:
            store_body()
            category = None
            crate = crate_match.group(1).strip("`")
            if crate not in crate_names:
                raise ChangelogError(
                    f"{path}: unknown crate {crate!r}; expected a workspace "
                    "package name such as zakura-orchard"
                )
            if crate in entries:
                raise ChangelogError(f"{path}: duplicate {crate} section")
            entries[crate] = {}
        elif category_match:
            store_body()
            if crate is None:
                raise ChangelogError(
                    f"{path}: category sections must be inside a crate section"
                )
            category = category_match.group(1)
            if category not in STANDARD_CATEGORIES:
                valid = ", ".join(STANDARD_CATEGORIES)
                raise ChangelogError(
                    f"{path}: invalid category {category!r}; expected one of: {valid}"
                )
            if category in entries[crate]:
                raise ChangelogError(
                    f"{path}: duplicate {crate} / {category} section"
                )
        elif line.startswith("#"):
            raise ChangelogError(f"{path}: malformed heading: {line}")
        elif category is not None:
            body.append(line)
        elif line.strip() and not line.lstrip().startswith("<!--"):
            raise ChangelogError(
                f"{path}: content must be inside a crate's category section"
            )

    store_body()
    if not entries:
        raise ChangelogError(
            f"{path}: add a changelog entry or use {NO_CHANGELOG_MARKER}"
        )
    for crate_name, categories in entries.items():
        if not categories:
            raise ChangelogError(f"{path}: {crate_name} section has no entries")
    return Fragment(path, entries)


def load_fragments(repo_root: Path) -> list[Fragment]:
    crate_names = set(workspace_changelogs(repo_root))
    return [parse_fragment(path, crate_names) for path in fragment_paths(repo_root)]


def check_seeds(repo_root: Path) -> None:
    """Every member changelog keeps its provenance seed and Unreleased section."""
    for name, path in sorted(workspace_changelogs(repo_root).items()):
        try:
            text = path.read_text()
        except OSError as error:
            raise ChangelogError(f"{name}: cannot read {path}: {error}") from error
        if not re.search(r"^## \[Unreleased\]$", text, re.MULTILINE):
            raise ChangelogError(f"{path}: missing ## [Unreleased] section")
        if not re.search(rf"^{re.escape(FORK_SEED_HEADING)}$", text, re.MULTILINE):
            raise ChangelogError(
                f"{path}: missing '{FORK_SEED_HEADING}' provenance section"
            )


def split_unreleased(text: str, path: Path) -> tuple[str, str, str]:
    marker = "## [Unreleased]"
    marker_start = text.find(marker)
    if marker_start < 0:
        raise ChangelogError(f"{path}: missing {marker}")
    marker_end = marker_start + len(marker)
    if text[marker_end : marker_end + 1] not in ("", "\n"):
        raise ChangelogError(f"{path}: malformed {marker} heading")

    next_heading = re.search(r"^## ", text[marker_end + 1 :], re.MULTILINE)
    if next_heading:
        suffix_start = marker_end + 1 + next_heading.start()
    else:
        suffix_start = len(text)

    prefix = text[:marker_end]
    body = text[marker_end:suffix_start].strip()
    suffix = text[suffix_start:].lstrip("\n")
    return prefix, body, suffix


def parse_category_body(body: str, path: Path, section: str) -> dict[str, str]:
    if not body:
        return {}

    categories: dict[str, str] = {}
    category: str | None = None
    lines: list[str] = []

    def store_body() -> None:
        nonlocal lines
        if category is None:
            return
        rendered = "\n".join(lines).strip()
        if not rendered:
            raise ChangelogError(f"{path}: empty {section} / {category} section")
        categories[category] = rendered
        lines = []

    for line in body.splitlines():
        match = re.match(r"^### (.+?)\s*$", line)
        if match:
            store_body()
            category = match.group(1)
            if category not in STANDARD_CATEGORIES:
                raise ChangelogError(f"{path}: invalid {section} category {category!r}")
            if category in categories:
                raise ChangelogError(
                    f"{path}: duplicate {section} / {category} section"
                )
        elif line.startswith("## ") or line.startswith("### "):
            raise ChangelogError(f"{path}: malformed {section} heading: {line}")
        elif category is None:
            if line.strip():
                raise ChangelogError(
                    f"{path}: {section} content must be in category sections"
                )
        else:
            lines.append(line)

    store_body()
    return categories


def promote_prereleases(
    suffix: str, stable_version: str, path: Path
) -> tuple[dict[str, str], str]:
    """Collapse X.Y.Z-<pre-release> sections into entries for the stable X.Y.Z release.

    Alpha, beta, and release-candidate sections are all pre-releases of the
    stable version: their entries fold into the stable section, oldest first,
    and the pre-release sections are removed.
    """
    matches = list(VERSION_HEADING.finditer(suffix))
    candidate_sections: list[dict[str, str]] = []
    kept: list[str] = []
    cursor = 0
    prerelease_prefix = f"{stable_version}-"

    for match in matches:
        version = match.group(1)
        if version.startswith(prerelease_prefix):
            # A section ends at the next ## heading of any kind: the next
            # version section or the trailing Record of Fork section.
            next_heading = re.search(r"^## ", suffix[match.end() :], re.MULTILINE)
            section_end = (
                match.end() + next_heading.start() if next_heading else len(suffix)
            )
            body = suffix[match.end() : section_end].strip()
            candidate_sections.append(
                parse_category_body(body, path, f"release {version}")
            )
            kept.append(suffix[cursor : match.start()])
            cursor = section_end

    kept.append(suffix[cursor:])

    additions: dict[str, list[str]] = defaultdict(list)
    for categories in reversed(candidate_sections):
        for category, body in categories.items():
            additions[category].append(body)

    promoted = {category: "\n".join(bodies) for category, bodies in additions.items()}
    return promoted, "".join(kept).lstrip("\n")


def render_categories(categories: dict[str, str]) -> str:
    return "\n\n".join(
        f"### {category}\n\n{categories[category]}"
        for category in STANDARD_CATEGORIES
        if category in categories
    )


def merge_entries(
    current: dict[str, str], additions: dict[str, list[str]]
) -> dict[str, str]:
    merged = dict(current)
    for category, bodies in additions.items():
        parts = []
        if category in merged:
            parts.append(merged[category])
        parts.extend(bodies)
        merged[category] = "\n".join(parts)
    return merged


def render_unreleased(prefix: str, body: str, suffix: str) -> str:
    parts = [prefix, ""]
    if body:
        parts.extend([body, ""])
    if suffix:
        parts.append(suffix.rstrip("\n"))
    return "\n".join(parts) + "\n"


def render_release(
    prefix: str, body: str, suffix: str, version: str, release_date: str
) -> str:
    parts = [prefix, "", f"## [{version}] - {release_date}", "", body]
    if suffix:
        parts.extend(["", suffix.rstrip("\n")])
    return "\n".join(parts) + "\n"


def release_plan(
    repo_root: Path, release_tag: str, release_date: str
) -> tuple[dict[Path, str], list[Path]]:
    tag_match = RELEASE_TAG.match(release_tag)
    if not tag_match:
        raise ChangelogError(
            f"invalid release tag {release_tag!r}; expected v<major>.<minor>.<patch>"
        )
    try:
        parsed_date = date.fromisoformat(release_date)
    except ValueError as error:
        raise ChangelogError(
            f"invalid changelog date {release_date!r}; expected YYYY-MM-DD"
        ) from error
    if parsed_date.isoformat() != release_date:
        raise ChangelogError(
            f"invalid changelog date {release_date!r}; expected YYYY-MM-DD"
        )
    version = tag_match.group(1)
    stable = "-" not in version

    check_seeds(repo_root)
    fragments = load_fragments(repo_root)
    changelogs = workspace_changelogs(repo_root)

    # crate -> category -> ordered fragment bodies
    fragment_entries: dict[str, dict[str, list[str]]] = defaultdict(
        lambda: defaultdict(list)
    )
    for fragment in fragments:
        for crate, categories in fragment.entries.items():
            for category, body in categories.items():
                fragment_entries[crate][category].append(body)

    writes: dict[Path, str] = {}
    assembled_any = False
    already_released = False

    for crate, path in sorted(changelogs.items()):
        original = path.read_text()
        prefix, unreleased, suffix = split_unreleased(original, path)
        current = parse_category_body(unreleased, path, "Unreleased")

        promoted: dict[str, str] = {}
        if stable:
            promoted, suffix = promote_prereleases(suffix, version, path)

        additions: dict[str, list[str]] = defaultdict(list)
        for category, body in current.items():
            additions[category].append(body)
        for category, bodies in fragment_entries.get(crate, {}).items():
            additions[category].extend(bodies)

        merged = merge_entries(promoted, additions)
        body = render_categories(merged)

        existing_versions = {
            match.group(1) for match in VERSION_HEADING.finditer(suffix)
        }
        if version in existing_versions:
            if body:
                raise ChangelogError(
                    f"{path}: release {version} already exists but new entries "
                    "remain; bump the release version first"
                )
            already_released = True
            continue
        if not body:
            # Nothing to record for this crate in this release.
            continue

        assembled_any = True
        rendered = render_release(prefix, body, suffix, version, release_date)
        if rendered != original:
            writes[path] = rendered

    if not assembled_any and not already_released and not fragments:
        raise ChangelogError(
            f"release {version}: no pending fragments and no unreleased entries"
        )

    return writes, [fragment.path for fragment in fragments]


def run_git(repo_root: Path, arguments: list[str]) -> str:
    result = subprocess.run(
        ["git", *arguments],
        cwd=repo_root,
        check=False,
        text=True,
        capture_output=True,
    )
    if result.returncode:
        raise ChangelogError(result.stderr.strip() or "git command failed")
    return result.stdout


def check_pull_request(
    repo_root: Path,
    base: str,
    head: str,
    pull_request: str,
    release_pr: bool,
    allow_missing: bool,
) -> None:
    check_seeds(repo_root)
    load_fragments(repo_root)
    existing = {path.name for path in fragment_paths(repo_root)}
    if release_pr:
        if existing:
            raise ChangelogError(
                "release PRs must consume every fragment; remaining: "
                + ", ".join(sorted(existing))
            )
        return

    # Compare from the merge base so fragments added to a moving base branch do
    # not look like deletions made by a stale pull request branch.
    diff_lines = run_git(
        repo_root,
        ["diff", "--name-status", "--find-renames=100%", f"{base}...{head}"],
    ).splitlines()
    diff_entries = [
        (line.split("\t")[0], line.split("\t")[-1]) for line in diff_lines
    ]
    changed_paths = [path for _, path in diff_entries]
    # An exact rename keeps a fragment's content intact, so repository moves
    # are not fragment changes owned by this pull request.
    changed = [
        path
        for status, path in diff_entries
        if not status.startswith("R")
        and path.startswith(f"{FRAGMENT_DIRECTORY}/")
        and path != f"{FRAGMENT_DIRECTORY}/README.md"
    ]
    expected = f"{FRAGMENT_DIRECTORY}/{pull_request}.md"
    unexpected = [path for path in changed if path != expected]
    if unexpected:
        raise ChangelogError(
            "each PR owns one fragment; unexpected fragment changes: "
            + ", ".join(unexpected)
        )
    changes_rust = any(
        Path(path).suffix == ".rs" or Path(path).name == "Cargo.toml"
        for path in changed_paths
    )
    if expected not in changed and not allow_missing and changes_rust:
        raise ChangelogError(
            f"add {expected}; use {NO_CHANGELOG_MARKER} for an internal-only PR"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser(
        "check", help="validate all pending fragments and changelog seeds"
    )

    check_pr = subparsers.add_parser(
        "check-pr", help="validate the fragment owned by a pull request"
    )
    check_pr.add_argument("--base", required=True)
    check_pr.add_argument("--head", required=True)
    check_pr.add_argument("--pr", required=True)
    check_pr.add_argument("--release-pr", action="store_true")
    check_pr.add_argument("--allow-missing", action="store_true")

    release = subparsers.add_parser(
        "release", help="assemble fragments into the per-crate changelogs"
    )
    release.add_argument("release_tag")
    release.add_argument("--date", default=date.today().isoformat())
    release.add_argument(
        "--check",
        action="store_true",
        help="fail if release assembly would change tracked files",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = Path(__file__).resolve().parent.parent
    try:
        if args.command == "check":
            check_seeds(repo_root)
            fragments = load_fragments(repo_root)
            print(f"validated {len(fragments)} changelog fragment(s)")
        elif args.command == "check-pr":
            check_pull_request(
                repo_root,
                args.base,
                args.head,
                args.pr,
                args.release_pr,
                args.allow_missing,
            )
            print("pull request changelog fragment is valid")
        elif args.command == "release":
            writes, removals = release_plan(repo_root, args.release_tag, args.date)
            if args.check:
                if writes or removals:
                    changed = [str(path.relative_to(repo_root)) for path in writes]
                    changed.extend(
                        str(path.relative_to(repo_root)) for path in removals
                    )
                    raise ChangelogError(
                        "release changelogs are not assembled; run "
                        f"./scripts/changelog.py release {args.release_tag}. "
                        "Pending paths: " + ", ".join(changed)
                    )
                print("release changelogs are assembled")
            else:
                for path, rendered in writes.items():
                    path.write_text(rendered)
                for path in removals:
                    path.unlink()
                print(
                    f"updated {len(writes)} changelog(s) and consumed "
                    f"{len(removals)} fragment(s)"
                )
        return 0
    except (ChangelogError, OSError) as error:
        print(f"changelog error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
