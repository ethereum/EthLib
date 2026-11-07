"""Report newer releases of the pinned test suites, and the tests of the next execution fork."""

# uv run --no-project --python 3.12 python scripts/check_spec_releases.py

import json
import os
import sys
import tomllib
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCES = "tests/sources.toml"

# The repositories whose releases the parity suites follow.
WATCHED = ("ethereum/consensus-specs", "ethereum/execution-specs")

# The next execution fork, whose rules wait until its tests leave the devnet branches.
# Its tests appear in this directory once an EIP merges into the fork branch.
NEXT_FORK = ("ethereum/execution-specs", "tests/bogota")


@dataclass(frozen=True)
class Release:
    """One release: its tag, its publication time and whether it is a pre-release."""

    tag: str
    published: str
    prerelease: bool


def line_of(tag: str) -> str:
    """The release line of a tag: the part before `@`, such as `tests` or `tests-bogota-devnet`."""
    return tag.partition("@")[0] if "@" in tag else ""


def pins(root: Path = ROOT) -> list[tuple[str, str]]:
    """Each pinned release of a watched repository, as its repository and its tag."""
    config = tomllib.loads((root / SOURCES).read_text(encoding="utf-8"))
    found = [
        (name, entry["release"])
        for name, entry in config.get("repositories", {}).items()
        if name in WATCHED and "release" in entry
    ]
    # A release line followed beside the pin, such as a devnet release, names its own release.
    found += [
        (entry["repository"], entry["release"])
        for entry in config.get("archives", {}).values()
        if entry.get("repository") in WATCHED and "release" in entry
    ]
    return sorted(set(found))


def _get(path: str):
    """The JSON answer of the GitHub API to `path`."""
    request = urllib.request.Request(
        f"https://api.github.com/{path}", headers={"Accept": "application/vnd.github+json"}
    )
    if token := os.environ.get("GITHUB_TOKEN"):
        request.add_header("Authorization", f"Bearer {token}")
    with urllib.request.urlopen(request) as response:
        return json.load(response)


def holds(repository: str, ref: str, directory: str) -> bool:
    """Whether the tree of `ref` in the repository holds `directory`."""
    try:
        _get(f"repos/{repository}/contents/{directory}?ref={urllib.parse.quote(ref)}")
    except urllib.error.HTTPError as error:
        if error.code == 404:
            return False
        raise
    return True


def releases(repository: str) -> list[Release]:
    """The published releases of a repository on GitHub, newest first, at most 100."""
    entries = _get(f"repos/{repository}/releases?per_page=100")
    return [
        Release(entry["tag_name"], entry["published_at"], entry["prerelease"])
        for entry in entries
        if not entry["draft"] and entry["published_at"]
    ]


def newer(pinned: str, published: list[Release]) -> list[Release]:
    """The releases of the pin's line published after the pin, newest first."""
    # A stable pin ignores pre-releases, since its line moves only on stable releases.
    line = line_of(pinned)
    same = [release for release in published if line_of(release.tag) == line]
    pin = next((release for release in same if release.tag == pinned), None)
    if pin is None:
        raise LookupError(f"the pinned release {pinned} is not among the published releases")
    return sorted(
        (
            release
            for release in same
            if release.published > pin.published and (pin.prerelease or not release.prerelease)
        ),
        key=lambda release: release.published,
        reverse=True,
    )


def report(found: dict[tuple[str, str], list[Release]]) -> list[str]:
    """One line for each pin: up to date, or the newer releases of its line."""
    lines = []
    for (repository, pinned), later in sorted(found.items()):
        if later:
            tags = ", ".join(f"{release.tag} ({release.published[:10]})" for release in later)
            lines.append(f"{repository}: {pinned} is pinned; newer: {tags}")
        else:
            lines.append(f"{repository}: {pinned} is the latest release of its line")
    return lines


def next_fork(found: dict[tuple[str, str], list[Release]]) -> list[str]:
    """One line for each place on GitHub that holds the tests of the next fork."""
    # The places are the default branch, and the newest release of the pinned stable line.
    repository, directory = NEXT_FORK
    refs = [_get(f"repos/{repository}")["default_branch"]]
    for (name, pinned), later in found.items():
        if name == repository and not line_of(pinned).startswith("tests-"):
            refs.append(later[0].tag if later else pinned)
    return [
        f"{repository}: {ref} holds {directory}, so the rules of that fork are due"
        for ref in refs
        if holds(repository, ref, directory)
    ]


def main() -> int:
    """Print the state of each pin, and fail when a newer release or the next fork exists."""
    cache: dict[str, list[Release]] = {}
    found = {}
    for repository, pinned in pins():
        published = cache.setdefault(repository, releases(repository))
        found[(repository, pinned)] = newer(pinned, published)
    lines = next_fork(found)
    for line in report(found) + lines:
        print(line)
    return 1 if any(found.values()) or lines else 0


if __name__ == "__main__":
    sys.exit(main())
