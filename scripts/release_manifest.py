"""Check that the release versions agree, and write the release manifest."""

# uv run --no-project --python 3.12 python scripts/release_manifest.py --check
# uv run --no-project --python 3.12 python scripts/release_manifest.py --check --tag v0.2.0
# uv run --no-project --python 3.12 python scripts/release_manifest.py --output manifest.json

from __future__ import annotations

import argparse
import json
import re
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from typing import Any

from soundness_facts import lean_exports  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent

LAKE_VERSION = re.compile(r'^\s*version\s*:=\s*v!"([^"]+)"', re.MULTILINE)
SEMVER = re.compile(r"^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$")


def python_version(root: Path) -> str:
    """The version of the Python package in `pyproject.toml`."""
    with (root / "pyproject.toml").open("rb") as f:
        return tomllib.load(f)["project"]["version"]


def lake_version(root: Path) -> str:
    """The version of the Lake package in `lakefile.lean`."""
    found = LAKE_VERSION.findall((root / "lakefile.lean").read_text())
    if len(found) != 1:
        raise ValueError(f"lakefile.lean declares {len(found)} versions, not 1")
    return found[0]


def version_errors(root: Path, tag: str | None) -> list[str]:
    """Each way in which the two versions and the tag disagree."""
    python = python_version(root)
    try:
        lake = lake_version(root)
    except ValueError as e:
        return [str(e)]
    errors = []
    if not SEMVER.match(python):
        errors.append(f"pyproject.toml version {python!r} is not MAJOR.MINOR.PATCH")
    if python != lake:
        errors.append(f"pyproject.toml has version {python!r}, lakefile.lean has {lake!r}")
    if tag is not None and tag != f"v{python}":
        errors.append(f"tag {tag!r} is not 'v{python}'")
    return errors


def packages(root: Path) -> list[dict[str, str]]:
    """The name, URL and revision of each Lake package in `lake-manifest.json`."""
    manifest = json.loads((root / "lake-manifest.json").read_text())
    return [
        {"name": p["name"], "url": p["url"], "rev": p["rev"]}
        for p in sorted(manifest["packages"], key=lambda p: p["name"])
    ]


def fixture_sources(root: Path) -> dict[str, object]:
    """The pinned sources of the test fixtures in `tests/sources.toml`."""
    with (root / "tests" / "sources.toml").open("rb") as f:
        return tomllib.load(f)


def exports(root: Path) -> list[str]:
    """The sorted C symbols of the Lean exports."""
    return sorted(lean_exports(root))


def manifest(root: Path) -> dict[str, Any]:
    """The release manifest of the checkout at `root`."""
    return {
        "version": python_version(root),
        "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
        "packages": packages(root),
        "fixture_sources": fixture_sources(root),
        "exports": exports(root),
    }


def main(argv: list[str] | None = None) -> int:
    """Check the release version, write the manifest, and return the exit code."""
    parser = argparse.ArgumentParser(
        description="Check the release version and write the manifest."
    )
    parser.add_argument("--check", action="store_true", help="check that the versions agree")
    parser.add_argument("--tag", help="the release tag, which must be v<version>")
    parser.add_argument("--output", type=Path, help="write the manifest to this file")
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    if not args.check and args.output is None:
        parser.error("give --check, --output, or both")
    errors = version_errors(args.root, args.tag)
    for error in errors:
        print(f"release_manifest: {error}", file=sys.stderr)
    if errors:
        return 1
    if args.output is not None:
        args.output.write_text(json.dumps(manifest(args.root), indent=2) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
