"""The release archives of `tests/sources.toml`, and the cases on which EthLib disagrees."""

import importlib.util
import sys
from collections.abc import Callable, Sequence
from importlib.machinery import ModuleSpec, SourceFileLoader
from pathlib import Path
from typing import cast

# The test of each wheel runs the suites on Python 3.10 too.
if sys.version_info >= (3, 11):
    import tomllib
else:
    import tomli as tomllib

REPO = Path(__file__).resolve().parents[3]

# The fetcher, loaded by path: `scripts` is not a package.
# A path that ends in .py always gets a spec, with the source file loader.
_spec = cast(
    ModuleSpec,
    importlib.util.spec_from_file_location(
        "fetch_archives", REPO / "scripts" / "fetch_archives.py"
    ),
)
fetch_archives = importlib.util.module_from_spec(_spec)
cast(SourceFileLoader, _spec.loader).exec_module(fetch_archives)

# The cache, or `None` when the archives are not to be read.
CACHE = fetch_archives.cache_from_environment()

# The cases of the official suites on which EthLib knowingly disagrees.
DISAGREEMENTS_FILE = REPO / "tests" / "parity" / "disagreements.toml"


def disagreements(suite: str) -> dict[tuple[str, str | None], dict]:
    """The listed disagreements of a suite, by case and group.

    An entry without a group holds for every group of its case.
    """
    entries = tomllib.loads(DISAGREEMENTS_FILE.read_text()).get("disagreement", [])
    return {
        (entry["case"], entry.get("group")): entry for entry in entries if entry["suite"] == suite
    }


def unpack(name: str, *paths: str) -> Path:
    """The directory of the archive `name`, with every member under `paths` unpacked."""
    return fetch_archives.unpack(fetch_archives.load(REPO)[name], CACHE, list(paths))


def download(name: str) -> Path:
    """The file of the archive `name`, for a pinned file that is used as it is, not unpacked."""
    return fetch_archives.download(fetch_archives.load(REPO)[name], CACHE)


def parametrize(argnames: str | Sequence[str], cases: Callable[[], list]):
    """Parametrize a test with the cases of an archive, built when pytest collects the test."""
    # A module that imports this test module for its tables then reads no archive.

    def mark(test):
        test.archive_parameters = (argnames, cases)
        return test

    return mark
