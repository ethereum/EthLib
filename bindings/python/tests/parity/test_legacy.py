"""Every legacy blockchain test from Frontier to London, through the runners of EthLib."""

from pathlib import Path
from typing import cast

import pytest

import archives

from . import catalogue, harness

SUITE = "legacytests"
# None without the archives, and then the mark `archive` skips every test of this file.
ROOT = (
    (
        archives.unpack(
            catalogue.LEGACY,
            *(f"{catalogue.LEGACY_ROOT}/{d}" for d in catalogue.LEGACY_DIRECTORIES),
        )
        / catalogue.LEGACY_ROOT
    )
    if archives.CACHE
    else None
)
CASES = catalogue.legacy_cases(ROOT) if ROOT else []
DISAGREEMENTS = archives.disagreements(SUITE)

# The cases that the run on each change reads, at their path in the archive.
VENDORED = archives.REPO / "tests" / "execution" / "legacytests"

pytestmark = pytest.mark.archive(catalogue.LEGACY)


@pytest.mark.parametrize(
    "case", harness.in_shard(CASES), ids=lambda case: f"{case.group}:{case.id}"
)
def test_case(case, request, record_property) -> None:
    harness.run(cast(Path, ROOT), case, DISAGREEMENTS, request, record_property)


def test_catalogue(record_property) -> None:
    record_property("parity catalogue", harness.catalogue(CASES))


def test_every_group_has_a_runner_or_a_plan() -> None:
    harness.check_groups(CASES)


def test_every_network_is_placed() -> None:
    # A network that is neither in scope nor listed as out of scope is new upstream.
    new = catalogue.legacy_networks(cast(Path, ROOT)) - set(catalogue.LEGACY_FORKS)
    assert sorted(new - catalogue.LEGACY_OUT_OF_SCOPE) == []


def test_vendored_files_are_those_of_the_archive() -> None:
    vendored = sorted(p for p in VENDORED.rglob("*.json"))
    assert vendored
    root = cast(Path, ROOT)
    for path in vendored:
        assert path.read_bytes() == (root / path.relative_to(VENDORED)).read_bytes(), path


def test_disagreements() -> None:
    harness.check_disagreements(CASES, DISAGREEMENTS)
