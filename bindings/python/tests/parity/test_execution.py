"""Every case of execution-spec-tests in scope, through the runners of EthLib."""

from pathlib import Path
from typing import cast

import pytest

import archives

from . import catalogue, harness

SUITE = "execution-spec-tests"
CASES = catalogue.execution_cases() if archives.CACHE else []
# None without the archives, and then the mark `archive` skips every test of this file.
ROOT = harness.unpack(catalogue.EXECUTION, CASES, 2) if archives.CACHE else None
DISAGREEMENTS = harness.disagreements(SUITE)

pytestmark = pytest.mark.archive(catalogue.EXECUTION)


@pytest.mark.parametrize("case", harness.in_shard(CASES), ids=lambda case: case.id)
def test_case(case, request, record_property) -> None:
    harness.run(cast(Path, ROOT), case, DISAGREEMENTS, request, record_property)


def test_catalogue(record_property) -> None:
    record_property("parity catalogue", harness.catalogue(CASES))


def test_every_group_has_a_runner_or_a_plan() -> None:
    harness.check_groups(CASES)


def test_every_network_is_placed() -> None:
    # A network that is not in scope is new upstream.
    networks = {entry["fork"] for entry in catalogue.execution_index()}
    assert sorted(networks - set(catalogue.EXECUTION_FORKS)) == []


def test_disagreements() -> None:
    harness.check_disagreements(CASES, DISAGREEMENTS)
