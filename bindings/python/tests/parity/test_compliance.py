"""Every fork choice compliance case of consensus-specs, through the fork choice of EthLib."""

from functools import cache
from pathlib import Path

import pytest

import archives

from . import catalogue, harness

SUITE = "fork-choice-compliance"
CASES = catalogue.compliance_cases() if archives.CACHE else []
SHARD = harness.in_shard(CASES)
DISAGREEMENTS = archives.disagreements(SUITE)

pytestmark = pytest.mark.archive(catalogue.COMPLIANCE)


# The archive, with the cases of this shard unpacked on first use.
# So the checks of the catalogue run without unpacking a case.
@cache
def root() -> Path:
    return harness.unpack(catalogue.COMPLIANCE, SHARD, 7)


@pytest.mark.parametrize(
    "case", SHARD, ids=lambda case: harness.case_id(case.suite, case.id, case.group)
)
def test_case(case, request, record_property) -> None:
    harness.run(root(), case, DISAGREEMENTS, request, record_property)


def test_catalogue(record_property) -> None:
    record_property("parity catalogue", harness.catalogue(CASES))


def test_every_group_has_a_runner_or_a_plan() -> None:
    harness.check_groups(CASES)


def test_every_case_runs() -> None:
    # Each suite of the archive is a fork choice suite that EthLib runs at each of its forks.
    assert harness.runnable(CASES) == CASES


def test_disagreements() -> None:
    harness.check_disagreements(CASES, DISAGREEMENTS)
