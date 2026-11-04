"""Every case of consensus-spec-tests from Phase 0 to Fulu, through the runners of EthLib."""

import pytest

import archives

from . import catalogue, harness

SUITE = "consensus-spec-tests"
CASES = catalogue.consensus_cases() if archives.CACHE else []
ROOTS = {preset: harness.unpack(name, [c for c in CASES if c.preset == preset], 5)
         for preset, name in catalogue.CONSENSUS.items()} if archives.CACHE else {}
DISAGREEMENTS = harness.disagreements(SUITE)

pytestmark = pytest.mark.archive(catalogue.CONSENSUS["mainnet"])


@pytest.mark.parametrize("case", harness.runnable(CASES), ids=lambda case: case.id)
def test_case(case, request, record_property) -> None:
    harness.run(ROOTS[case.preset], case, DISAGREEMENTS, request, record_property)


def test_catalogue(record_property) -> None:
    record_property("parity catalogue", harness.catalogue(CASES))


def test_every_group_has_a_runner_or_a_plan() -> None:
    harness.check_groups(CASES)


def test_disagreements() -> None:
    harness.check_disagreements(CASES, DISAGREEMENTS)
