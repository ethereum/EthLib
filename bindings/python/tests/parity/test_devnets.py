"""The cases of the execution-spec-tests devnets that the pinned release lacks."""

import pytest

import archives

from . import catalogue, harness

CASES = (
    {suite: catalogue.devnet_cases(suite) for suite in catalogue.DEVNETS} if archives.CACHE else {}
)

# Most cases of a devnet run in the pinned release, so only the files of the others are unpacked.
ROOTS = {suite: harness.unpack_read(catalogue.DEVNETS[suite], CASES[suite]) for suite in CASES}
DISAGREEMENTS = {suite: archives.disagreements(suite) for suite in catalogue.DEVNETS}

pytestmark = pytest.mark.archive


@pytest.mark.parametrize(
    "case",
    [case for cases in CASES.values() for case in harness.in_shard(cases)],
    ids=lambda case: f"{case.suite}:{case.id}",
)
def test_case(case, request, record_property) -> None:
    harness.run(ROOTS[case.suite], case, DISAGREEMENTS[case.suite], request, record_property)


@pytest.mark.parametrize("suite", catalogue.DEVNETS)
def test_catalogue(suite, record_property) -> None:
    record_property("parity catalogue", harness.catalogue(CASES[suite]))


@pytest.mark.parametrize("suite", catalogue.DEVNETS)
def test_every_group_has_a_runner_or_a_plan(suite) -> None:
    harness.check_groups(CASES[suite])


@pytest.mark.parametrize("suite", catalogue.DEVNETS)
def test_every_network_is_placed(suite) -> None:
    # A network that is not on the timeline is new upstream.
    timeline = catalogue.EXECUTION_FORKS + catalogue.BOGOTA_NETWORKS
    networks = {entry["fork"] for entry in catalogue.execution_index(catalogue.DEVNETS[suite])}
    assert sorted(networks - set(timeline)) == []


@pytest.mark.parametrize("suite", catalogue.DEVNETS)
def test_disagreements(suite) -> None:
    harness.check_disagreements(CASES[suite], DISAGREEMENTS[suite])
