"""The cases of the execution-spec-tests devnets that the pinned release lacks."""

from pathlib import Path

import pytest

import archives

from . import catalogue, harness

CASES = (
    {suite: catalogue.devnet_cases(suite) for suite in catalogue.DEVNETS} if archives.CACHE else {}
)


def unpack(suite: str) -> Path:
    """The archive of a devnet, with the files of its runnable cases unpacked."""
    # Most cases of a devnet run in the pinned release, so whole directories would waste the disk.
    # A case of the format blockchain_test_engine_x also reads the shared states of its format.
    runnable = harness.runnable(CASES[suite])
    paths = {case.path for case in runnable} | {
        "/".join(case.path.split("/")[:2]) + "/pre_alloc"
        for case in runnable
        if case.group == "blockchain_test_engine_x"
    }
    return archives.unpack(catalogue.DEVNETS[suite], *sorted(paths)) if paths else archives.CACHE


ROOTS = {suite: unpack(suite) for suite in CASES}
DISAGREEMENTS = {suite: harness.disagreements(suite) for suite in catalogue.DEVNETS}

pytestmark = pytest.mark.archive


@pytest.mark.parametrize(
    "case",
    [case for cases in CASES.values() for case in harness.runnable(cases)],
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
