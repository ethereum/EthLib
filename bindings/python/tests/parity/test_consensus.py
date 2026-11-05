"""Every case of consensus-spec-tests from Phase 0 to Heze, through the runners of EthLib."""

import pytest

import archives

from consensus.test_operations import HANDLERS as OPERATIONS

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


# Runnable groups that keep no vendored case, each with the reason.
# A mainnet state case is a few megabytes, so the weekly archive run alone reads them; the
# minimal state cases are vendored, and test_ssz_static decodes an empty mainnet state.
# A mainnet operation case holds two states of a few hundred kilobytes, for the same reason.
# The custody cases of Gloas and Heze repeat those of Fulu, and only the fork name in their
# manifest differs, so only the Fulu cases are vendored.
NOT_VENDORED = {f"mainnet/{fork}/ssz_static/BeaconState" for fork in
                ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu",
                 "gloas")} | {
    f"mainnet/{fork}/operations/{handler}" for handler, (_, forks) in OPERATIONS.items()
    for fork in forks} | {
    f"{preset}/{fork}/networking/{handler}" for preset in ("mainnet", "minimal")
    for fork in ("gloas", "heze")
    for handler in ("get_custody_groups", "compute_columns_for_custody_group")}


def test_every_runnable_group_has_vendored_cases() -> None:
    # The run on each change reads vendored cases, so each preset, fork and handler that a
    # runner covers keeps some of its cases under tests/consensus, at their path in the archive.
    vendored = archives.REPO / "tests" / "consensus"
    groups = {"/".join(case.path.split("/")[1:5]) for case in harness.runnable(CASES)}
    # An exception for a group that no longer runs is stale.
    assert NOT_VENDORED <= groups
    missing = sorted(group for group in groups - NOT_VENDORED
                     if not any(vendored.glob(f"*/{group}/*/*")))
    assert missing == []


def test_disagreements() -> None:
    harness.check_disagreements(CASES, DISAGREEMENTS)
