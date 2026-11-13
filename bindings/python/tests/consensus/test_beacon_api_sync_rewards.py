"""The Beacon API sync committee rewards, on the pinned sync aggregate operations vectors."""

from pathlib import Path

import pytest

from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS
from .test_operations import FILES

# The proposer earns 8/56 of the reward of each seat that signed: the Altair incentive weights.
PROPOSER_WEIGHT = 8
WEIGHT_DENOMINATOR = 64


def _cases() -> list:
    """Every vendored sync aggregate case that the block accepts, as its fork and directory."""
    return [
        pytest.param(post.parent.relative_to(FILES).parts[1], post.parent, id=str(post.parent))
        for post in sorted(FILES.glob("minimal/*/operations/sync_aggregate/pyspec_tests/*/post*"))
    ]


def _read(path: Path) -> bytes:
    return snappy.decompress(path.read_bytes())


def _seats(fork: str, pre: bytes, aggregate: bytes) -> list[tuple[int, bool]]:
    """Each seat of the committee: the first validator with its key, and whether it signed."""
    state = consensus.api_json("minimal", FORKS[fork], "BeaconState", pre)
    keys = [validator["pubkey"] for validator in state["validators"]]
    bits = bytes.fromhex(
        consensus.api_json("minimal", FORKS[fork], "SyncAggregate", aggregate)[
            "sync_committee_bits"
        ][2:]
    )
    return [
        (keys.index(pubkey), bool(bits[seat // 8] >> (seat % 8) & 1))
        for seat, pubkey in enumerate(state["current_sync_committee"]["pubkeys"])
    ]


def _balances(fork: str, state: bytes) -> list[int]:
    return [
        int(balance)
        for balance in consensus.api_json("minimal", FORKS[fork], "BeaconState", state)["balances"]
    ]


@pytest.mark.parametrize("fork, case", _cases())
def test_rewards_match_balances(fork, case):
    pre = _read(case / "pre.ssz_snappy")
    aggregate = _read(case / "sync_aggregate.ssz_snappy")
    entries = consensus.api_sync_committee_rewards("minimal", FORKS[fork], pre, aggregate)["data"]
    seats = _seats(fork, pre, aggregate)
    # An empty request names every member once, in increasing order of index.
    assert [int(entry["validator_index"]) for entry in entries] == sorted({i for i, _ in seats})
    net = {index: 0 for index, _ in seats}
    for index, signed in seats:
        net[index] += 1 if signed else -1
    # Every member earns one participant reward per signed seat and pays it per other seat.
    participant = next(
        abs(int(e["reward"])) // abs(net[int(e["validator_index"])])
        for e in entries
        if net[int(e["validator_index"])]
    )
    assert participant > 0
    for entry in entries:
        assert int(entry["reward"]) == participant * net[int(entry["validator_index"])]
    before = _balances(fork, pre)
    after = _balances(fork, _read(case / "post.ssz_snappy"))
    share = participant * PROPOSER_WEIGHT // (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT)
    signatures = sum(signed for _, signed in seats)
    proposers = 0
    for entry in entries:
        index = int(entry["validator_index"])
        moved = after[index] - before[index]
        if consensus.is_proposer("minimal", FORKS[fork], pre, index):
            # The proposer also earns a share of the reward of each seat that signed.
            proposers += 1
            assert moved == int(entry["reward"]) + share * signatures
        else:
            # No balance of these cases is low enough for a penalty to stop at zero.
            assert before[index] >= len(seats) * participant
            assert moved == int(entry["reward"]), index
    # The cases are named for a proposer that sits in the committee.
    assert proposers == 1


def test_named_members():
    fork, case = _cases()[0].values
    pre = _read(case / "pre.ssz_snappy")
    aggregate = _read(case / "sync_aggregate.ssz_snappy")
    everyone = consensus.api_sync_committee_rewards("minimal", FORKS[fork], pre, aggregate)["data"]
    first, second = everyone[0]["validator_index"], everyone[1]["validator_index"]
    state = consensus.api_json("minimal", FORKS[fork], "BeaconState", pre)
    pubkey = state["validators"][int(second)]["pubkey"]
    outsider = next(
        str(index)
        for index in range(len(state["validators"]))
        if str(index) not in {entry["validator_index"] for entry in everyone}
    )
    # An outsider or an index past the registry gives no entry; a repeat gives one.
    # The entries go by index.
    past = str(len(state["validators"]))
    named = consensus.api_sync_committee_rewards(
        "minimal", FORKS[fork], pre, aggregate, ids=[pubkey, outsider, first, past, first]
    )["data"]
    assert named == [everyone[0], everyone[1]]


def test_invalid_identifier():
    fork, case = _cases()[0].values
    pre = _read(case / "pre.ssz_snappy")
    aggregate = _read(case / "sync_aggregate.ssz_snappy")
    with raises(consensus.ConsensusError, "Invalid validator ID: nobody") as info:
        consensus.api_sync_committee_rewards("minimal", FORKS[fork], pre, aggregate, ids=["nobody"])
    assert info.value.code == 400


def test_no_sync_aggregate_before_altair():
    _, case = _cases()[0].values
    aggregate = _read(case / "sync_aggregate.ssz_snappy")
    pre = _read(next(FILES.glob("minimal/phase0/operations/attestation/pyspec_tests/*/pre*")))
    message = "Invalid request to retrieve sync committee rewards info"
    with raises(consensus.ConsensusError, message) as info:
        consensus.api_sync_committee_rewards("minimal", "phase0", pre, aggregate)
    assert info.value.code == 400
