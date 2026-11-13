"""The Beacon API duty answers, on the pinned minimal states moved to epoch 20."""

import copy
from typing import Any

import pytest

from ethlib import consensus
from raising import raises

from .containers import FORKS
from .test_beacon_api_committees import (
    EPOCH,
    GLOAS,
    SLOTS_PER_EPOCH,
    _active,
    _committees,
    _json,
    _state,
)

# The length of the buffer of block roots in the minimal preset.
SLOTS_PER_HISTORICAL_ROOT = 64

GENESIS = bytes(range(32))


def _duties(fork: str, kind: str, epoch: int, **options: Any) -> dict[str, Any]:
    config = GLOAS if fork == "gloas" else None
    return consensus.api_duties(
        "minimal", FORKS[fork], _state(fork), kind, epoch, GENESIS, config=config, **options
    )


def _pubkey(fork: str, index: int) -> str:
    return _json(fork)["validators"][index]["pubkey"]


def _root_at(fork: str, slot: int) -> str:
    """The block root at a slot, read from the buffer of the state."""
    return _json(fork)["block_roots"][slot % SLOTS_PER_HISTORICAL_ROOT]


@pytest.mark.parametrize("fork", ["phase0", "electra", "gloas"])
@pytest.mark.parametrize("epoch", [EPOCH, EPOCH + 1])
def test_attester_duties_match_the_committees(fork: str, epoch: int) -> None:
    active = _active(fork, epoch)
    requested = [active[0], active[-1], active[len(active) // 2]]
    committees = _committees(fork, epoch=epoch)
    per_slot = sum(1 for c in committees if c["slot"] == committees[0]["slot"])
    expected = []
    for index in requested:
        (committee,) = [c for c in committees if str(index) in c["validators"]]
        expected.append(
            {
                "pubkey": _pubkey(fork, index),
                "validator_index": str(index),
                "committee_index": committee["index"],
                "committee_length": str(len(committee["validators"])),
                "committees_at_slot": str(per_slot),
                "validator_committee_index": str(committee["validators"].index(str(index))),
                "slot": committee["slot"],
            }
        )
    answer = _duties(fork, "attester", epoch, indices=requested)
    # The duties of the epoch depend on the block before the start of the epoch before it.
    root = _root_at(fork, (epoch - 1) * SLOTS_PER_EPOCH - 1)
    assert answer == {"dependent_root": root, "data": expected}


def test_attester_duties_skip_an_inactive_validator() -> None:
    moved = copy.deepcopy(_json("electra"))
    moved["validators"][0]["exit_epoch"] = str(EPOCH - 5)
    state = consensus.api_ssz("minimal", FORKS["electra"], "BeaconState", moved)
    answer = consensus.api_duties(
        "minimal", FORKS["electra"], state, "attester", EPOCH, GENESIS, indices=[0]
    )
    assert answer["data"] == []


@pytest.mark.parametrize("kind", ["attester", "ptc"])
def test_duties_too_far_ahead(kind: str) -> None:
    with raises(consensus.ConsensusError, f"Invalid epoch: {EPOCH + 2}") as error:
        _duties("gloas", kind, EPOCH + 2, indices=[0])
    assert error.value.code == 400


def test_duties_of_an_unknown_validator() -> None:
    count = len(_json("electra")["validators"])
    with raises(consensus.ConsensusError, f"Invalid validator index: {count}") as error:
        _duties("electra", "attester", EPOCH, indices=[count])
    assert error.value.code == 400


@pytest.mark.parametrize("fork", ["fulu", "gloas"])
@pytest.mark.parametrize("ahead", [0, 1])
def test_proposer_duties_read_the_lookahead(fork: str, ahead: int) -> None:
    epoch = EPOCH + ahead
    lookahead = _json(fork)["proposer_lookahead"]
    proposers = lookahead[ahead * SLOTS_PER_EPOCH : (ahead + 1) * SLOTS_PER_EPOCH]
    expected = [
        {"pubkey": _pubkey(fork, int(p)), "validator_index": p, "slot": str(epoch * 8 + i)}
        for i, p in enumerate(proposers)
    ]
    answer = _duties(fork, "proposer_v2", epoch)
    assert answer == {"dependent_root": _root_at(fork, (epoch - 1) * 8 - 1), "data": expected}


def test_proposer_duties_v1_root() -> None:
    answer = _duties("fulu", "proposer", EPOCH)
    assert answer["dependent_root"] == _root_at("fulu", EPOCH * SLOTS_PER_EPOCH - 1)


@pytest.mark.parametrize("fork", ["phase0", "electra"])
def test_proposer_duties_before_fulu_name_the_proposer_of_each_slot(fork: str) -> None:
    duties = _duties(fork, "proposer_v2", EPOCH)["data"]
    assert [d["slot"] for d in duties] == [
        str(EPOCH * SLOTS_PER_EPOCH + i) for i in range(SLOTS_PER_EPOCH)
    ]
    for duty in duties:
        # The state at the slot of the duty, as the slots of an epoch leave the draw unchanged.
        moved = copy.deepcopy(_json(fork))
        moved["slot"] = duty["slot"]
        state = consensus.api_ssz("minimal", FORKS[fork], "BeaconState", moved)
        assert consensus.is_proposer("minimal", FORKS[fork], state, int(duty["validator_index"]))


@pytest.mark.parametrize("fork", ["phase0", "fulu"])
def test_proposer_duties_out_of_range(fork: str) -> None:
    # Before Fulu only the current epoch is drawn; from Fulu the lookahead holds one more.
    epoch = EPOCH + 1 if fork == "phase0" else EPOCH + 2
    with raises(consensus.ConsensusError, f"Invalid epoch: {epoch}") as error:
        _duties(fork, "proposer_v2", epoch)
    assert error.value.code == 400


def test_dependent_root_of_the_first_epochs_is_genesis() -> None:
    # A lag of one reaches below epoch 0 for epochs 0 and 1, and slot 0 has no slot before it.
    for kind, epoch in [("attester", 0), ("attester", 1), ("proposer", 0)]:
        moved = copy.deepcopy(_json("electra"))
        moved["slot"] = "0"
        state = consensus.api_ssz("minimal", FORKS["electra"], "BeaconState", moved)
        answer = consensus.api_duties("minimal", FORKS["electra"], state, kind, epoch, GENESIS)
        assert answer["dependent_root"] == "0x" + GENESIS.hex()


@pytest.mark.parametrize("next_period", [False, True])
def test_sync_duties_list_the_seats(next_period: bool) -> None:
    state = _json("electra")
    key = "next_sync_committee" if next_period else "current_sync_committee"
    pubkeys = state[key]["pubkeys"]
    by_key = {v["pubkey"]: i for i, v in reversed(list(enumerate(state["validators"])))}
    members = sorted({by_key[k] for k in pubkeys})[:3]
    # The minimal period is 8 epochs, so epoch 20 is in period 2 and epoch 24 in period 3.
    epoch = 24 if next_period else EPOCH
    answer = _duties("electra", "sync", epoch, indices=members)
    assert answer == {
        "data": [
            {
                "pubkey": _pubkey("electra", m),
                "validator_index": str(m),
                "validator_sync_committee_indices": [
                    str(seat) for seat, k in enumerate(pubkeys) if k == _pubkey("electra", m)
                ],
            }
            for m in members
        ]
    }


def test_sync_duties_outside_the_periods() -> None:
    with raises(
        consensus.ConsensusError, "Epoch is outside the sync committee period of the state"
    ):
        _duties("electra", "sync", 32, indices=[0])


def test_ptc_duties_match_the_assignments() -> None:
    requested = _active("gloas", EPOCH)[:6]
    expected = []
    for index in requested:
        slot = consensus.get_ptc_assignment(
            "minimal", FORKS["gloas"], _state("gloas"), EPOCH, index, config=GLOAS
        )
        if slot is not None:
            expected.append(
                {
                    "pubkey": _pubkey("gloas", index),
                    "validator_index": str(index),
                    "slot": str(slot),
                }
            )
    answer = _duties("gloas", "ptc", EPOCH, indices=requested)
    assert answer == {"dependent_root": _root_at("gloas", (EPOCH - 1) * 8 - 1), "data": expected}


@pytest.mark.parametrize(
    ("fork", "kind", "message"),
    [
        ("phase0", "sync", "sync duties is not in a state before altair"),
        ("electra", "ptc", "PTC duties is not in a state before gloas"),
    ],
)
def test_duties_before_their_fork(fork: str, kind: str, message: str) -> None:
    with raises(consensus.ConsensusError, message) as error:
        _duties(fork, kind, EPOCH, indices=[0])
    assert error.value.code == 400


def test_unknown_kind() -> None:
    with raises(consensus.ConsensusError, "no duties are named aggregator") as error:
        _duties("electra", "aggregator", EPOCH)
    assert error.value.code == 0
