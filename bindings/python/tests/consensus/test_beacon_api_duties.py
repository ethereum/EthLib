"""The Beacon API duty answers, on the pinned minimal states moved to epoch 20."""

import copy
from functools import cache
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
)

# The length of the buffer of block roots in the minimal preset.
SLOTS_PER_HISTORICAL_ROOT = 64

GENESIS = bytes(range(32))


@cache
def _rooted(fork: str) -> dict[str, Any]:
    """The JSON of the state of a fork, with a different block root at each place of its buffer."""
    state = copy.deepcopy(_json(fork))
    state["block_roots"] = [
        "0x" + bytes([i + 1]).hex() * 32 for i in range(SLOTS_PER_HISTORICAL_ROOT)
    ]
    return state


@cache
def _state(fork: str) -> bytes:
    return consensus.api_ssz("minimal", FORKS[fork], "BeaconState", _rooted(fork))


# The minimal configuration does not schedule Fulu, so the states from Fulu start it at epoch 0.
FULU = {"FULU_FORK_EPOCH": "0"}

# The configuration of the duties of a state of each fork.
CONFIGS: dict[str, dict[str, str] | None] = {"fulu": FULU, "gloas": GLOAS | FULU}


def _duties(
    fork: str, kind: str, epoch: int, *, config: dict[str, str] | None = None, **options: Any
) -> dict[str, Any]:
    config = config if config is not None else CONFIGS.get(fork)
    return consensus.api_duties(
        "minimal", FORKS[fork], _state(fork), kind, epoch, GENESIS, config=config, **options
    )


def _pubkey(fork: str, index: int) -> str:
    return _json(fork)["validators"][index]["pubkey"]


def _root_at(fork: str, slot: int) -> str:
    """The block root at a slot, read from the buffer of the state."""
    return _rooted(fork)["block_roots"][slot % SLOTS_PER_HISTORICAL_ROOT]


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


@pytest.mark.parametrize("fork", ["phase0", "electra"])
def test_attester_duties_skip_an_inactive_validator(fork: str) -> None:
    moved = copy.deepcopy(_rooted(fork))
    moved["validators"][0]["exit_epoch"] = str(EPOCH - 5)
    state = consensus.api_ssz("minimal", FORKS[fork], "BeaconState", moved)
    answer = consensus.api_duties(
        "minimal", FORKS[fork], state, "attester", EPOCH, GENESIS, indices=[0]
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
        {
            "pubkey": _pubkey(fork, int(p)),
            "validator_index": p,
            "slot": str(epoch * SLOTS_PER_EPOCH + i),
        }
        for i, p in enumerate(proposers)
    ]
    answer = _duties(fork, "proposer_v2", epoch)
    root = _root_at(fork, (epoch - 1) * SLOTS_PER_EPOCH - 1)
    assert answer == {"dependent_root": root, "data": expected}


def test_proposer_duties_v2_root_before_fulu() -> None:
    # Before Fulu the proposers of the epoch are drawn at its start, as for the first version.
    answer = _duties("electra", "proposer_v2", EPOCH)
    assert answer["dependent_root"] == _root_at("electra", EPOCH * SLOTS_PER_EPOCH - 1)


@pytest.mark.parametrize("ahead", [0, 1])
def test_proposer_duties_v2_root_at_the_fulu_fork_epoch(ahead: int) -> None:
    # The upgrade draws the proposers of the fork epoch after the epoch before it.
    #
    # So the fork epoch and the epoch after it both depend on the last slot before the fork.
    fork_epoch = {"FULU_FORK_EPOCH": str(EPOCH)}
    answer = _duties("fulu", "proposer_v2", EPOCH + ahead, config=fork_epoch)
    assert answer["dependent_root"] == _root_at("fulu", EPOCH * SLOTS_PER_EPOCH - 1)


def test_proposer_duties_v1_root() -> None:
    answer = _duties("fulu", "proposer", EPOCH)
    assert answer["dependent_root"] == _root_at("fulu", EPOCH * SLOTS_PER_EPOCH - 1)
    second = _duties("fulu", "proposer_v2", EPOCH)
    assert second["dependent_root"] != answer["dependent_root"]
    assert second["data"] == answer["data"]


def test_proposer_duties_v1_only_for_the_current_epoch() -> None:
    with raises(consensus.ConsensusError, f"Invalid epoch: {EPOCH + 1}") as error:
        _duties("fulu", "proposer", EPOCH + 1)
    assert error.value.code == 400


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


@pytest.mark.parametrize(
    ("fork", "epoch"), [("phase0", EPOCH + 1), ("fulu", EPOCH + 2), ("fulu", EPOCH - 1)]
)
def test_proposer_duties_out_of_range(fork: str, epoch: int) -> None:
    # Before Fulu only the current epoch is drawn; from Fulu the lookahead holds one more.
    with raises(consensus.ConsensusError, f"Invalid epoch: {epoch}") as error:
        _duties(fork, "proposer_v2", epoch)
    assert error.value.code == 400


@pytest.mark.parametrize(("kind", "epoch"), [("attester", 0), ("attester", 1), ("proposer", 0)])
def test_dependent_root_of_the_first_epochs_is_genesis(kind: str, epoch: int) -> None:
    # A lag of one reaches below epoch 0 for epoch 0, and slot 0 has no slot before it.
    moved = copy.deepcopy(_rooted("electra"))
    moved["slot"] = "0"
    state = consensus.api_ssz("minimal", FORKS["electra"], "BeaconState", moved)
    answer = consensus.api_duties(
        "minimal", FORKS["electra"], state, kind, epoch, GENESIS, indices=[0]
    )
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


@pytest.mark.parametrize("epoch", [8, 32])
def test_sync_duties_outside_the_periods(epoch: int) -> None:
    message = "Epoch is outside the sync committee period of the state"
    with raises(consensus.ConsensusError, message) as error:
        _duties("electra", "sync", epoch, indices=[0])
    assert error.value.code == 400


@pytest.mark.parametrize("epoch", [EPOCH, EPOCH + 1])
def test_ptc_duties_match_the_assignments(epoch: int) -> None:
    requested = _active("gloas", epoch)[:6]
    expected = []
    for index in requested:
        slot = consensus.get_ptc_assignment(
            "minimal", FORKS["gloas"], _state("gloas"), epoch, index, config=GLOAS
        )
        if slot is not None:
            expected.append(
                {
                    "pubkey": _pubkey("gloas", index),
                    "validator_index": str(index),
                    "slot": str(slot),
                }
            )
    answer = _duties("gloas", "ptc", epoch, indices=requested)
    root = _root_at("gloas", (epoch - 1) * SLOTS_PER_EPOCH - 1)
    assert answer == {"dependent_root": root, "data": expected}


def _ptc(fork_epoch: int, epoch: int) -> dict[str, Any]:
    """The PTC answer of the Gloas state for two active validators, with Gloas at an epoch."""
    config = {"GLOAS_FORK_EPOCH": str(fork_epoch)}
    requested = _active("gloas", EPOCH)[:2]
    return consensus.api_duties(
        "minimal",
        FORKS["gloas"],
        _state("gloas"),
        "ptc",
        epoch,
        GENESIS,
        config=config,
        indices=requested,
    )


def test_ptc_root_at_the_gloas_fork_epoch() -> None:
    """At the fork epoch the PTC root is that of the last slot before it, one epoch later."""
    # Both answers depend on the root at the last slot of epoch 19.
    root = _root_at("gloas", EPOCH * SLOTS_PER_EPOCH - 1)
    assert _ptc(EPOCH, EPOCH)["dependent_root"] == root
    assert _ptc(EPOCH, EPOCH + 1)["dependent_root"] == root
    # Without the fork at epoch 20, the root of epoch 20 is one epoch earlier.
    assert _ptc(0, EPOCH)["dependent_root"] == _root_at("gloas", (EPOCH - 1) * SLOTS_PER_EPOCH - 1)


def test_ptc_duties_of_the_next_fork_epoch() -> None:
    """The duties of a fork epoch that starts after the state wait for its last slot before."""
    with raises(consensus.ConsensusError, f"Invalid epoch: {EPOCH + 1}") as error:
        _ptc(EPOCH + 1, EPOCH + 1)
    assert error.value.code == 400


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


@pytest.mark.parametrize(("kind", "epoch"), [("attester", 11), ("ptc", 18)])
def test_duties_too_old(kind: str, epoch: int) -> None:
    # The block roots of the minimal state span 64 slots, so the root at slot 79 is gone.
    # The PTC window of the state starts at the previous epoch.
    with raises(consensus.ConsensusError, f"Invalid epoch: {epoch}") as error:
        _duties("gloas", kind, epoch, indices=[0])
    assert error.value.code == 400


def test_ptc_duties_refuse_a_repeated_index() -> None:
    with raises(consensus.ConsensusError, "Repeated validator index") as error:
        _duties("gloas", "ptc", EPOCH, indices=[1, 1])
    assert error.value.code == 400


@pytest.mark.parametrize("kind", ["attester", "sync", "ptc"])
def test_empty_request(kind: str) -> None:
    with raises(consensus.ConsensusError, "Empty validator index list") as error:
        _duties("gloas", kind, EPOCH, indices=[])
    assert error.value.code == 400


def test_unknown_kind() -> None:
    with raises(consensus.ConsensusError, "no duties are named aggregator") as error:
        _duties("electra", "aggregator", EPOCH)
    assert error.value.code == 0
