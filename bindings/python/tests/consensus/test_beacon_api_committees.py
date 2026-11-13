"""The Beacon API answers that list the committees of a state, on pinned minimal states."""

from functools import cache
from pathlib import Path
from typing import Any

import pytest

from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS

CASES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "fork" / "minimal"

# The minimal preset: slots per epoch, the lookahead of seeds, and the sync committee period.
SLOTS_PER_EPOCH = 8
MIN_SEED_LOOKAHEAD = 1
EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 8
SYNC_COMMITTEE_SUBNET_COUNT = 4

# The states are moved to epoch 20, in sync committee period 2.
EPOCH = 20
SLOT = EPOCH * SLOTS_PER_EPOCH

# The minimal configuration does not schedule Gloas, so the PTC tests start it at epoch 0.
GLOAS = {"GLOAS_FORK_EPOCH": "0"}


@cache
def _json(fork: str) -> dict[str, Any]:
    """The JSON of the base state of a fork, moved to the slot above."""
    # The upgrade to Altair starts from a Phase 0 state, which no other case gives.
    case, part = ("altair", "pre") if fork == "phase0" else (fork, "post")
    path = (
        CASES / case / "fork" / "fork" / "pyspec_tests" / "fork_base_state" / f"{part}.ssz_snappy"
    )
    base = snappy.decompress(path.read_bytes())
    state = consensus.api_json("minimal", FORKS[fork], "BeaconState", base)
    state["slot"] = str(SLOT)
    return state


@cache
def _state(fork: str) -> bytes:
    return consensus.api_ssz("minimal", FORKS[fork], "BeaconState", _json(fork))


def _committees(fork: str = "electra", **filters: int | None) -> list[dict[str, Any]]:
    answer = consensus.api_committees("minimal", FORKS[fork], _state(fork), **filters)
    assert list(answer) == ["data"]
    return answer["data"]


def _active(fork: str, epoch: int) -> list[int]:
    """The indices of the validators active in an epoch, read from the JSON of the state."""
    return [
        i
        for i, validator in enumerate(_json(fork)["validators"])
        if int(validator["activation_epoch"]) <= epoch < int(validator["exit_epoch"])
    ]


@pytest.mark.parametrize("fork", ["phase0", "electra", "gloas"])
@pytest.mark.parametrize("epoch", [EPOCH, EPOCH + 1])
def test_committees_partition_the_active_validators(fork: str, epoch: int) -> None:
    committees = _committees(fork, epoch=epoch)
    active = _active(fork, epoch)
    # The count of committees per slot of the source, from the minimal preset.
    per_slot = max(1, min(4, len(active) // SLOTS_PER_EPOCH // 4))
    slots = range(epoch * SLOTS_PER_EPOCH, (epoch + 1) * SLOTS_PER_EPOCH)
    assert [(c["slot"], c["index"]) for c in committees] == [
        (str(slot), str(index)) for slot in slots for index in range(per_slot)
    ]
    members = sorted(int(v) for c in committees for v in c["validators"])
    assert members == active


def test_committees_match_the_assignments_of_the_guide() -> None:
    committees = {(c["slot"], c["index"]): c["validators"] for c in _committees(epoch=EPOCH)}
    for validator in _active("electra", EPOCH):
        assignment = consensus.get_committee_assignment(
            "minimal", FORKS["electra"], _state("electra"), EPOCH, validator
        )
        assert assignment is not None
        committee, index, slot = assignment
        assert committees[(str(slot), str(index))] == [str(v) for v in committee]


def test_committees_default_to_the_epoch_of_the_state() -> None:
    assert _committees() == _committees(epoch=EPOCH)


def test_committees_filters() -> None:
    every = _committees(epoch=EPOCH)
    slot = SLOT + 3
    assert _committees(slot=slot) == [c for c in every if c["slot"] == str(slot)]
    assert _committees(index=0) == [c for c in every if c["index"] == "0"]
    assert _committees(index=0, slot=slot) == [
        c for c in every if c["index"] == "0" and c["slot"] == str(slot)
    ]
    assert _committees(index=1000) == []


def test_committees_errors() -> None:
    with raises(consensus.ConsensusError, "Slot does not belong in epoch") as error:
        _committees(epoch=EPOCH, slot=SLOT - 1)
    assert error.value.code == 400
    with raises(consensus.ConsensusError, f"Epoch {EPOCH + 2} is after the next epoch") as error:
        _committees(epoch=EPOCH + 2)
    assert error.value.code == 400


def _sync(fork: str = "electra", epoch: int | None = None) -> dict[str, Any]:
    return consensus.api_sync_committees("minimal", FORKS[fork], _state(fork), epoch=epoch)


@pytest.mark.parametrize(
    ("epoch", "field"),
    [
        (None, "current_sync_committee"),
        (16, "current_sync_committee"),
        (23, "current_sync_committee"),
        (24, "next_sync_committee"),
        (31, "next_sync_committee"),
    ],
)
def test_sync_committee_indices(epoch: int | None, field: str) -> None:
    state = _json("electra")
    keys = [validator["pubkey"] for validator in state["validators"]]
    # Each seat names the first validator that holds its key.
    expected = [str(keys.index(key)) for key in state[field]["pubkeys"]]
    size = len(expected) // SYNC_COMMITTEE_SUBNET_COUNT
    aggregates = [expected[k * size : (k + 1) * size] for k in range(SYNC_COMMITTEE_SUBNET_COUNT)]
    assert _sync(epoch=epoch) == {
        "data": {"validators": expected, "validator_aggregates": aggregates}
    }


@pytest.mark.parametrize("epoch", [15, 32])
def test_sync_committee_outside_the_periods_of_the_state(epoch: int) -> None:
    message = "Epoch is outside the sync committee period of the state"
    with raises(consensus.ConsensusError, message) as error:
        _sync(epoch=epoch)
    assert error.value.code == 400


def test_no_sync_committee_before_altair() -> None:
    with raises(
        consensus.ConsensusError, "sync_committees is not in a state before altair"
    ) as error:
        _sync("phase0")
    assert error.value.code == 400


def _window_position(slot: int) -> int:
    """The position of a slot in the window of a state at the epoch above."""
    return (slot // SLOTS_PER_EPOCH - EPOCH + 1) * SLOTS_PER_EPOCH + slot % SLOTS_PER_EPOCH


# The window holds the slots of the epoch before the state's, its own, and the lookahead.
WINDOW = range((EPOCH - 1) * SLOTS_PER_EPOCH, (EPOCH + MIN_SEED_LOOKAHEAD + 1) * SLOTS_PER_EPOCH)


@pytest.mark.parametrize("slot", [None, WINDOW[0], SLOT + 5, WINDOW[-1]])
def test_ptc(slot: int | None) -> None:
    state = _state("gloas")
    window = _json("gloas")["ptc_window"]
    at = SLOT if slot is None else slot
    members = window[_window_position(at)]
    answer = consensus.api_ptc("minimal", FORKS["gloas"], state, GLOAS, slot=slot)
    assert answer == {"data": {"slot": str(at), "validators": members}}
    body = consensus.api_ptc_ssz("minimal", FORKS["gloas"], state, GLOAS, slot=slot)
    assert body == b"".join(int(v).to_bytes(8, "little") for v in [at, *members])


@pytest.mark.parametrize("slot", [WINDOW[0] - 1, WINDOW[-1] + 1])
def test_ptc_outside_the_window(slot: int) -> None:
    with raises(consensus.ConsensusError, "Slot is outside the PTC window of the state") as error:
        consensus.api_ptc("minimal", FORKS["gloas"], _state("gloas"), GLOAS, slot=slot)
    assert error.value.code == 400


def test_ptc_before_the_gloas_fork_epoch() -> None:
    config = {"GLOAS_FORK_EPOCH": str(EPOCH)}
    with raises(consensus.ConsensusError, "Slot is outside the PTC window of the state") as error:
        consensus.api_ptc("minimal", FORKS["gloas"], _state("gloas"), config, slot=SLOT - 1)
    assert error.value.code == 400
    answer = consensus.api_ptc("minimal", FORKS["gloas"], _state("gloas"), config, slot=SLOT)
    assert answer["data"]["slot"] == str(SLOT)


def test_no_ptc_before_gloas() -> None:
    with raises(consensus.ConsensusError, "ptc is not in a state before gloas") as error:
        consensus.api_ptc("minimal", FORKS["fulu"], _state("fulu"), GLOAS)
    assert error.value.code == 400
