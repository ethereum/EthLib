"""The Beacon API answers that list the committees of a state, on pinned minimal states."""

import copy
from collections.abc import Callable
from functools import cache
from pathlib import Path
from typing import Any

import pytest

from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS

CASES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "fork" / "minimal"

# The minimal preset: slots per epoch, the lookahead of seeds, and the length of the mix buffer.
SLOTS_PER_EPOCH = 8
MIN_SEED_LOOKAHEAD = 1
EPOCHS_PER_HISTORICAL_VECTOR = 64

# The count of sync committee subnets, the same in every preset.
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


def _variant(fork: str, change: Callable[[dict[str, Any]], None]) -> tuple[dict[str, Any], bytes]:
    """A copy of the state of a fork with one change, as JSON and as SSZ."""
    state = copy.deepcopy(_json(fork))
    change(state)
    return state, consensus.api_ssz("minimal", FORKS[fork], "BeaconState", state)


def _committees(
    fork: str = "electra", state: bytes | None = None, **filters: int | None
) -> list[dict[str, Any]]:
    encoded = _state(fork) if state is None else state
    answer = consensus.api_committees("minimal", FORKS[fork], encoded, **filters)
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
@pytest.mark.parametrize("epoch", [EPOCH - 1, EPOCH, EPOCH + 1])
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


@pytest.mark.parametrize("epoch", [EPOCH - 1, EPOCH, EPOCH + 1])
def test_committees_match_the_assignments_of_the_guide(epoch: int) -> None:
    # The guide reads the same shuffle; the shuffle itself rests on the shuffling vectors.
    committees = {(c["slot"], c["index"]): c["validators"] for c in _committees(epoch=epoch)}
    for validator in _active("electra", epoch):
        assignment = consensus.get_committee_assignment(
            "minimal", FORKS["electra"], _state("electra"), epoch, validator
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


@pytest.mark.parametrize("slot", [SLOT - 1, SLOT + SLOTS_PER_EPOCH])
def test_committees_slot_outside_the_epoch(slot: int) -> None:
    with raises(consensus.ConsensusError, "Slot does not belong in epoch") as error:
        _committees(epoch=EPOCH, slot=slot)
    assert error.value.code == 400


def test_committees_after_the_next_epoch() -> None:
    with raises(consensus.ConsensusError, f"Epoch {EPOCH + 2} is after the next epoch") as error:
        _committees(epoch=EPOCH + 2)
    assert error.value.code == 400


def test_committees_before_the_mixes_of_the_state() -> None:
    """At epoch 100, the mix of an epoch up to 37 has been overwritten in the buffer."""
    late = 100
    _, state = _variant("electra", lambda s: s.update(slot=str(late * SLOTS_PER_EPOCH)))
    oldest = late + MIN_SEED_LOOKAHEAD + 2 - EPOCHS_PER_HISTORICAL_VECTOR
    assert len(_committees(state=state, epoch=oldest)) == SLOTS_PER_EPOCH * 2
    message = f"Epoch {oldest - 1} is before the mixes of the state"
    with raises(consensus.ConsensusError, message) as error:
        _committees(state=state, epoch=oldest - 1)
    assert error.value.code == 400


def test_committees_epoch_out_of_range() -> None:
    message = "expected an int below 18446744073709551616, got 18446744073709551616"
    with raises(consensus.ConsensusError, message) as error:
        _committees(epoch=2**64)
    assert error.value.code == 0


def _rotate_next(state: dict[str, Any]) -> None:
    """Make the next sync committee differ from the current one: its keys move by one seat."""
    keys = state["next_sync_committee"]["pubkeys"]
    state["next_sync_committee"]["pubkeys"] = keys[1:] + keys[:1]


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
    state, encoded = _variant("electra", _rotate_next)
    assert state["current_sync_committee"] != state["next_sync_committee"]
    keys = [validator["pubkey"] for validator in state["validators"]]
    # Each seat names the first validator that holds its key.
    expected = [str(keys.index(key)) for key in state[field]["pubkeys"]]
    size = len(expected) // SYNC_COMMITTEE_SUBNET_COUNT
    aggregates = [expected[k * size : (k + 1) * size] for k in range(SYNC_COMMITTEE_SUBNET_COUNT)]
    answer = consensus.api_sync_committees("minimal", FORKS["electra"], encoded, epoch=epoch)
    assert answer == {"data": {"validators": expected, "validator_aggregates": aggregates}}


def test_sync_committee_key_held_twice() -> None:
    """A key held by two validators names the first of them."""
    members = _json("electra")["current_sync_committee"]["pubkeys"]
    keys = [validator["pubkey"] for validator in _json("electra")["validators"]]
    first = keys.index(members[0])
    later = next(i for i in range(first + 1, len(keys)) if keys[i] not in members)

    def share(state: dict[str, Any]) -> None:
        state["validators"][later]["pubkey"] = members[0]

    _, encoded = _variant("electra", share)
    answer = consensus.api_sync_committees("minimal", FORKS["electra"], encoded)
    assert answer["data"]["validators"][0] == str(first)


def test_sync_committee_key_that_no_validator_holds() -> None:
    def drop(state: dict[str, Any]) -> None:
        state["current_sync_committee"]["pubkeys"][0] = "0x" + "ee" * 48

    _, encoded = _variant("electra", drop)
    message = "Internal error: a sync committee key that no validator holds"
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_sync_committees("minimal", FORKS["electra"], encoded)
    assert error.value.code == 500


@pytest.mark.parametrize("epoch", [15, 32])
def test_sync_committee_outside_the_periods_of_the_state(epoch: int) -> None:
    message = "Epoch is outside the sync committee period of the state"
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_sync_committees("minimal", FORKS["electra"], _state("electra"), epoch=epoch)
    assert error.value.code == 400


def test_no_sync_committee_before_altair() -> None:
    message = "sync_committees is not in a state before altair"
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_sync_committees("minimal", FORKS["phase0"], _state("phase0"))
    assert error.value.code == 400


# The window holds the slots of the epoch before the state's, its own, and the lookahead.
WINDOW = range((EPOCH - 1) * SLOTS_PER_EPOCH, (EPOCH + MIN_SEED_LOOKAHEAD + 1) * SLOTS_PER_EPOCH)


@cache
def _tagged() -> tuple[dict[str, Any], bytes]:
    """A Gloas state whose window holds, in row k, the validator index k at every seat."""

    def tag(state: dict[str, Any]) -> None:
        rows = state["ptc_window"]
        state["ptc_window"] = [[str(k)] * len(row) for k, row in enumerate(rows)]

    return _variant("gloas", tag)


@pytest.mark.parametrize("slot", [None, *WINDOW[:: SLOTS_PER_EPOCH // 2], WINDOW[-1]])
def test_ptc(slot: int | None) -> None:
    state, encoded = _tagged()
    at = SLOT if slot is None else slot
    # The first slot of the window is its row 0, and the rows follow the slots.
    members = state["ptc_window"][at - WINDOW[0]]
    assert members == [str(at - WINDOW[0])] * len(members)
    answer = consensus.api_ptc("minimal", FORKS["gloas"], encoded, GLOAS, slot=slot)
    assert answer == {"data": {"slot": str(at), "validators": members}}
    body = consensus.api_ptc_ssz("minimal", FORKS["gloas"], encoded, GLOAS, slot=slot)
    assert body == b"".join(int(v).to_bytes(8, "little") for v in [at, *members])


@pytest.mark.parametrize("slot", [WINDOW[0] - 1, WINDOW[-1] + 1])
def test_ptc_outside_the_window(slot: int) -> None:
    with raises(consensus.ConsensusError, "Slot is outside the PTC window of the state") as error:
        consensus.api_ptc("minimal", FORKS["gloas"], _state("gloas"), GLOAS, slot=slot)
    assert error.value.code == 400


def test_ptc_before_the_gloas_fork_epoch() -> None:
    state, encoded = _tagged()
    config = {"GLOAS_FORK_EPOCH": str(EPOCH)}
    with raises(consensus.ConsensusError, "Slot is outside the PTC window of the state") as error:
        consensus.api_ptc("minimal", FORKS["gloas"], encoded, config, slot=SLOT - 1)
    assert error.value.code == 400
    answer = consensus.api_ptc("minimal", FORKS["gloas"], encoded, config, slot=SLOT)
    members = state["ptc_window"][SLOT - WINDOW[0]]
    assert answer == {"data": {"slot": str(SLOT), "validators": members}}


def test_no_ptc_before_gloas() -> None:
    with raises(consensus.ConsensusError, "ptc is not in a state before gloas") as error:
        consensus.api_ptc("minimal", FORKS["fulu"], _state("fulu"), GLOAS)
    assert error.value.code == 400
