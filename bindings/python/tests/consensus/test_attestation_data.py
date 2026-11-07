"""The attestation data of an honest attester, against values worked out from the guides."""

import struct

import pytest

from ethlib import consensus
from raising import raises

from .test_honest_validator import (
    _ALTAIR_FIELDS,
    _PHASE0_FIELDS,
    GLOAS,
    GWEI,
    _container,
    _validator,
)

DUTY_ERROR = consensus.ValidatorDutyError

COUNT = 64
SLOTS_PER_EPOCH = 32
SLOTS_PER_HISTORICAL_ROOT = 8192

# The root of the head block, given by the fork choice.
HEAD = bytes([0xAA]) * 32

# The current justified checkpoint of the state: epoch 1 at a root of 0x11 bytes.
SOURCE = struct.pack("<Q", 1) + bytes([0x11]) * 32

# Slot 70 is in epoch 2, whose first slot is 64.
SLOT = 70


def _block_roots() -> bytes:
    """A buffer of block roots whose entry at position i holds the byte i mod 256, 32 times."""
    return b"".join(bytes([i % 256]) * 32 for i in range(SLOTS_PER_HISTORICAL_ROOT))


def _values(slot: int) -> dict:
    """The fields of a state at a slot, with block roots and a current justified checkpoint."""
    return {
        "slot": struct.pack("<Q", slot),
        "block_roots": _block_roots(),
        "current_justified_checkpoint": SOURCE,
        "validators": _validator() * COUNT,
        "balances": struct.pack("<Q", 32 * GWEI) * COUNT,
    }


def phase0_state(slot: int) -> bytes:
    return _container(_PHASE0_FIELDS, _values(slot))


def altair_state(slot: int) -> bytes:
    values = _values(slot)
    values["previous_epoch_participation"] = bytes(COUNT)
    values["current_epoch_participation"] = bytes(COUNT)
    values["inactivity_scores"] = bytes(8 * COUNT)
    return _container(_ALTAIR_FIELDS, values)


def upgraded_state(slot: int, last: str) -> bytes:
    """An Altair state at a slot, upgraded fork by fork up to the last fork named."""
    state = altair_state(slot)
    for fork in ["bellatrix", "shapella", "dencun", "pectra", "fusaka", "glamsterdam"]:
        state = consensus.upgrade_state("mainnet", fork, state, verify=False, config=GLOAS)
        if fork == last:
            return state
    raise AssertionError(last)


def expected(slot: int, index: int, target_root: bytes) -> bytes:
    """Attestation data for the head block, from the source to the current epoch at a root."""
    epoch = slot // SLOTS_PER_EPOCH
    return struct.pack("<QQ", slot, index) + HEAD + SOURCE + struct.pack("<Q", epoch) + target_root


def recorded_root(slot: int) -> bytes:
    """The root that the buffer of the state records for a slot."""
    return bytes([slot % SLOTS_PER_HISTORICAL_ROOT % 256]) * 32


def data(fork: str, state: bytes, head_slot: int, committee: int, status: int) -> bytes:
    return consensus.get_attestation_data(
        "mainnet", fork, state, HEAD, head_slot, committee, status
    )


@pytest.fixture(scope="module")
def gloas() -> bytes:
    return upgraded_state(SLOT, "glamsterdam")


def test_phase0_target_is_the_recorded_root_of_the_first_slot():
    # Inside epoch 2, the target root is the root that the state records for slot 64.
    got = data("phase0", phase0_state(SLOT), SLOT, 3, 0)
    assert got == expected(SLOT, 3, recorded_root(64))


def test_phase0_target_at_the_first_slot_is_the_head():
    # At slot 64 the head block is the block of the epoch boundary.
    got = data("phase0", phase0_state(64), 64, 3, 0)
    assert got == expected(64, 3, HEAD)


def test_altair_keeps_the_committee_index():
    got = data("altair", altair_state(SLOT), SLOT, 1, 0)
    assert got == expected(SLOT, 1, recorded_root(64))


def test_electra_index_is_zero():
    # From Electra the attestation names its committee, so the index in the data is zero.
    state = upgraded_state(SLOT, "pectra")
    assert data("pectra", state, SLOT - 1, 3, 1) == expected(SLOT, 0, recorded_root(64))


def test_gloas_head_of_the_slot_has_index_zero(gloas: bytes):
    # A head block of the slot of the data has index zero, whatever its payload status.
    for status in (0, 1, 2):
        assert data("glamsterdam", gloas, SLOT, 3, status) == expected(SLOT, 0, recorded_root(64))


@pytest.mark.parametrize(("status", "index"), [(0, 0), (1, 1)], ids=["empty", "full"])
def test_gloas_earlier_head_has_the_payload_status(gloas: bytes, status: int, index: int):
    got = data("glamsterdam", gloas, SLOT - 1, 3, status)
    assert got == expected(SLOT, index, recorded_root(64))


def test_gloas_earlier_head_with_a_pending_status(gloas: bytes):
    with raises(DUTY_ERROR, "validator duty failed with code 13") as info:
        data("glamsterdam", gloas, SLOT - 1, 3, 2)
    assert info.value.code == 13


def test_root_of_the_first_slot_out_of_range():
    # At slot 2^64 - 2 the first slot of the epoch plus the buffer length overflows 64 bits.
    with raises(DUTY_ERROR, "validator duty failed with code 1") as info:
        data("phase0", phase0_state(2**64 - 2), 0, 0, 0)
    assert info.value.code == 1


def test_unknown_payload_status():
    with raises(DUTY_ERROR, "unknown payload status 3") as info:
        data("phase0", phase0_state(SLOT), SLOT, 0, 3)
    assert info.value.code == 0


def test_head_root_of_the_wrong_length():
    with raises(DUTY_ERROR, "input rejected: EthLib.Serialization.Ssz.Err.scope 32 31"):
        consensus.get_attestation_data("mainnet", "phase0", phase0_state(SLOT), HEAD[:31], 0, 0, 0)


def test_state_that_does_not_decode():
    with raises(DUTY_ERROR, "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 2687377 0"):
        data("phase0", b"", 0, 0, 0)


@pytest.mark.parametrize(
    ("name", "fork", "message"),
    [
        ("nowhere", "phase0", "no preset is named nowhere"),
        ("mainnet", "nowhere", "no fork named nowhere"),
        ("mainnet", "frontier", "frontier is not a fork of the beacon chain"),
        ("mainnet", "bpo3", "fork bpo3 not yet specified"),
    ],
    ids=["preset", "fork", "execution", "unspecified"],
)
def test_unknown_preset_or_fork(name: str, fork: str, message: str):
    with raises(DUTY_ERROR, message) as info:
        consensus.get_attestation_data(name, fork, phase0_state(SLOT), HEAD, 0, 0, 0)
    assert info.value.code == 0
