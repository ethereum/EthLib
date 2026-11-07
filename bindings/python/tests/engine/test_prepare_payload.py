"""The forkchoice update of an honest proposer, against values worked out from the guides."""

import hashlib
import struct

import pytest

from consensus.test_honest_validator import (
    _ALTAIR_FIELDS,
    FAR_FUTURE_EPOCH,
    GWEI,
    PUBKEY,
    _container,
    _validator,
)
from ethlib import consensus, engine
from raising import raises

PROPOSER_ERROR = engine.ProposerError

# Slot 70 is in epoch 2, and a mainnet slot lasts 12 seconds.
SLOT = 70
GENESIS_TIME = 1000
TIMESTAMP = GENESIS_TIME + SLOT * 12

# The RANDAO mix of epoch 2, and the latest block header of the state.
MIX = bytes([0x22]) * 32
HEADER = struct.pack("<QQ", 69, 5) + bytes([0x33]) * 32 + bytes([0x44]) * 32 + bytes([0x55]) * 32

SAFE = bytes([0x0A]) * 32
FINALIZED = bytes([0x0B]) * 32
FEE_RECIPIENT = bytes([0xFE]) * 20

# The address of the withdrawal credentials of validator 0, and its balance above 32 ether.
ADDRESS = bytes([0xAD]) * 20
EXCESS = GWEI

TTD = 58750000000000000000000
PRE_MERGE = ["bellatrix"]
AFTER_CAPELLA = ["shapella", "dencun", "pectra", "fusaka"]


def _hex(data: bytes) -> str:
    return "0x" + data.hex()


def _withdrawing_validator() -> bytes:
    """A validator of 32 ether with credentials of an address, active and never exiting."""
    credentials = bytes([1]) + bytes(11) + ADDRESS
    return (
        PUBKEY
        + credentials
        + struct.pack("<Q", 32 * GWEI)
        + b"\x00"
        + struct.pack("<QQQQ", 0, 0, FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH)
    )


def state_at(fork: str, slot: int = SLOT, balances: int = 2) -> bytes:
    """An Altair state at a slot, upgraded fork by fork to a fork from Bellatrix."""
    # Validator 0 can withdraw one ether from Capella, and validator 1 nothing.
    mixes = bytearray(65536 * 32)
    epoch = slot // 32 % 65536
    mixes[epoch * 32 : epoch * 32 + 32] = MIX
    altair = _container(
        _ALTAIR_FIELDS,
        {
            "genesis_time": struct.pack("<Q", GENESIS_TIME),
            "slot": struct.pack("<Q", slot),
            "latest_block_header": HEADER,
            "randao_mixes": bytes(mixes),
            "validators": _withdrawing_validator() + _validator(),
            "balances": struct.pack("<QQ", 32 * GWEI + EXCESS, 32 * GWEI)[: 8 * balances],
            "previous_epoch_participation": bytes(2),
            "current_epoch_participation": bytes(2),
            "inactivity_scores": bytes(16),
            "current_sync_committee": PUBKEY * 513,
            "next_sync_committee": PUBKEY * 513,
        },
    )
    state = altair
    for step in ["bellatrix", "shapella", "dencun", "pectra", "fusaka"]:
        state = consensus.upgrade_state("mainnet", step, state, verify=False)
        if step == fork:
            return state
    raise AssertionError(fork)


def merged_bellatrix(block_hash: bytes) -> bytes:
    """A Bellatrix state whose latest payload header, its last 536 bytes, has a block hash."""
    state = bytearray(state_at("bellatrix"))
    start = len(state) - 536 + 472
    state[start : start + 32] = block_hash
    return bytes(state)


def pow_block(block_hash: bytes, parent_hash: bytes, total_difficulty: int) -> bytes:
    return block_hash + parent_hash + total_difficulty.to_bytes(32, "little")


def prepare(fork: str, state: bytes, pow_chain=None, config=None):
    return engine.prepare_execution_payload(
        "mainnet", fork, state, SAFE, FINALIZED, FEE_RECIPIENT, pow_chain, config
    )


def expected(head: bytes, withdrawals=None, parent_root=None) -> dict:
    """The update that the guides give, with the withdrawals and the root of the later forks."""
    attributes = {
        "timestamp": hex(TIMESTAMP),
        "prevRandao": _hex(MIX),
        "suggestedFeeRecipient": _hex(FEE_RECIPIENT),
    }
    if withdrawals is not None:
        attributes["withdrawals"] = withdrawals
    if parent_root is not None:
        attributes["parentBeaconBlockRoot"] = _hex(parent_root)
    return {
        "forkchoiceState": {
            "headBlockHash": _hex(head),
            "safeBlockHash": _hex(SAFE),
            "finalizedBlockHash": _hex(FINALIZED),
        },
        "payloadAttributes": attributes,
    }


def _hash(tag: int) -> bytes:
    return hashlib.sha256(bytes([tag])).digest()


@pytest.fixture(scope="module")
def bellatrix() -> bytes:
    return state_at("bellatrix")


def test_terminal_block_of_the_difficulty(bellatrix: bytes):
    # The terminal block reaches the difficulty, and its parent, listed after it, does not.
    chain = [pow_block(_hash(2), _hash(1), TTD), pow_block(_hash(1), _hash(0), TTD - 1)]
    assert prepare("bellatrix", bellatrix, chain) == expected(_hash(2))


def test_first_of_two_terminal_blocks(bellatrix: bytes):
    # Two children of one parent below the difficulty both qualify, and the first one wins.
    chain = [
        pow_block(_hash(3), _hash(1), TTD + 1),
        pow_block(_hash(2), _hash(1), TTD),
        pow_block(_hash(1), _hash(0), TTD - 1),
    ]
    assert prepare("bellatrix", bellatrix, chain) == expected(_hash(3))


def test_terminal_block_at_genesis(bellatrix: bytes):
    # A block whose parent is the zero hash qualifies by its own difficulty.
    chain = [pow_block(_hash(1), bytes(32), TTD)]
    assert prepare("bellatrix", bellatrix, chain) == expected(_hash(1))


def test_block_after_the_terminal_block_is_skipped(bellatrix: bytes):
    # A block whose parent already reaches the difficulty is not terminal.
    chain = [
        pow_block(_hash(3), _hash(2), TTD + 2),
        pow_block(_hash(2), _hash(1), TTD),
        pow_block(_hash(1), _hash(0), TTD - 1),
    ]
    assert prepare("bellatrix", bellatrix, chain) == expected(_hash(2))


@pytest.mark.parametrize(
    "chain",
    [[], [pow_block(_hash(1), _hash(0), TTD - 1)]],
    ids=["empty", "below"],
)
def test_no_terminal_block_asks_nothing(bellatrix: bytes, chain: list):
    assert prepare("bellatrix", bellatrix, chain) is None


def test_terminal_block_with_an_unknown_parent(bellatrix: bytes):
    chain = [pow_block(_hash(2), _hash(1), TTD)]
    with raises(PROPOSER_ERROR, "proposer step failed with code 14") as info:
        prepare("bellatrix", bellatrix, chain)
    assert info.value.code == 14


def test_configured_terminal_block_hash(bellatrix: bytes):
    # The configured hash names the terminal block, whatever its difficulty.
    config = {"TERMINAL_BLOCK_HASH": _hex(_hash(5)), "TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH": "2"}
    chain = [pow_block(_hash(2), _hash(1), TTD), pow_block(_hash(5), _hash(4), 0)]
    assert prepare("bellatrix", bellatrix, chain, config) == expected(_hash(5))


def test_configured_terminal_block_hash_not_in_the_chain(bellatrix: bytes):
    config = {"TERMINAL_BLOCK_HASH": _hex(_hash(5)), "TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH": "0"}
    chain = [pow_block(_hash(2), _hash(1), TTD), pow_block(_hash(1), _hash(0), TTD - 1)]
    assert prepare("bellatrix", bellatrix, chain, config) is None


def test_configured_terminal_block_hash_before_its_epoch(bellatrix: bytes):
    # Epoch 2 is before the activation epoch 3, so the proposer asks nothing.
    config = {"TERMINAL_BLOCK_HASH": _hex(_hash(5)), "TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH": "3"}
    chain = [pow_block(_hash(5), _hash(4), TTD)]
    assert prepare("bellatrix", bellatrix, chain, config) is None


def test_after_the_merge_the_head_is_the_latest_payload():
    # Once the latest payload header is not empty, the chain of proof of work is not read.
    state = merged_bellatrix(_hash(9))
    assert prepare("bellatrix", state, [pow_block(_hash(1), bytes(32), TTD)]) == expected(_hash(9))


@pytest.mark.parametrize("fork", AFTER_CAPELLA)
def test_withdrawals_and_parent_root(fork: str):
    # Validator 0 withdraws the ether above its 32, as the first withdrawal, at index 0.
    withdrawal = {"index": "0x0", "validatorIndex": "0x0", "address": _hex(ADDRESS)}
    withdrawal["amount"] = hex(EXCESS)
    # From Capella the head is the block hash of the latest payload, zero after the upgrades.
    parent_root = None
    if fork != "shapella":
        parent_root, _ = consensus.ssz_static("mainnet", fork, "BeaconBlockHeader", HEADER)
    got = prepare(fork, state_at(fork), [pow_block(_hash(1), bytes(32), TTD)])
    assert got == expected(bytes(32), [withdrawal], parent_root)


def test_time_of_a_slot_beyond_64_bits():
    # The slot times 12000 milliseconds overflows 64 bits.
    with raises(PROPOSER_ERROR, "proposer step failed with code 1") as info:
        prepare("shapella", state_at("shapella", slot=2**63))
    assert info.value.code == 1


def test_expected_withdrawals_fail():
    # Validator 1 has no balance, so the sweep of withdrawals cannot read it.
    with raises(PROPOSER_ERROR, "proposer step failed with code 5") as info:
        prepare("shapella", state_at("shapella", balances=1))
    assert info.value.code == 5


@pytest.mark.parametrize("fork", ["phase0", "altair", "glamsterdam", "hegota"])
def test_fork_without_this_preparation(bellatrix: bytes, fork: str):
    with raises(PROPOSER_ERROR, f"no payload preparation at {fork}") as info:
        prepare(fork, bellatrix)
    assert info.value.code == 0


@pytest.mark.parametrize(
    ("name", "fork", "message"),
    [
        ("nowhere", "bellatrix", "no preset is named nowhere"),
        ("mainnet", "nowhere", "no fork named nowhere"),
        ("mainnet", "frontier", "frontier is not a fork of the beacon chain"),
    ],
    ids=["preset", "fork", "execution"],
)
def test_unknown_preset_or_fork(bellatrix: bytes, name: str, fork: str, message: str):
    with raises(PROPOSER_ERROR, message) as info:
        engine.prepare_execution_payload(name, fork, bellatrix, SAFE, FINALIZED, FEE_RECIPIENT)
    assert info.value.code == 0


@pytest.mark.parametrize(
    ("safe", "finalized", "fee", "message"),
    [
        (SAFE[:31], FINALIZED, FEE_RECIPIENT, "Err.scope 32 31"),
        (SAFE, FINALIZED[:31], FEE_RECIPIENT, "Err.scope 32 31"),
        (SAFE, FINALIZED, FEE_RECIPIENT[:19], "Err.scope 20 19"),
    ],
    ids=["safe", "finalized", "fee recipient"],
)
def test_input_of_the_wrong_length(bellatrix: bytes, safe, finalized, fee, message: str):
    with raises(PROPOSER_ERROR, f"input rejected: EthLib.Serialization.Ssz.{message}") as info:
        engine.prepare_execution_payload("mainnet", "bellatrix", bellatrix, safe, finalized, fee)
    assert info.value.code == 0


def test_block_of_proof_of_work_that_does_not_decode(bellatrix: bytes):
    with raises(PROPOSER_ERROR, "input rejected: EthLib.Serialization.Ssz.Err.scope 96 95") as info:
        prepare("bellatrix", bellatrix, [bytes(95)])
    assert info.value.code == 0


def test_state_that_does_not_decode():
    with raises(
        PROPOSER_ERROR, "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 2736633 0"
    ) as info:
        prepare("bellatrix", b"")
    assert info.value.code == 0
