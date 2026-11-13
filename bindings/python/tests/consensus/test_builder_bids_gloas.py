"""The Gloas checks of a request for a bid and of a fetched bid, on a state with a builder."""

import hashlib
import struct
from pathlib import Path
from typing import Any

import pytest
from py_ecc.bls import G2ProofOfPossession

from ethlib import consensus
from ethlib.errors import TransitionError
from ethlib.networking import snappy
from raising import raises

# The pre-state of a builder exit of the consensus tests: it holds an active builder.
STATE = (
    Path(__file__).resolve().parents[4]
    / "tests/consensus/operations/minimal/gloas/operations/builder_exit_request/pyspec_tests"
    / "process_builder_exit_request__success"
)
FORK = "glamsterdam"
# A key that no validator of the consensus tests has: their secret keys are their index plus one.
SECRET_KEY = 10**30
PUBKEY = G2ProofOfPossession.SkToPk(SECRET_KEY)
BUILDER_INDEX = 0
SELF_BUILD = 2**64 - 1
# The parent's gas limit, the proposer's target, and the one step from the first toward the second.
PARENT_GAS_LIMIT = 30_000_000
TARGET_GAS_LIMIT = 2 * PARENT_GAS_LIMIT
GAS_LIMIT = PARENT_GAS_LIMIT + PARENT_GAS_LIMIT // 1024 - 1
FEE_RECIPIENT = bytes(19) + b"\x01"
# Where the genesis validators root, the slot, the current fork version and the latest header sit.
ROOT_AT, SLOT_AT, VERSION_AT, HEADER_AT = 8, 40, 52, 64
# The latest block header: slot, proposer, parent root, state root and body root.
HEADER_SIZE = 112
# The RANDAO mixes follow the block and state roots, the Eth1 data, the deposit index and four
# offsets.
RANDAO_AT = 4368
# Minimal slots per epoch, and the length of the vector of RANDAO mixes.
SLOTS_PER_EPOCH, MIXES = 8, 64
# Where a minimal Gloas state stores its latest block hash, after the two sync committees.
LATEST_BLOCK_HASH_AT = 10_229
DOMAIN_BEACON_BUILDER = bytes([0x0B, 0, 0, 0])
# The withdrawable epoch of a builder follows its key, version, address, balance and deposit epoch.
WITHDRAWABLE_AFTER_KEY = 48 + 1 + 20 + 8 + 8
# The exit epoch of a validator follows its key, credentials, balance, slashed flag and two epochs.
EXIT_AFTER_KEY = 48 + 32 + 8 + 1 + 8 + 8
# The block hash of the latest bid, written into the state: the parent with its payload.
FULL_PARENT_HASH = b"\xbb" * 32
CURRENT_MIX = b"\x11" * 32


def _sha(data: bytes) -> bytes:
    """The SHA-256 digest of the bytes."""
    return hashlib.sha256(data).digest()


def _slot(state: bytes) -> int:
    """The slot of a state."""
    (slot,) = struct.unpack_from("<Q", state, SLOT_AT)
    return slot


def _mix_at(state: bytes, epoch: int) -> int:
    """The position of the RANDAO mix of an epoch in a state."""
    return RANDAO_AT + 32 * (epoch % MIXES)


def _state() -> bytes:
    """The pinned state, with the test key as builder, a mix of its own and a full parent hash."""
    state = snappy.decompress((STATE / "pre.ssz_snappy").read_bytes())
    request = snappy.decompress((STATE / "builder_exit_request.ssz_snappy").read_bytes())
    # The request holds the source address, then the key of the builder.
    builder_key = request[20:68]
    assert state.count(builder_key) == 1
    state = state.replace(builder_key, PUBKEY)
    # Every mix of the pinned state is the same, so the current epoch gets one of its own.
    at = _mix_at(state, _slot(state) // SLOTS_PER_EPOCH)
    state = state[:at] + CURRENT_MIX + state[at + 32 :]
    # The latest bid opens with its parent hash, the latest block hash, then its parent root.
    parent_hash = state[LATEST_BLOCK_HASH_AT : LATEST_BLOCK_HASH_AT + 32]
    bid = state.index(parent_hash, LATEST_BLOCK_HASH_AT + 32)
    at = bid + 64
    state = state[:at] + FULL_PARENT_HASH + state[at + 32 :]
    bid_json = consensus.api_json("minimal", FORK, "BeaconState", state)
    assert bid_json["latest_execution_payload_bid"]["block_hash"] == "0x" + FULL_PARENT_HASH.hex()
    return state


def _parent_root(state: bytes) -> bytes:
    """The root of the latest block header of a state."""
    header = state[HEADER_AT : HEADER_AT + HEADER_SIZE]
    root, _ = consensus.ssz_static("minimal", FORK, "BeaconBlockHeader", header)
    return root


def _empty_parent_hash(state: bytes) -> bytes:
    """The latest block hash of a state: the parent without its payload."""
    return state[LATEST_BLOCK_HASH_AT : LATEST_BLOCK_HASH_AT + 32]


def _preferences(validator_index: int = 0) -> bytes:
    """Proposer preferences: dependent root, slot, validator, fee recipient and gas target."""
    fields = struct.pack("<QQ", 0, validator_index)
    return bytes(32) + fields + FEE_RECIPIENT + struct.pack("<Q", TARGET_GAS_LIMIT)


def _signed_bid(
    state: bytes,
    *,
    later_slots: int = 0,
    parent_hash: bytes | None = None,
    parent_root: bytes | None = None,
    prev_randao: bytes = CURRENT_MIX,
    fee_recipient: bytes = FEE_RECIPIENT,
    gas_limit: int = GAS_LIMIT,
    builder_index: int = BUILDER_INDEX,
    value: int = 0,
    key: int = SECRET_KEY,
) -> bytes:
    """A bid on the state, right unless a field is given, signed under the builder domain."""
    message = (
        (_empty_parent_hash(state) if parent_hash is None else parent_hash)
        + (_parent_root(state) if parent_root is None else parent_root)
        + bytes(32)
        + prev_randao
        + fee_recipient
        + struct.pack("<QQQQQ", gas_limit, builder_index, _slot(state) + later_slots, value, 0)
        # The offset of the empty list of commitments, then the root of the requests.
        + struct.pack("<I", 4 * 32 + 20 + 5 * 8 + 4 + 32)
        + bytes(32)
    )
    root, again = consensus.ssz_static("minimal", FORK, "ExecutionPayloadBid", message)
    assert again == message
    version = state[VERSION_AT : VERSION_AT + 4]
    fork_data_root = _sha(version.ljust(32, b"\0") + state[ROOT_AT : ROOT_AT + 32])
    domain = DOMAIN_BEACON_BUILDER + fork_data_root[:28]
    signature = G2ProofOfPossession.Sign(key, _sha(root + domain))
    return struct.pack("<I", 4 + 96) + signature + message


def _validate(state: bytes, signed: bytes) -> str | None:
    """The rule that refuses a bid on the state, or None when the proposer accepts it."""
    return consensus.validate_bid(
        "minimal", FORK, state, _preferences(), PARENT_GAS_LIMIT, signed, FEE_RECIPIENT
    )


def _proposer(state: bytes) -> int:
    """The index of the proposer of the slot of the state."""
    index = 0
    while not consensus.is_proposer("minimal", FORK, state, index):
        index += 1
    return index


@pytest.mark.parametrize("parent_hash", [None, FULL_PARENT_HASH], ids=["empty", "full"])
def test_validate_bid(parent_hash: bytes | None):
    # A bid may build on the parent without its payload, or with it.
    state = _state()
    assert _validate(state, _signed_bid(state, parent_hash=parent_hash)) is None


def _previous_mix(state: bytes) -> bytes:
    """The RANDAO mix of the epoch before the current one."""
    at = _mix_at(state, _slot(state) // SLOTS_PER_EPOCH - 1)
    return state[at : at + 32]


@pytest.mark.parametrize(
    ("change", "expected"),
    [
        ({"later_slots": 1}, "wrong_slot"),
        ({"fee_recipient": bytes(20)}, "wrong_fee_recipient"),
        ({"parent_hash": b"\xcc" * 32}, "wrong_parent_hash"),
        ({"parent_root": b"\xcc" * 32}, "wrong_parent_root"),
        ({"prev_randao": b"\xcc" * 32}, "wrong_prev_randao"),
        ({"gas_limit": PARENT_GAS_LIMIT}, "incompatible_gas_limit"),
        ({"gas_limit": TARGET_GAS_LIMIT}, "incompatible_gas_limit"),
        ({"value": 2**63}, "cannot_cover_bid"),
        ({"key": SECRET_KEY + 1}, "bad_signature"),
    ],
    ids=lambda value: value if isinstance(value, str) else repr(value),
)
def test_validate_bid_refused(change: dict[str, Any], expected: str):
    state = _state()
    assert _validate(state, _signed_bid(state, **change)) == expected


def test_validate_bid_mix_of_the_previous_epoch():
    state = _state()
    signed = _signed_bid(state, prev_randao=_previous_mix(state))
    assert _validate(state, signed) == "wrong_prev_randao"


def test_validate_bid_of_positive_value():
    # The builder of the pinned state holds more than the minimum deposit and one Gwei.
    state = _state()
    assert _validate(state, _signed_bid(state, value=1)) is None


def _exiting_builder(state: bytes) -> bytes:
    """The state whose builder has a withdrawable epoch, so has started to exit."""
    at = state.index(PUBKEY) + WITHDRAWABLE_AFTER_KEY
    return state[:at] + struct.pack("<Q", 5) + state[at + 8 :]


def test_validate_bid_of_an_inactive_builder():
    state = _exiting_builder(_state())
    assert _validate(state, _signed_bid(state)) == "inactive_builder"


@pytest.mark.parametrize(
    ("first", "second", "expected"),
    [
        ("inactive", {"later_slots": 1}, "inactive_builder"),
        ({"later_slots": 1}, {"fee_recipient": bytes(20)}, "wrong_slot"),
        ({"fee_recipient": bytes(20)}, {"parent_hash": b"\xcc" * 32}, "wrong_fee_recipient"),
        ({"parent_hash": b"\xcc" * 32}, {"parent_root": b"\xcc" * 32}, "wrong_parent_hash"),
        ({"parent_root": b"\xcc" * 32}, {"prev_randao": b"\xcc" * 32}, "wrong_parent_root"),
        ({"prev_randao": b"\xcc" * 32}, {"gas_limit": PARENT_GAS_LIMIT}, "wrong_prev_randao"),
        ({"gas_limit": PARENT_GAS_LIMIT}, {"value": 2**63}, "incompatible_gas_limit"),
        ({"value": 2**63}, {"key": SECRET_KEY + 1}, "cannot_cover_bid"),
    ],
    ids=lambda value: value if isinstance(value, str) else repr(value),
)
def test_validate_bid_rules_in_order(first: Any, second: dict[str, Any], expected: str):
    # When two neighbouring rules fail, the earlier one names the refusal.
    state = _state()
    if first == "inactive":
        state, first = _exiting_builder(state), {}
    assert _validate(state, _signed_bid(state, **first, **second)) == expected


def test_validate_bid_of_a_self_built_payload():
    # No builder sits at the index of a self-built payload, so the bid cannot be read.
    state = _state()
    signed = _signed_bid(state, builder_index=SELF_BUILD)
    message = (
        "EthLib.Consensus.TransitionError.accessor "
        f"(EthLib.Consensus.AccessorError.builderIndexOutOfRange {SELF_BUILD})"
    )
    with raises(TransitionError, message) as info:
        _validate(state, signed)
    assert info.value.code != 0


@pytest.mark.parametrize(
    ("preferences", "signed", "message"),
    [
        (b"", None, "preferences rejected: EthLib.Serialization.Ssz.Err.scope 76 0"),
        (None, b"", "bid rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 100 0"),
    ],
    ids=["preferences", "bid"],
)
def test_validate_bid_input_that_does_not_decode(
    preferences: bytes | None, signed: bytes | None, message: str
):
    state = _state()
    preferences = _preferences() if preferences is None else preferences
    signed = _signed_bid(state) if signed is None else signed
    with raises(TransitionError, message) as info:
        consensus.validate_bid(
            "minimal", FORK, state, preferences, PARENT_GAS_LIMIT, signed, FEE_RECIPIENT
        )
    assert info.value.code == 0


def test_is_eligible_for_bid_gloas():
    state = _state()
    proposer = _proposer(state)
    # The secret key of a validator of the consensus tests is its index plus one.
    pubkey = G2ProofOfPossession.SkToPk(proposer + 1)
    slot, parent_root = _slot(state), _parent_root(state)
    received = [_preferences(proposer)]

    def eligible(on: bytes = state, **change: Any) -> bool:
        args: dict[str, Any] = {
            "preferences": received,
            "slot": slot,
            "parent_hash": _empty_parent_hash(state),
            "parent_root": parent_root,
            "pubkey": pubkey,
        }
        return consensus.is_eligible_for_bid_gloas("minimal", FORK, on, **(args | change))

    assert eligible()
    assert eligible(parent_hash=FULL_PARENT_HASH)
    assert not eligible(slot=slot + 1)
    assert not eligible(pubkey=G2ProofOfPossession.SkToPk(proposer + 2))
    assert not eligible(preferences=[_preferences(proposer + 1)])
    assert not eligible(parent_hash=b"\xcc" * 32)
    assert not eligible(parent_root=b"\xcc" * 32)
    # The proposer exits at the current epoch, so it is no longer active.
    at = state.rindex(pubkey) + EXIT_AFTER_KEY
    epoch = struct.pack("<Q", slot // SLOTS_PER_EPOCH)
    assert not eligible(state[:at] + epoch + state[at + 8 :])


@pytest.mark.parametrize("fork", ["fusaka", "bellatrix"])
def test_no_gloas_bids_before_gloas(fork: str):
    with raises(TransitionError, f"no Gloas bids at {fork}") as info:
        consensus.validate_bid("minimal", fork, b"", b"", 0, b"", bytes(20))
    assert info.value.code == 0
    with raises(TransitionError, f"no Gloas bids at {fork}") as info:
        consensus.is_eligible_for_bid_gloas(
            "minimal", fork, b"", [], 0, bytes(32), bytes(32), bytes(48)
        )
    assert info.value.code == 0
