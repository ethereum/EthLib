"""The optimistic sync of Bellatrix against blocks built in the test."""

import struct

import pytest

from ethlib import consensus
from raising import raises

ERROR = consensus.ForkChoiceError
FORK = "bellatrix"
ZERO = bytes(32)

# The mainnet sizes of the fixed part of a Bellatrix payload, body and block.
PAYLOAD_FIXED = 32 + 20 + 32 + 32 + 256 + 32 + 8 * 4 + 4 + 32 + 32 + 4
BODY_FIXED = 96 + 72 + 32 + 5 * 4 + 64 + 96 + 4
BLOCK_FIXED = 8 + 8 + 32 + 32 + 4


def payload(block_number: int) -> bytes:
    """A payload whose fields are zero but its block number; number 0 gives the empty payload."""
    return (
        bytes(32 + 20 + 32 + 32 + 256 + 32)
        + struct.pack("<QQQQ", block_number, 0, 0, 0)
        + struct.pack("<I", PAYLOAD_FIXED)
        + bytes(32 + 32)
        + struct.pack("<I", PAYLOAD_FIXED)
    )


def block(slot: int, parent: bytes, block_number: int = 0) -> bytes:
    """A mainnet Bellatrix block of a slot on a parent, with an empty body but its payload."""
    body = bytes(96 + 72 + 32) + struct.pack("<I", BODY_FIXED) * 5 + bytes(64 + 96)
    body += struct.pack("<I", BODY_FIXED) + payload(block_number)
    head = struct.pack("<QQ", slot, 0) + parent + bytes(32) + struct.pack("<I", BLOCK_FIXED)
    return head + body


def root(data: bytes) -> bytes:
    """The root of a block, from the SSZ export, which also checks that the bytes decode."""
    found, again = consensus.ssz_static("mainnet", FORK, "BeaconBlock", data)
    assert again == data
    return found


# A genesis block g without payload, then a with a payload and b on it, and c on g.
G = block(1, ZERO)
A = block(2, root(G), 1)
B = block(3, root(A), 2)
C = block(3, root(G))
BLOCKS = [G, A, B, C]
RG, RA, RB, RC = (root(x) for x in BLOCKS)


def test_execution_block():
    assert not consensus.is_execution_block("mainnet", FORK, G)
    assert consensus.is_execution_block("mainnet", FORK, A)


@pytest.mark.parametrize(
    ("current_slot", "candidate", "expected"),
    [
        # The parent carries a payload, so the slot of the clock does not matter.
        (3, B, True),
        # The parent carries none: the block needs a slot at least 128 slots ago.
        (3 + 127, C, False),
        (3 + 128, C, True),
    ],
    ids=["parent payload", "too early", "far enough"],
)
def test_optimistic_candidate(current_slot: int, candidate: bytes, expected: bool):
    got = consensus.is_optimistic_candidate_block("mainnet", FORK, BLOCKS, current_slot, candidate)
    assert got is expected


def test_optimistic_candidate_with_another_number_of_slots():
    assert consensus.is_optimistic_candidate_block("mainnet", FORK, BLOCKS, 5, C, safe_slots=2)


@pytest.mark.parametrize(
    ("candidate", "code"),
    [(block(3, bytes([7]) * 32), 2), (block(2**64 - 1, RG), 7)],
    ids=["unknown parent", "overflow"],
)
def test_optimistic_candidate_rejected(candidate: bytes, code: int):
    with raises(ERROR, f"optimistic sync failed with code {code}") as info:
        consensus.is_optimistic_candidate_block("mainnet", FORK, BLOCKS, 0, candidate)
    assert info.value.code == code


@pytest.mark.parametrize(
    ("optimistic", "start", "expected"),
    [
        ([RA, RB], RB, RG),
        ([RA, RB], RG, RG),
        ([RA], RB, RB),
        # The walk stops at a block whose parent root is zero, optimistic or not.
        ([RG, RA, RB], RB, RG),
    ],
    ids=["two optimistic", "verified", "head verified", "genesis"],
)
def test_latest_verified_ancestor(optimistic: list, start: bytes, expected: bytes):
    assert (
        consensus.latest_verified_ancestor("mainnet", FORK, BLOCKS, optimistic, start) == expected
    )


def test_latest_verified_ancestor_rejected():
    orphan = block(4, bytes([7]) * 32)
    with raises(ERROR, "optimistic sync failed with code 2") as info:
        consensus.latest_verified_ancestor("mainnet", FORK, BLOCKS, [], bytes([9]) * 32)
    assert info.value.code == 2
    with raises(ERROR, "optimistic sync failed with code 2"):
        consensus.latest_verified_ancestor("mainnet", FORK, [orphan], [root(orphan)], root(orphan))


@pytest.mark.parametrize(
    ("valid", "expected"), [(RB, [RC]), (RA, [RB, RC]), (RC, [RA, RB])], ids=["b", "a", "c"]
)
def test_valid_payload(valid: bytes, expected: list):
    # The block and its ancestors leave the set.
    assert consensus.on_valid_payload("mainnet", FORK, BLOCKS, [RA, RB, RC], valid) == expected


@pytest.mark.parametrize(
    ("first", "expected"),
    [(RA, [RC]), (RB, [RA, RC]), (bytes([9]) * 32, [RA, RB, RC])],
    ids=["a", "b", "unknown"],
)
def test_invalidated_payload(first: bytes, expected: list):
    # The first invalid block and its descendants leave the set.
    assert (
        consensus.on_invalidated_payload("mainnet", FORK, BLOCKS, [RA, RB, RC], first) == expected
    )


def test_transitions_rejected():
    lower = block(1, RB)
    with raises(ERROR, "optimistic sync failed with code 6") as info:
        consensus.on_valid_payload("mainnet", FORK, [*BLOCKS, lower], [], root(lower))
    assert info.value.code == 6
    with raises(ERROR, "optimistic sync failed with code 2") as info:
        consensus.on_invalidated_payload("mainnet", FORK, BLOCKS, [bytes([9]) * 32], RA)
    assert info.value.code == 2


RESTRICTED = [0, 1, 5, 6, 7, 8, 9]


@pytest.mark.parametrize("kind", range(17))
def test_restricted_domains(kind: int):
    expected = kind in RESTRICTED
    assert consensus.is_optimistic_restricted_domain(bytes([kind, 0, 0, 0])) is expected


def test_restricted_domain_of_another_length():
    with raises(ERROR, "a domain type is 4 bytes, not 3") as info:
        consensus.is_optimistic_restricted_domain(bytes(3))
    assert info.value.code == 0


_EXPORTS = [
    lambda fork, data: consensus.is_execution_block("mainnet", fork, data),
    lambda fork, data: consensus.is_optimistic_candidate_block("mainnet", fork, [data], 0, data),
    lambda fork, data: consensus.latest_verified_ancestor("mainnet", fork, [data], [], ZERO),
    lambda fork, data: consensus.on_valid_payload("mainnet", fork, [data], [], ZERO),
    lambda fork, data: consensus.on_invalidated_payload("mainnet", fork, [data], [], ZERO),
]
_IDS = ["execution", "candidate", "ancestor", "valid", "invalidated"]


@pytest.mark.parametrize("call", _EXPORTS, ids=_IDS)
@pytest.mark.parametrize("fork", ["phase0", "altair", "glamsterdam"])
def test_no_optimistic_sync_outside_bellatrix_to_fulu(call, fork: str):
    with raises(ERROR, f"no optimistic sync at {fork}") as info:
        call(fork, G)
    assert info.value.code == 0


@pytest.mark.parametrize("call", _EXPORTS, ids=_IDS)
def test_block_that_does_not_decode(call):
    with raises(ERROR, "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 84 0") as info:
        call(FORK, b"")
    assert info.value.code == 0


def test_roots_of_another_length():
    with raises(ERROR, "a root is 32 bytes, not 31") as info:
        consensus.latest_verified_ancestor("mainnet", FORK, BLOCKS, [], bytes(31))
    assert info.value.code == 0
    with raises(ERROR, "a list of roots is 32 bytes each, not 33") as info:
        consensus.on_valid_payload("mainnet", FORK, BLOCKS, [bytes(33)], RA)
    assert info.value.code == 0
