"""The snap capability, against hand-built messages and the block access lists of the fixtures."""

import json
from pathlib import Path

import pytest

from ethlib.cryptography import keccak
from ethlib.execution.network.snap import (
    ACCOUNT_RANGE,
    BLOCK_ACCESS_LISTS,
    BYTE_CODES,
    GET_ACCOUNT_RANGE,
    GET_BLOCK_ACCESS_LISTS,
    GET_BYTE_CODES,
    GET_STORAGE_RANGES,
    GET_TRIE_NODES,
    STORAGE_RANGES,
    TRIE_NODES,
    SnapError,
    access_lists_answer,
    codes_answer,
    decode_message,
    full_account,
)
from ethlib.serialization import rlp
from raising import raises

# The snap/2 forms come from caps/snap.md of ethereum/devp2p at its pin.
# The trie node messages are those of snap/1, whose text EthLib/Execution/Network/Snap.lean cites.
# The pinned file records only their removal by snap/2.
# The access lists and their hashes come from tests/execution/blocks/block_access_lists.json.

_BALS = Path(__file__).resolve().parents[4] / "tests/execution/blocks/block_access_lists.json"


def _distinct_valid(cases: list) -> list:
    """The first three valid access lists with distinct hashes."""
    seen, kept = set(), []
    for case in cases:
        if case["error"] is None and case["hash"] not in seen:
            seen.add(case["hash"])
            kept.append(case)
    return kept[:3]


BALS = _distinct_valid(json.loads(_BALS.read_text()))

EMPTY_ROOT = keccak.keccak256(b"\x80")
EMPTY_CODE = keccak.keccak256(b"")


def _p(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


H = [bytes([i]) * 32 for i in range(1, 4)]
ACCOUNT = rlp.encode([_p(1), _p(10), b"", b""])
PROOF = [b"\xc0", b"\xc1\x80"]

COMMON = [
    (GET_ACCOUNT_RANGE, rlp.encode([_p(7), H[0], H[1], H[2], _p(500_000)])),
    (ACCOUNT_RANGE, rlp.encode([_p(7), [[H[0], ACCOUNT], [H[1], ACCOUNT]], PROOF])),
    (GET_STORAGE_RANGES, rlp.encode([_p(7), H[0], [H[1], H[2]], b"", b"", _p(500_000)])),
    (STORAGE_RANGES, rlp.encode([_p(7), [[[H[0], b"\x01"]], []], PROOF])),
    (GET_BYTE_CODES, rlp.encode([_p(7), H, _p(500_000)])),
    (BYTE_CODES, rlp.encode([_p(7), [b"\x60\x00", b""]])),
]
SNAP1 = [
    (GET_TRIE_NODES, rlp.encode([_p(7), H[0], [[b"\x01"], [H[1], b"\x02"]], _p(500_000)])),
    (TRIE_NODES, rlp.encode([_p(7), [b"\xc0"]])),
]
SNAP2 = [
    (GET_BLOCK_ACCESS_LISTS, rlp.encode([_p(7), H, _p(2_000_000)])),
    (BLOCK_ACCESS_LISTS, rlp.encode([_p(7), [rlp.decode(bytes.fromhex(BALS[0]["bal"])), b""]])),
]


@pytest.mark.parametrize("message_id, data", COMMON + SNAP1)
def test_snap1_round_trip(message_id: int, data: bytes) -> None:
    assert decode_message(1, message_id, data) == data


@pytest.mark.parametrize("message_id, data", COMMON + SNAP2)
def test_snap2_round_trip(message_id: int, data: bytes) -> None:
    assert decode_message(2, message_id, data) == data


@pytest.mark.parametrize(
    "version, message_id, data",
    [(2, m, d) for m, d in SNAP1] + [(1, m, d) for m, d in SNAP2] + [(2, 0x0A, rlp.encode([]))],
)
def test_ids_of_the_other_version(version: int, message_id: int, data: bytes) -> None:
    with raises(SnapError, f"message ID {message_id} is not used by this snap version") as info:
        decode_message(version, message_id, data)
    assert info.value.code == 1


def test_full_account() -> None:
    # The slim form writes the root of the empty trie and the hash of empty code as empty strings.
    assert full_account(ACCOUNT) == rlp.encode([_p(1), _p(10), EMPTY_ROOT, EMPTY_CODE])
    full = rlp.encode([_p(1), _p(10), H[0], H[1]])
    assert full_account(full) == full


CODES = [b"\x60\x00", b"\x60\x01", b"\x60\x02"]
CODE_HASHES = [keccak.keccak256(c) for c in CODES]


@pytest.mark.parametrize(
    "codes, request_id, accepted",
    [
        (CODES, 7, True),
        # The peer skips codes it does not have, and keeps the order.
        ([CODES[0], CODES[2]], 7, True),
        ([], 7, True),
        ([CODES[1], CODES[0]], 7, False),
        ([b"\x00"], 7, False),
        (CODES, 8, False),
    ],
)
def test_codes_answer(codes: list[bytes], request_id: int, accepted: bool) -> None:
    request = rlp.encode([_p(7), CODE_HASHES, _p(500_000)])
    response = rlp.encode([_p(request_id), codes])
    assert codes_answer(2, request, response) is accepted


def _bal(case) -> list:
    return rlp.decode(bytes.fromhex(case["bal"]))


def test_fixture_hashes() -> None:
    # Each access list hashes to the hash its fixture gives.
    for case in BALS:
        assert keccak.keccak256(bytes.fromhex(case["bal"])) == bytes.fromhex(case["hash"])


@pytest.mark.parametrize(
    "lists, accepted",
    [
        ([_bal(c) for c in BALS], True),
        # A list the peer does not have is the empty string, in its position.
        ([_bal(BALS[0]), b"", _bal(BALS[2])], True),
        # The peer may cut the tail.
        ([_bal(BALS[0])], True),
        # A list in the wrong position.
        ([_bal(BALS[1]), _bal(BALS[0])], False),
        # More lists than requested blocks.
        ([_bal(c) for c in BALS] + [b""], False),
    ],
)
def test_access_lists_answer(lists: list, accepted: bool) -> None:
    hashes = [bytes.fromhex(c["hash"]) for c in BALS]
    request = rlp.encode([_p(7), H, _p(2_000_000)])
    response = rlp.encode([_p(7), lists])
    assert access_lists_answer(request, response, hashes) is accepted
