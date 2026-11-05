"""The access list messages of eth/71 and the cell messages of eth/72.

The forms come from caps/eth.md of ethereum/devp2p at the pin.
The access lists and their hashes come from tests/execution/blocks/block_access_lists.json.
No official vectors exist for the messages, so each one is built here as RLP.
"""

import pytest

from ethlib.execution.network import (
    BLOCK_ACCESS_LISTS,
    CELLS,
    GET_BLOCK_ACCESS_LISTS,
    GET_CELLS,
    EthWireError,
    access_lists_answer,
    decode_message,
)
from ethlib.serialization import rlp
from raising import raises

from .test_snap import BALS


def _p(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


H = [bytes([i]) * 32 for i in range(1, 4)]
MASK = b"\xff" + bytes(15)
CELL = bytes(2048)

ACCESS_LISTS = [
    (GET_BLOCK_ACCESS_LISTS, rlp.encode([_p(3), H])),
    (BLOCK_ACCESS_LISTS, rlp.encode([_p(3), [rlp.decode(bytes.fromhex(BALS[0]["bal"])), b""]])),
]
CELL_MESSAGES = [
    (GET_CELLS, rlp.encode([_p(3), H[:2], MASK])),
    (CELLS, rlp.encode([_p(3), H[:1], [[CELL] * 8], MASK])),
]


@pytest.mark.parametrize("version", [71, 72])
@pytest.mark.parametrize("message_id, data", ACCESS_LISTS)
def test_access_list_messages(version: int, message_id: int, data: bytes) -> None:
    assert decode_message(version, message_id, data) == data


@pytest.mark.parametrize("message_id, data", CELL_MESSAGES)
def test_cell_messages(message_id: int, data: bytes) -> None:
    assert decode_message(72, message_id, data) == data


@pytest.mark.parametrize(
    "version, message_id, data",
    [(v, m, d) for v in (68, 69, 70) for m, d in ACCESS_LISTS]
    + [(v, m, d) for v in (68, 69, 70, 71) for m, d in CELL_MESSAGES],
)
def test_ids_of_later_versions(version: int, message_id: int, data: bytes) -> None:
    message = f"message ID {message_id} is not used by this eth version, or not read by EthLib yet"
    with raises(EthWireError, message) as info:
        decode_message(version, message_id, data)
    assert info.value.code == 1


def test_cell_mask_of_15_bytes() -> None:
    with raises(EthWireError, "message data is not RLP of the expected shape") as info:
        decode_message(72, GET_CELLS, rlp.encode([_p(3), H, MASK[:15]]))
    assert info.value.code == 2


def _bal(case) -> list:
    return rlp.decode(bytes.fromhex(case["bal"]))


@pytest.mark.parametrize(
    "lists, request_id, accepted",
    [
        ([_bal(c) for c in BALS], 3, True),
        ([_bal(BALS[0]), b"", _bal(BALS[2])], 3, True),
        # Each requested block has its entry, so a response cut at the tail is refused.
        ([_bal(BALS[0]), b""], 3, False),
        ([_bal(BALS[1])], 3, False),
        ([_bal(c) for c in BALS], 4, False),
    ],
)
def test_access_lists_answer(lists: list, request_id: int, accepted: bool) -> None:
    hashes = [bytes.fromhex(c["hash"]) for c in BALS]
    request = rlp.encode([_p(3), H])
    response = rlp.encode([_p(request_id), lists])
    assert access_lists_answer(71, request, response, hashes) is accepted
