"""The block exchange of the eth capability, against hand-built messages.

The forms come from "Protocol Messages" and "Block Encoding and Validity" of caps/eth.md in
ethereum/devp2p at the pin, with the request ID of EIP-2481.
No official vectors exist, so each message and each header is built here as RLP.
"""

import pytest

from ethlib.cryptography import keccak
from ethlib.execution.network import (
    BLOCK_BODIES,
    BLOCK_HEADERS,
    GET_BLOCK_BODIES,
    GET_BLOCK_HEADERS,
    NEW_BLOCK,
    NEW_BLOCK_HASHES,
    EthWireError,
    check_headers,
    decode_message,
)
from ethlib.serialization import rlp


def _p(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _header(parent: bytes, number: int) -> list:
    # The fifteen fields of a Frontier header, with the parent hash first and the number ninth.
    return [
        parent,
        bytes(32),
        bytes(20),
        bytes(32),
        bytes(32),
        bytes(32),
        bytes(256),
        _p(131072),
        _p(number),
        _p(5000),
        b"",
        _p(number),
        b"",
        bytes(32),
        bytes(8),
    ]


def _hash(header: list) -> bytes:
    return keccak.keccak256(rlp.encode(header))


def _chain(first: int, count: int) -> list[list]:
    headers = [_header(b"\x11" * 32, first)]
    for number in range(first + 1, first + count):
        headers.append(_header(_hash(headers[-1]), number))
    return headers


CHAIN = _chain(100, 10)
REQUEST_ID = 7


def _get_headers(start, limit: int, skip: int, reverse: int, request_id: int = REQUEST_ID) -> bytes:
    start_item = start if isinstance(start, bytes) else _p(start)
    return rlp.encode([_p(request_id), [start_item, _p(limit), _p(skip), _p(reverse)]])


def _headers(headers: list[list], request_id: int = REQUEST_ID) -> bytes:
    return rlp.encode([_p(request_id), headers])


@pytest.mark.parametrize(
    "message_id, data",
    [
        (NEW_BLOCK_HASHES, rlp.encode([[_hash(CHAIN[0]), _p(100)], [_hash(CHAIN[1]), _p(101)]])),
        (GET_BLOCK_HEADERS, _get_headers(100, 3, 0, 0)),
        (GET_BLOCK_HEADERS, _get_headers(_hash(CHAIN[2]), 3, 1, 1)),
        (BLOCK_HEADERS, _headers(CHAIN[:3])),
        (GET_BLOCK_BODIES, rlp.encode([_p(REQUEST_ID), [_hash(h) for h in CHAIN[:2]]])),
        (BLOCK_BODIES, rlp.encode([_p(REQUEST_ID), [[[], []], [[], []]]])),
        (NEW_BLOCK, rlp.encode([[CHAIN[0], [], []], _p(17_179_869_184)])),
    ],
)
@pytest.mark.parametrize("version", [68, 69, 70, 71, 72])
def test_round_trip(version: int, message_id: int, data: bytes) -> None:
    assert decode_message(version, message_id, data) == data


@pytest.mark.parametrize(
    "message_id, data",
    [
        # A start block of 31 bytes: neither a hash nor a scalar below 2^64.
        (GET_BLOCK_HEADERS, _get_headers(bytes(range(1, 32)), 3, 0, 0)),
        # reverse is a flag, 0 or 1.
        (GET_BLOCK_HEADERS, _get_headers(100, 3, 0, 2)),
        # A request ID of 2^64 does not fit 64 bits.
        (GET_BLOCK_HEADERS, _get_headers(100, 3, 0, 0, request_id=2**64)),
        # No request ID.
        (GET_BLOCK_BODIES, rlp.encode([[_hash(CHAIN[0])]])),
        # An announcement with three fields.
        (NEW_BLOCK_HASHES, rlp.encode([[_hash(CHAIN[0]), _p(100), b""]])),
    ],
)
def test_malformed(message_id: int, data: bytes) -> None:
    with pytest.raises(EthWireError) as info:
        decode_message(69, message_id, data)
    assert info.value.code == 2


@pytest.mark.parametrize(
    "request_, response",
    [
        # Three headers from block 100, rising.
        (_get_headers(100, 3, 0, 0), _headers(CHAIN[:3])),
        # Fewer headers than the limit.
        (_get_headers(100, 5, 0, 0), _headers(CHAIN[:2])),
        # Falling from the hash of block 105.
        (_get_headers(_hash(CHAIN[5]), 3, 0, 1), _headers([CHAIN[5], CHAIN[4], CHAIN[3]])),
        # Every third block: skip 2.
        (_get_headers(100, 4, 2, 0), _headers([CHAIN[0], CHAIN[3], CHAIN[6], CHAIN[9]])),
        # No header at all.
        (_get_headers(100, 3, 0, 0), _headers([])),
    ],
)
def test_headers_answer(request_: bytes, response: bytes) -> None:
    check_headers(69, request_, response)


@pytest.mark.parametrize(
    "request_, response, code",
    [
        # More headers than the limit.
        (_get_headers(100, 2, 0, 0), _headers(CHAIN[:3]), 201),
        # The first header is not the start block.
        (_get_headers(101, 3, 0, 0), _headers(CHAIN[:3]), 203),
        (_get_headers(_hash(CHAIN[1]), 3, 0, 0), _headers(CHAIN[:3]), 203),
        # A gap of one block where none was asked.
        (_get_headers(100, 3, 0, 0), _headers([CHAIN[0], CHAIN[2]]), 204),
        # Rising where falling was asked.
        (_get_headers(100, 3, 0, 1), _headers(CHAIN[:2]), 204),
        # The right numbers, but block 101 does not have block 100 as its parent.
        (_get_headers(100, 2, 0, 0), _headers([CHAIN[0], _header(bytes(32), 101)]), 205),
        # Another request ID.
        (_get_headers(100, 3, 0, 0), _headers(CHAIN[:3], request_id=8), 206),
    ],
)
def test_headers_refused(request_: bytes, response: bytes, code: int) -> None:
    with pytest.raises(EthWireError) as info:
        check_headers(69, request_, response)
    assert info.value.code == code
