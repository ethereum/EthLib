"""The transaction exchange of the eth capability.

The hashes come from the TransactionTests of ethereum/tests at the pin in tests/sources.toml.
The messages are built here as RLP, from caps/eth.md, EIP-2976, EIP-5793 and EIP-8070.
"""

import json
from pathlib import Path

import pytest

from ethlib.cryptography import keccak
from ethlib.execution.network import (
    GET_POOLED_TRANSACTIONS,
    NEW_POOLED_TRANSACTION_HASHES,
    POOLED_TRANSACTIONS,
    TRANSACTIONS,
    EthWireError,
    check_pooled,
    decode_message,
    wire_hash,
)
from ethlib.serialization import rlp
from raising import raises

FIXTURES = Path(__file__).resolve().parents[4] / "tests/execution/ethereum_tests/TransactionTests"


def _hashed_transactions() -> list[tuple[str, bytes, bytes]]:
    """Each fixture with a hash at some fork: its name, its bytes and its hash."""
    cases = []
    for path in sorted(FIXTURES.rglob("*.json")):
        for name, case in json.loads(path.read_text()).items():
            hashes = {r["hash"] for r in case["result"].values() if "hash" in r}
            if len(hashes) == 1:
                tx = bytes.fromhex(case["txbytes"][2:])
                cases.append((name, tx, bytes.fromhex(hashes.pop()[2:])))
    return cases


HASHED = _hashed_transactions()


def _item(tx: bytes) -> bytes:
    """The RLP item of a transaction on the wire: a legacy list as is, a typed one as bytes."""
    return tx if tx[0] >= 0xC0 else rlp.encode(tx)


def test_fixtures_found() -> None:
    assert len(HASHED) >= 50
    assert any(tx[0] < 0xC0 for _, tx, _ in HASHED)


@pytest.mark.parametrize("name, tx, tx_hash", HASHED, ids=[c[0] for c in HASHED])
def test_wire_hash(name: str, tx: bytes, tx_hash: bytes) -> None:
    assert wire_hash(_item(tx)) == tx_hash


def _p(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def test_blob_network_form_hash() -> None:
    # EIP-4844 "Networking": the network form hashes as the transaction without its blobs.
    body = [
        _p(1),
        b"",
        _p(1),
        _p(10),
        _p(21000),
        b"\x11" * 20,
        b"",
        b"",
        [],
        _p(1),
        [b"\x01" + bytes(31)],
        b"",
        _p(1),
        _p(1),
    ]
    canonical = b"\x03" + rlp.encode(body)
    # The network form of Fusaka, with blobs elided as eth/72 sends them.
    network = b"\x03" + rlp.encode([body, _p(1), [], [bytes(48)], [bytes(48)] * 128])
    assert wire_hash(rlp.encode(canonical)) == keccak.keccak256(canonical)
    assert wire_hash(rlp.encode(network)) == keccak.keccak256(canonical)


TXS = [_item(tx) for _, tx, _ in HASHED[:3]]
HASHES = [h for _, _, h in HASHED[:3]]


def _raw(items: list[bytes]) -> list:
    return [rlp.decode(item) for item in items]


@pytest.mark.parametrize("version", [68, 69, 70, 71, 72])
@pytest.mark.parametrize(
    "message_id, data",
    [
        (TRANSACTIONS, rlp.encode(_raw(TXS))),
        (GET_POOLED_TRANSACTIONS, rlp.encode([_p(9), HASHES])),
        (POOLED_TRANSACTIONS, rlp.encode([_p(9), _raw(TXS)])),
    ],
)
def test_round_trip(version: int, message_id: int, data: bytes) -> None:
    assert decode_message(version, message_id, data) == data


def _announcement(types: bytes, sizes: list[int], hashes: list[bytes], cells=None) -> bytes:
    fields = [types, [_p(s) for s in sizes], hashes]
    if cells is not None:
        fields.append(cells)
    return rlp.encode(fields)


@pytest.mark.parametrize("version", [68, 69, 70, 71])
def test_announcement_eth68(version: int) -> None:
    data = _announcement(b"\x00\x02\x03", [100, 120, 300], HASHES)
    assert decode_message(version, NEW_POOLED_TRANSACTION_HASHES, data) == data
    # The form of eth/72 has four fields.
    with raises(EthWireError, "message data is not RLP of the expected shape") as info:
        decode_message(
            version,
            NEW_POOLED_TRANSACTION_HASHES,
            _announcement(b"\x00\x02\x03", [100, 120, 300], HASHES, b""),
        )
    assert info.value.code == 2


@pytest.mark.parametrize("cells", [b"", b"\xff" * 16])
def test_announcement_eth72(cells: bytes) -> None:
    data = _announcement(b"\x00\x02\x03", [100, 120, 300], HASHES, cells)
    assert decode_message(72, NEW_POOLED_TRANSACTION_HASHES, data) == data


@pytest.mark.parametrize(
    "version, data, code, message",
    [
        # Two types for three hashes.
        (
            68,
            _announcement(b"\x00\x02", [100, 120, 300], HASHES),
            3,
            "announcement has 2 types and 3 sizes for 3 hashes",
        ),
        # Two sizes for three hashes.
        (
            69,
            _announcement(b"\x00\x02\x03", [100, 120], HASHES),
            3,
            "announcement has 3 types and 2 sizes for 3 hashes",
        ),
        (
            72,
            _announcement(b"\x00\x02\x03", [100, 120], HASHES, b""),
            3,
            "announcement has 3 types and 2 sizes for 3 hashes",
        ),
        # Cells of 15 bytes.
        (
            72,
            _announcement(b"\x00\x02\x03", [100, 120, 300], HASHES, b"\xff" * 15),
            2,
            "message data is not RLP of the expected shape",
        ),
        # eth/72 reads four fields.
        (
            72,
            _announcement(b"\x00\x02\x03", [100, 120, 300], HASHES),
            2,
            "message data is not RLP of the expected shape",
        ),
    ],
)
def test_announcement_refused(version: int, data: bytes, code: int, message: str) -> None:
    with raises(EthWireError, message) as info:
        decode_message(version, NEW_POOLED_TRANSACTION_HASHES, data)
    assert info.value.code == code


def _get(hashes: list[bytes], request_id: int = 9) -> bytes:
    return rlp.encode([_p(request_id), hashes])


def _pooled(items: list[bytes], request_id: int = 9) -> bytes:
    return rlp.encode([_p(request_id), _raw(items)])


@pytest.mark.parametrize(
    "response",
    [
        _pooled(TXS),
        # The peer may leave transactions out, but keeps the order.
        _pooled([TXS[0], TXS[2]]),
        _pooled([]),
    ],
)
def test_pooled_answer(response: bytes) -> None:
    check_pooled(69, _get(HASHES), response)


@pytest.mark.parametrize(
    "response, code, message",
    [
        # Out of order.
        (
            _pooled([TXS[1], TXS[0]]),
            302,
            "transactions are not requested ones in the order of the request",
        ),
        # A transaction that was not requested.
        (
            _pooled([_item(HASHED[3][1])]),
            302,
            "transactions are not requested ones in the order of the request",
        ),
        # Another request ID.
        (
            _pooled(TXS, request_id=10),
            303,
            "response is not PooledTransactions with the request ID of the request",
        ),
    ],
)
def test_pooled_refused(response: bytes, code: int, message: str) -> None:
    with raises(EthWireError, message) as info:
        check_pooled(69, _get(HASHES), response)
    assert info.value.code == code
