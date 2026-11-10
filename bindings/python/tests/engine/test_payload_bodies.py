"""The answers of engine_getPayloadBodiesByHash and ByRange, versions 1 and 2."""

from typing import Any

import pytest

from ethlib import engine
from raising import raises


def _hash(n: int) -> bytes:
    return bytes([2]) + n.to_bytes(31, "big")


def _hex(data: bytes) -> str:
    return "0x" + data.hex()


def _tx(n: int) -> bytes:
    return bytes([2, n, n])


ADDRESS = bytes(range(20))
WITHDRAWAL: engine.WithdrawalEntry = (7, 300, ADDRESS, 32_000_000_000)
WITHDRAWAL_JSON = {
    "index": "0x7",
    "validatorIndex": "0x12c",
    "address": _hex(ADDRESS),
    "amount": "0x773594000",
}
ACCESS_LIST = bytes([0xC0])

# The canonical chain holds blocks 1, 3, 4 and 5, and lacks block 2, as if pruned.
# Block 1 is before Shapella, block 3 from Shapella, and blocks 4 and 5 from Glamsterdam.
# Block 5 is the latest known block; the node pruned the access list of block 4.
# Block 9 sits on a side branch, so the node serves it by hash alone.
STORE: list[engine.BodyEntry] = [
    (_hash(1), 1, "paris", [_tx(1)], None, None),
    (_hash(3), 3, "shapella", [_tx(3)], [WITHDRAWAL], None),
    (_hash(4), 4, "glamsterdam", [], [], None),
    (_hash(5), 5, "glamsterdam", [_tx(5)], [WITHDRAWAL], ACCESS_LIST),
    (_hash(9), None, "dencun", [_tx(9)], [], None),
]
LATEST = 5

B1 = {"transactions": [_hex(_tx(1))], "withdrawals": None}
B3 = {"transactions": [_hex(_tx(3))], "withdrawals": [WITHDRAWAL_JSON]}
B4 = {"transactions": [], "withdrawals": []}
B5 = {"transactions": [_hex(_tx(5))], "withdrawals": [WITHDRAWAL_JSON]}
B9 = {"transactions": [_hex(_tx(9))], "withdrawals": []}


def _range(
    version: int, start: int, count: int, *, max_request: int = 32
) -> list[dict[str, Any] | None]:
    method = f"engine_getPayloadBodiesByRangeV{version}"
    params = [hex(start), hex(count)]
    return engine.get_payload_bodies(STORE, LATEST, method, params, max_request=max_request)


def _by_hash(
    version: int, hashes: list[bytes], *, max_request: int = 32
) -> list[dict[str, Any] | None]:
    method = f"engine_getPayloadBodiesByHashV{version}"
    params = [[_hex(h) for h in hashes]]
    return engine.get_payload_bodies(STORE, LATEST, method, params, max_request=max_request)


def test_range_trims_past_latest() -> None:
    """A range keeps null below the latest known block, and stops at it."""
    assert _range(1, 1, 8) == [B1, None, B3, B4, B5]


def test_range_inside_chain() -> None:
    """A range below the latest known block has count entries, null where a block is missing."""
    assert _range(1, 2, 2) == [None, B3]
    assert _range(1, 2, 1) == [None]


def test_range_past_latest() -> None:
    """A range past the latest known block is empty, and one from it holds that block alone."""
    assert _range(1, 6, 4) == []
    assert _range(1, LATEST, 3) == [B5]


def test_by_hash_order_and_null() -> None:
    """By hash, the answer keeps the order of the request, with null for an unknown block."""
    assert _by_hash(1, [_hash(3), _hash(2), _hash(1), _hash(9)]) == [B3, None, B1, B9]


def test_by_hash_empty() -> None:
    """A request for no hash has an empty answer."""
    assert _by_hash(2, []) == []


def test_v2_access_list() -> None:
    """Version 2 holds the access list, null before Glamsterdam or when it was pruned."""
    expected = [
        B1 | {"blockAccessList": None},
        None,
        B3 | {"blockAccessList": None},
        B4 | {"blockAccessList": None},
        B5 | {"blockAccessList": _hex(ACCESS_LIST)},
    ]
    assert _range(2, 1, 5) == expected
    assert _by_hash(2, [_hash(5), _hash(9)]) == [expected[4], B9 | {"blockAccessList": None}]


@pytest.mark.parametrize(
    ("start", "count", "message"),
    [(0, 1, "start: below 1"), (1, 0, "count: below 1"), (0, 1000, "start: below 1")],
)
def test_range_below_one(start: int, count: int, message: str) -> None:
    """A start or a count below 1 is invalid, and is checked before the size of the request."""
    with raises(
        engine.EngineError, f'engine error: EthLib.Engine.EngineError.invalidParams "{message}"'
    ) as e:
        _range(1, start, count)
    assert e.value.code == 32602


@pytest.mark.parametrize("version", [1, 2])
def test_request_limit(version: int) -> None:
    """A request above the limit is too large, and a request of 32 bodies never is."""
    with raises(engine.EngineError, "engine error: EthLib.Engine.EngineError.tooLargeRequest") as e:
        _range(version, 1, 33)
    assert e.value.code == 38004
    with raises(engine.EngineError, "engine error: EthLib.Engine.EngineError.tooLargeRequest") as e:
        _by_hash(version, [_hash(1)] * 33)
    assert e.value.code == 38004
    assert len(_range(version, 1, 32)) == LATEST
    assert len(_by_hash(version, [_hash(1)] * 32)) == 32
    assert len(_range(version, 1, 33, max_request=33)) == LATEST
    assert len(_by_hash(version, [_hash(1)] * 33, max_request=33)) == 33


@pytest.mark.parametrize(
    ("method", "params", "message"),
    [
        ("engine_getPayloadBodiesByHashV1", [[], []], "params: got 2, expected 1"),
        ("engine_getPayloadBodiesByHashV2", [["0x01"]], "block hash: 1 bytes, not 32"),
        ("engine_getPayloadBodiesByHashV1", [_hex(_hash(1))], "hashes: not an array"),
        ("engine_getPayloadBodiesByRangeV1", ["0x1"], "params: got 1, expected 2"),
        ("engine_getPayloadBodiesByRangeV2", ["0x1", "0x01"], "count: leading zero"),
        ("engine_getPayloadBodiesByRangeV1", ["0x1", "0x10000000000000000"], "count: above 2^64"),
    ],
)
def test_invalid_params(method: str, params: list, message: str) -> None:
    """The parameters are an array of 32-byte hashes, or a start and a count of 64 bits."""
    with raises(
        engine.EngineError, f'engine error: EthLib.Engine.EngineError.invalidParams "{message}"'
    ) as e:
        engine.get_payload_bodies(STORE, LATEST, method, params)
    assert e.value.code == 32602


def test_unknown_method() -> None:
    """A method other than versions 1 and 2 of the two calls is malformed input."""
    with raises(engine.EngineError, "no method engine_getPayloadBodiesByHashV3") as e:
        engine.get_payload_bodies(STORE, LATEST, "engine_getPayloadBodiesByHashV3", [[]])
    assert e.value.code == 0


@pytest.mark.parametrize(
    ("store", "latest", "message"),
    [
        ([(_hash(1), 1, "paris", [], [], None)], 1, "store: withdrawals: present before its fork"),
        ([(_hash(1), 1, "shapella", [], None, None)], 1, "store: withdrawals: absent at its fork"),
        (
            [(_hash(1), 1, "pectra", [], [], ACCESS_LIST)],
            1,
            "store: block access list: present before its fork",
        ),
        ([*STORE, STORE[0]], LATEST, "store: two entries with one block hash"),
        (
            [*STORE, (_hash(6), 5, "glamsterdam", [], [], None)],
            LATEST,
            "store: two canonical entries at a number",
        ),
        (STORE, 9, "store: no canonical entry at the latest known block 9"),
        (
            [(_hash(1), 1, "shapella", [], [(1, 2, bytes(19), 3)], None)],
            1,
            "expected 20 bytes, got 19",
        ),
        ([(b"\x01", 1, "paris", [], None, None)], 1, "expected 32 bytes, got 1"),
        ([(_hash(1), 1, "hegota", [], [], None)], 1, "fork hegota not yet specified"),
    ],
)
def test_malformed_store(store: list[engine.BodyEntry], latest: int, message: str) -> None:
    """A store whose entries break the rules of their fork, or of a chain, is malformed input."""
    with raises(engine.EngineError, message) as e:
        engine.get_payload_bodies(store, latest, "engine_getPayloadBodiesByHashV1", [[]])
    assert e.value.code == 0


def test_limit_below_32() -> None:
    """A node must take requests of 32 bodies, so a lower limit is malformed input."""
    with raises(engine.EngineError, "store: a limit of 31, below 32") as e:
        _by_hash(1, [], max_request=31)
    assert e.value.code == 0
