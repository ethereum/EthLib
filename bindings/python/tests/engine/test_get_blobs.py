"""The answers of engine_getBlobs, versions 1 to 4, against the rules of the Engine API."""

import pytest

from ethlib import engine
from raising import raises

BLOB_SIZE = 131072
CELL_SIZE = 2048
CELLS = 128


def _hash(n: int) -> bytes:
    return bytes([1]) + n.to_bytes(31, "big")


def _hex(data: bytes) -> str:
    return "0x" + data.hex()


def _blob(n: int) -> bytes:
    return bytes([n]) * BLOB_SIZE


def _proof(n: int, cell: int) -> bytes:
    return bytes([n, cell]) * 24


def _cell(n: int, cell: int) -> bytes:
    return bytes([n, cell]) * (CELL_SIZE // 2)


def _cells(n: int, missing: frozenset[int] = frozenset()) -> list[tuple[bytes, bytes] | None]:
    return [None if i in missing else (_cell(n, i), _proof(n, i)) for i in range(CELLS)]


def _full(n: int) -> engine.PoolEntry:
    """A blob with its blob proof and all its cells, as a pool after Fusaka may hold it."""
    return (_hash(n), _blob(n), _proof(n, 255), _cells(n))


def _bitarray(*indices: int) -> str:
    """The 16 bytes whose bit i mod 8 of byte i / 8 is set for each index, as hex."""
    bits = bytearray(16)
    for i in indices:
        bits[i // 8] |= 1 << (i % 8)
    return _hex(bytes(bits))


A, B, C = 1, 2, 3
REQUEST = [_hex(_hash(A)), _hex(_hash(B)), _hex(_hash(C))]
# The pool holds A and C, and lacks B: the example of the source.
POOL = [_full(A), _full(C)]


def _v1(n: int) -> dict:
    return {"blob": _hex(_blob(n)), "proof": _hex(_proof(n, 255))}


def _v2(n: int) -> dict:
    return {"blob": _hex(_blob(n)), "proofs": [_hex(_proof(n, i)) for i in range(CELLS)]}


def test_v1_order_and_null() -> None:
    """Version 1 answers in the order of the request, with null for the missing blob."""
    answer = engine.get_blobs(POOL, "pectra", "engine_getBlobsV1", [REQUEST])
    assert answer == [_v1(A), None, _v1(C)]


def test_v1_not_serving() -> None:
    """A pool that does not serve answers null for every hash of version 1."""
    answer = engine.get_blobs(POOL, "dencun", "engine_getBlobsV1", [REQUEST], serving=False)
    assert answer == [None, None, None]


def test_v1_unsupported_from_fusaka() -> None:
    """From Fusaka, version 1 is an unsupported fork."""
    with raises(engine.EngineError, "engine error: EthLib.Engine.EngineError.unsupportedFork") as e:
        engine.get_blobs(POOL, "fusaka", "engine_getBlobsV1", [REQUEST])
    assert e.value.code == 38005


def test_v2_all_or_nothing() -> None:
    """Version 2 answers null when one blob is missing, and every blob otherwise."""
    assert engine.get_blobs(POOL, "fusaka", "engine_getBlobsV2", [REQUEST]) is None
    answer = engine.get_blobs(POOL, "fusaka", "engine_getBlobsV2", [[REQUEST[2], REQUEST[0]]])
    assert answer == [_v2(C), _v2(A)]


def test_v2_blob_proof_only() -> None:
    """A blob held with its blob proof alone has no cell proofs, so version 2 answers null."""
    pool = [(_hash(A), _blob(A), _proof(A, 255), None)]
    assert engine.get_blobs(pool, "fusaka", "engine_getBlobsV2", [[REQUEST[0]]]) is None


def test_v3_partial() -> None:
    """Version 3 answers null only in place of each missing blob."""
    answer = engine.get_blobs(POOL, "fusaka", "engine_getBlobsV3", [REQUEST])
    assert answer == [_v2(A), None, _v2(C)]
    assert engine.get_blobs([], "fusaka", "engine_getBlobsV3", [REQUEST]) == [None, None, None]


def test_v3_missing_cell() -> None:
    """A blob with a missing cell proof counts as missing for version 3."""
    pool = [(_hash(A), _blob(A), None, _cells(A, frozenset({7})))]
    assert engine.get_blobs(pool, "fusaka", "engine_getBlobsV3", [[REQUEST[0]]]) == [None]


@pytest.mark.parametrize("version", [2, 3, 4])
def test_not_serving(version: int) -> None:
    """From version 2, a pool that does not serve answers null alone."""
    params: list = [REQUEST] if version < 4 else [REQUEST, _bitarray(0)]
    method = f"engine_getBlobsV{version}"
    assert engine.get_blobs(POOL, "glamsterdam", method, params, serving=False) is None


def test_v4_selected_cells() -> None:
    """Version 4 answers the selected cells of each held blob, in order, with their proofs."""
    pool = [(_hash(A), None, None, _cells(A, frozenset({5}))), _full(C)]
    answer = engine.get_blobs(pool, "glamsterdam", "engine_getBlobsV4", [REQUEST, _bitarray(5, 0)])
    assert answer == [
        # Cell 5 of A is missing, so it and its proof are null.
        {"blob_cells": [_hex(_cell(A, 0)), None], "proofs": [_hex(_proof(A, 0)), None]},
        None,
        {
            "blob_cells": [_hex(_cell(C, 0)), _hex(_cell(C, 5))],
            "proofs": [_hex(_proof(C, 0)), _hex(_proof(C, 5))],
        },
    ]


def test_v4_last_cell() -> None:
    """Cell 127 is the top bit of the last byte of the bitarray."""
    answer = engine.get_blobs(
        [_full(A)], "glamsterdam", "engine_getBlobsV4", [[REQUEST[0]], "0x" + "00" * 15 + "80"]
    )
    assert answer == [{"blob_cells": [_hex(_cell(A, 127))], "proofs": [_hex(_proof(A, 127))]}]


def test_v4_holds_nothing() -> None:
    """An entry that holds no cell is a missing blob for version 4."""
    pool = [(_hash(A), None, None, None)]
    answer = engine.get_blobs(
        pool, "glamsterdam", "engine_getBlobsV4", [[REQUEST[0]], _bitarray(0)]
    )
    assert answer == [None]


def test_v4_blob_without_cells() -> None:
    """A blob held with only its blob proof has no cell, so version 4 counts it as missing."""
    pool = [(_hash(A), _blob(A), _proof(A, 255), None)]
    answer = engine.get_blobs(
        pool, "glamsterdam", "engine_getBlobsV4", [[REQUEST[0]], _bitarray(3)]
    )
    assert answer == [None]


def test_v4_no_cell_selected() -> None:
    """A bitarray with no bit set selects no cell of a held blob."""
    answer = engine.get_blobs(POOL, "glamsterdam", "engine_getBlobsV4", [REQUEST, _bitarray()])
    assert answer == [{"blob_cells": [], "proofs": []}, None, {"blob_cells": [], "proofs": []}]


def test_v4_bitarray_size() -> None:
    """A bitarray that is not 16 bytes is an invalid parameter."""
    with raises(
        engine.EngineError,
        'engine error: EthLib.Engine.EngineError.invalidParams "indices_bitarray: 2 bytes, not 16"',
    ) as e:
        engine.get_blobs(POOL, "glamsterdam", "engine_getBlobsV4", [REQUEST, "0x0001"])
    assert e.value.code == 32602


# The answer to a request that names A alone, for each version.
ANSWER_A = {1: _v1(A), 2: _v2(A), 3: _v2(A), 4: {"blob_cells": [], "proofs": []}}


def _params(version: int, hashes: list[str]) -> list:
    return [hashes] if version < 4 else [hashes, _bitarray()]


@pytest.mark.parametrize("version", [1, 2, 3, 4])
def test_request_limit(version: int) -> None:
    """A request above the limit is too large, and a request of 128 hashes never is."""
    # Versions 2 to 4 have no fork in the source, so Dencun suits all four versions.
    method = f"engine_getBlobsV{version}"
    with raises(engine.EngineError, "engine error: EthLib.Engine.EngineError.tooLargeRequest") as e:
        engine.get_blobs(POOL, "dencun", method, _params(version, [REQUEST[0]] * 129))
    assert e.value.code == 38004
    answer = engine.get_blobs(POOL, "dencun", method, _params(version, [REQUEST[0]] * 128))
    assert answer == [ANSWER_A[version]] * 128
    params = _params(version, [REQUEST[0]] * 129)
    answer = engine.get_blobs(POOL, "dencun", method, params, max_request=129)
    assert answer == [ANSWER_A[version]] * 129


def test_fork_before_size() -> None:
    """The fork of version 1 is checked before the size of the request."""
    with raises(engine.EngineError, "engine error: EthLib.Engine.EngineError.unsupportedFork") as e:
        engine.get_blobs(POOL, "fusaka", "engine_getBlobsV1", [[REQUEST[0]] * 200])
    assert e.value.code == 38005


@pytest.mark.parametrize(
    ("version", "params", "message"),
    [
        (1, [REQUEST, _bitarray(0)], "params: got 2, expected 1"),
        (4, [REQUEST], "params: got 1, expected 2"),
        (2, [["0x01"]], "versioned hash: 1 bytes, not 32"),
        (3, [REQUEST[0]], "hashes: not an array"),
    ],
)
def test_invalid_params(version: int, params: list, message: str) -> None:
    """The parameters are an array of 32-byte hashes, and from version 4 a bitarray."""
    with raises(
        engine.EngineError,
        f'engine error: EthLib.Engine.EngineError.invalidParams "{message}"',
    ) as e:
        engine.get_blobs(POOL, "dencun", f"engine_getBlobsV{version}", params)
    assert e.value.code == 32602


def test_unknown_method() -> None:
    """A method name of no version is malformed input."""
    with raises(engine.EngineError, "no method engine_getBlobsV5") as e:
        engine.get_blobs(POOL, "dencun", "engine_getBlobsV5", [REQUEST])
    assert e.value.code == 0


def test_blob_size() -> None:
    """A blob of the pool must have 131072 bytes."""
    pool = [(_hash(A), b"\x00" * 10, None, None)]
    with raises(engine.EngineError, "expected 131072 bytes, got 10") as e:
        engine.get_blobs(pool, "dencun", "engine_getBlobsV1", [REQUEST])
    assert e.value.code == 0


def test_cell_count() -> None:
    """The cells of an entry must number 128."""
    pool = [(_hash(A), None, None, _cells(A)[:127])]
    with raises(engine.EngineError, "pool: 127 cells, not 128") as e:
        engine.get_blobs(pool, "dencun", "engine_getBlobsV1", [REQUEST])
    assert e.value.code == 0


def test_limit_below_128() -> None:
    """A pool must take requests of 128 hashes, so a lower limit is malformed input."""
    with raises(engine.EngineError, "pool: a limit of 127, below 128") as e:
        engine.get_blobs(POOL, "dencun", "engine_getBlobsV1", [REQUEST], max_request=127)
    assert e.value.code == 0


def test_fork_not_specified() -> None:
    """The method is specified up to Glamsterdam, so a later fork is malformed input."""
    with raises(engine.EngineError, "fork hegota not yet specified") as e:
        engine.get_blobs(POOL, "hegota", "engine_getBlobsV4", [REQUEST, _bitarray(0)])
    assert e.value.code == 0


def test_duplicate_entry() -> None:
    """A pool holds each blob once, so two entries with one hash are malformed input."""
    with raises(engine.EngineError, "pool: two entries with one versioned hash") as e:
        engine.get_blobs([_full(A), _full(A)], "dencun", "engine_getBlobsV1", [REQUEST])
    assert e.value.code == 0
