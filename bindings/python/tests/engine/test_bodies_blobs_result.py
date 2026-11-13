"""The decoders of engine_getPayloadBodies and engine_getBlobs results, on the OpenRPC examples."""

# Rules: ethereum/execution-apis, src/engine/{shanghai,cancun,osaka,amsterdam}.md.
# Commit: 3284ee80c3da3e516c53782dde75157cccf1ebdc.

import copy
import json
from collections.abc import Callable
from pathlib import Path
from typing import Any

import pytest

from ethlib import engine
from raising import raises

_DIR = Path(__file__).resolve().parents[4] / "tests" / "engine"
_CASES = json.loads((_DIR / "openrpc.json").read_text())
BODIES = {
    case["method"]: case["result"]
    for case in _CASES
    if case["method"].startswith("engine_getPayloadBodies")
}
BLOBS = {
    case["method"]: case["result"]
    for case in _CASES
    if case["method"].startswith("engine_getBlobsV")
}

_INVALID = "engine error: EthLib.Engine.EngineError.invalidParams "


def _invalid(reason: str) -> str:
    return _INVALID + json.dumps(reason)


def _bodies(method: str) -> list[Any]:
    return copy.deepcopy(BODIES[method])


def _blobs(method: str) -> list[Any]:
    return copy.deepcopy(BLOBS[method])


def test_example_methods() -> None:
    """The OpenRPC file has one result example for each version of the two methods."""
    assert sorted(BODIES) == sorted(
        f"engine_getPayloadBodiesBy{kind}V{v}" for kind in ("Hash", "Range") for v in (1, 2)
    )
    assert sorted(BLOBS) == [f"engine_getBlobsV{v}" for v in range(1, 5)]


@pytest.mark.parametrize("method", sorted(BODIES))
def test_bodies_example(method: str) -> None:
    """Each bodies example decodes and is written back unchanged."""
    result = BODIES[method]
    assert engine.read_payload_bodies_result(method, result) == result


@pytest.mark.parametrize("method", sorted(BLOBS))
def test_blobs_example(method: str) -> None:
    """Each blobs example decodes and is written back unchanged."""
    result = BLOBS[method]
    assert engine.read_get_blobs_result(method, result) == result


def test_blobs_v4_example_nulls() -> None:
    """The missing cell and the missing blob of the example of version 4 keep their positions."""
    written = engine.read_get_blobs_result("engine_getBlobsV4", BLOBS["engine_getBlobsV4"])
    assert written is not None
    assert written[1] is not None
    assert written[1]["blob_cells"][1] is None
    assert written[1]["proofs"][1] is None
    assert written[2] is None


def test_blobs_uppercase_hex() -> None:
    """A proof in uppercase hex is not data, whose digits are lowercase."""
    result = _blobs("engine_getBlobsV1")
    result[0]["proof"] = "0x" + result[0]["proof"][2:].upper()
    with raises(engine.EngineError, _invalid("proof: not a hex digit")):
        engine.read_get_blobs_result("engine_getBlobsV1", result)


def test_bodies_null_entry() -> None:
    """A `null` entry of a bodies answer stays at its position."""
    result = [None, *_bodies("engine_getPayloadBodiesByHashV1"), None]
    assert engine.read_payload_bodies_result("engine_getPayloadBodiesByHashV1", result) == result


def test_body_absent_field_is_null() -> None:
    """Absent withdrawals and access list read as `null`, and are written as `null`."""
    result = _bodies("engine_getPayloadBodiesByRangeV2")
    del result[0]["withdrawals"]
    del result[0]["blockAccessList"]
    written = engine.read_payload_bodies_result("engine_getPayloadBodiesByRangeV2", result)
    assert written[0] == {
        "transactions": result[0]["transactions"],
        "withdrawals": None,
        "blockAccessList": None,
    }


def test_body_v1_with_access_list() -> None:
    """A body of version 1 holds no block access list."""
    result = _bodies("engine_getPayloadBodiesByHashV2")
    with raises(engine.EngineError, _invalid("body: a field of no body of version 1")) as error:
        engine.read_payload_bodies_result("engine_getPayloadBodiesByHashV1", result)
    assert error.value.code == 32602


def test_body_without_transactions() -> None:
    """A body needs its transactions."""
    result = _bodies("engine_getPayloadBodiesByHashV1")
    del result[0]["transactions"]
    with raises(engine.EngineError, _invalid("body: no field transactions")):
        engine.read_payload_bodies_result("engine_getPayloadBodiesByHashV1", result)


def test_bodies_null_result() -> None:
    """A bodies answer is an array, never `null` alone."""
    with raises(engine.EngineError, _invalid("result: not an array")):
        engine.read_payload_bodies_result("engine_getPayloadBodiesByRangeV1", None)


@pytest.mark.parametrize("method", ["engine_getBlobsV2", "engine_getBlobsV3", "engine_getBlobsV4"])
def test_blobs_null_result(method: str) -> None:
    """From version 2, `null` alone is an answer."""
    assert engine.read_get_blobs_result(method, None) is None


def test_blobs_v1_null_entry() -> None:
    """A `null` entry of version 1 stays at its position."""
    result = [None, *_blobs("engine_getBlobsV1"), None]
    assert engine.read_get_blobs_result("engine_getBlobsV1", result) == result


@pytest.mark.parametrize("method", ["engine_getBlobsV1", "engine_getBlobsV3"])
def test_blob_size(method: str) -> None:
    """A blob has 131072 bytes."""
    result = _blobs(method)
    result[0]["blob"] = "0x" + "00" * 131071
    with raises(engine.EngineError, _invalid("blob: 131071 bytes, not 131072")):
        engine.read_get_blobs_result(method, result)


@pytest.mark.parametrize(
    ("method", "message"),
    [
        ("engine_getBlobsV1", "blobAndProof: not the fields of version 1"),
        ("engine_getBlobsV2", "blobAndProof: not the fields of version 2"),
        ("engine_getBlobsV4", "blobCells: not the fields of version 1"),
    ],
)
def test_blobs_extra_field(method: str, message: str) -> None:
    """An object of a blobs answer holds exactly its two fields."""
    result = _blobs(method)
    result[0]["extra"] = "0x"
    with raises(engine.EngineError, _invalid(message)):
        engine.read_get_blobs_result(method, result)


def test_blobs_v2_object_at_v1() -> None:
    """A blob with its cell proofs is not a blob and its proof of version 1."""
    result = _blobs("engine_getBlobsV2")
    with raises(engine.EngineError, _invalid("blobAndProof: not the fields of version 1")):
        engine.read_get_blobs_result("engine_getBlobsV1", result)


def test_body_v2_extra_field() -> None:
    """A body of version 2 holds no other field."""
    result = _bodies("engine_getPayloadBodiesByHashV2")
    result[0]["extra"] = "0x"
    with raises(engine.EngineError, _invalid("body: a field of no body of version 2")):
        engine.read_payload_bodies_result("engine_getPayloadBodiesByHashV2", result)


def test_blobs_v1_null_result() -> None:
    """Version 1 answers an array, never `null` alone."""
    with raises(engine.EngineError, _invalid("result: not an array")):
        engine.read_get_blobs_result("engine_getBlobsV1", None)


def test_blobs_v2_null_entry() -> None:
    """Version 2 has no `null` entry: a missing blob makes the whole answer `null`."""
    result = [*_blobs("engine_getBlobsV2"), None]
    with raises(engine.EngineError, _invalid("blobAndProof: not an object")):
        engine.read_get_blobs_result("engine_getBlobsV2", result)


@pytest.mark.parametrize("method", ["engine_getBlobsV2", "engine_getBlobsV3"])
@pytest.mark.parametrize("count", [127, 129])
def test_cell_proof_count(method: str, count: int) -> None:
    """A blob with its cell proofs needs exactly 128 proofs, one per cell."""
    result = _blobs(method)
    proofs = result[0]["proofs"]
    assert len(proofs) == 128
    result[0]["proofs"] = (proofs * 2)[:count]
    with raises(engine.EngineError, _invalid(f"proofs: {count}, not 128")):
        engine.read_get_blobs_result(method, result)


@pytest.mark.parametrize("method", ["engine_getBlobsV2", "engine_getBlobsV4"])
def test_cell_proof_size(method: str) -> None:
    """A proof of a cell has 48 bytes."""
    result = _blobs(method)
    result[0]["proofs"][0] = "0x" + "00" * 47
    with raises(engine.EngineError, _invalid("proof: 47 bytes, not 48")):
        engine.read_get_blobs_result(method, result)


def test_blobs_v1_proof_size() -> None:
    """A proof has 48 bytes."""
    result = _blobs("engine_getBlobsV1")
    result[0]["proof"] = "0x" + "00" * 47
    with raises(engine.EngineError, _invalid("proof: 47 bytes, not 48")):
        engine.read_get_blobs_result("engine_getBlobsV1", result)


def test_proof_without_cell() -> None:
    """A proof next to a `null` cell does not decode."""
    result = _blobs("engine_getBlobsV4")
    result[1]["proofs"][1] = result[1]["proofs"][0]
    with raises(engine.EngineError, _invalid("blobCells: a cell and its proof, one of them null")):
        engine.read_get_blobs_result("engine_getBlobsV4", result)


def test_cell_without_proof() -> None:
    """A cell next to a `null` proof does not decode."""
    result = _blobs("engine_getBlobsV4")
    result[1]["proofs"][0] = None
    with raises(engine.EngineError, _invalid("blobCells: a cell and its proof, one of them null")):
        engine.read_get_blobs_result("engine_getBlobsV4", result)


def test_cells_length_mismatch() -> None:
    """The cells and their proofs are two arrays of one length."""
    result = _blobs("engine_getBlobsV4")
    result[0]["proofs"].pop()
    with raises(engine.EngineError, _invalid("blobCells: arrays of two lengths")):
        engine.read_get_blobs_result("engine_getBlobsV4", result)


def test_cell_size() -> None:
    """A cell has 2048 bytes, the size of a cell of EIP-7594."""
    result = _blobs("engine_getBlobsV4")
    result[0]["blob_cells"][0] = "0x" + "00" * 2047
    with raises(engine.EngineError, _invalid("cell: 2047 bytes, not 2048")):
        engine.read_get_blobs_result("engine_getBlobsV4", result)


@pytest.mark.parametrize(
    ("read", "method"),
    [
        (engine.read_payload_bodies_result, "engine_getPayloadBodiesByHashV3"),
        (engine.read_get_blobs_result, "engine_getBlobsV5"),
        (engine.read_get_blobs_result, "engine_getPayloadBodiesByHashV1"),
    ],
)
def test_unknown_method(read: Callable[[str, Any], object], method: str) -> None:
    """A method name that the reader does not know has code 0."""
    with raises(engine.EngineError, f"no method {method}") as error:
        read(method, [])
    assert error.value.code == 0
