"""The decoder of engine_getPayload results, against the OpenRPC examples of `tests/engine`."""

# Rules: ethereum/execution-apis, src/engine/{paris,shanghai,cancun,prague,osaka,amsterdam}.md.
# Commit: 3284ee80c3da3e516c53782dde75157cccf1ebdc.

import copy
import json
from pathlib import Path
from typing import Any

import pytest

from ethlib import engine
from raising import raises

_DIR = Path(__file__).resolve().parents[4] / "tests" / "engine"
CASES = [
    case
    for case in json.loads((_DIR / "openrpc.json").read_text())
    if case["method"].startswith("engine_getPayloadV")
]
EXAMPLES = {case["method"]: case["result"] for case in CASES}

_INVALID = "engine error: EthLib.Engine.EngineError.invalidParams "

# A fork that each of versions 1 to 5 serves, chosen to match the fields of its example.
FORKS = {
    "engine_getPayloadV1": "paris",
    "engine_getPayloadV2": "shapella",
    "engine_getPayloadV3": "dencun",
    "engine_getPayloadV4": "pectra",
    "engine_getPayloadV5": "fusaka",
}


def _example(method: str) -> dict[str, Any]:
    return copy.deepcopy(EXAMPLES[method])


def test_example_count() -> None:
    """The OpenRPC file has one result example for each of the six versions, in order."""
    assert [c["method"] for c in CASES] == [f"engine_getPayloadV{v}" for v in range(1, 7)]


@pytest.mark.parametrize(("method", "fork"), FORKS.items())
def test_example(method: str, fork: str) -> None:
    """Each result example of versions 1 to 5 decodes at its fork and is written back unchanged."""
    result = EXAMPLES[method]
    assert engine.read_get_payload_result(method, fork, result) == result


def test_example_v6_rejected() -> None:
    """The example of version 6 at the pin has no slot number, which version 4 payloads require."""
    with raises(engine.EngineError, _INVALID + '"payload: not the fields of version 4"') as error:
        engine.read_get_payload_result(
            "engine_getPayloadV6", "glamsterdam", EXAMPLES["engine_getPayloadV6"]
        )
    assert error.value.code == 32602


def _result_v6() -> dict[str, Any]:
    # The example of version 5 with the two fields of a version 4 payload is a valid result.
    result = _example("engine_getPayloadV5")
    result["executionPayload"]["blockAccessList"] = "0xc0"
    result["executionPayload"]["slotNumber"] = "0x1"
    return result


def test_result_v6() -> None:
    """A result of version 6 with a slot number decodes at Glamsterdam and is written back."""
    result = _result_v6()
    assert engine.read_get_payload_result("engine_getPayloadV6", "glamsterdam", result) == result


def test_canonical_form() -> None:
    """An address in mixed case decodes, and the writer writes it in lowercase."""
    result = _example("engine_getPayloadV2")
    address = result["executionPayload"]["feeRecipient"]
    result["executionPayload"]["feeRecipient"] = "0x" + address[2:].upper()
    written = engine.read_get_payload_result("engine_getPayloadV2", "shapella", result)
    assert written == EXAMPLES["engine_getPayloadV2"]


def test_bundle_v1_proof_count() -> None:
    """A bundle of version 1 with two proofs for one blob breaks its length rule."""
    result = _example("engine_getPayloadV3")
    bundle = result["blobsBundle"]
    bundle["proofs"] = bundle["proofs"] * 2
    with raises(engine.EngineError, _INVALID + '"blobsBundle: lengths do not match"'):
        engine.read_get_payload_result("engine_getPayloadV3", "dencun", result)


@pytest.mark.parametrize("count", [127, 129])
def test_bundle_v2_proof_count(count: int) -> None:
    """A bundle of version 2 needs 128 proofs per blob, so 127 or 129 break its length rule."""
    result = _example("engine_getPayloadV5")
    proofs = result["blobsBundle"]["proofs"]
    assert len(proofs) == 128
    result["blobsBundle"]["proofs"] = (proofs * 2)[:count]
    with raises(engine.EngineError, _INVALID + '"blobsBundle: lengths do not match"'):
        engine.read_get_payload_result("engine_getPayloadV5", "fusaka", result)


def test_bundle_v1_proofs_at_v5() -> None:
    """One proof per blob, the rule of version 1, breaks the rule of version 2."""
    result = _example("engine_getPayloadV5")
    result["blobsBundle"]["proofs"] = result["blobsBundle"]["proofs"][:1]
    with raises(engine.EngineError, _INVALID + '"blobsBundle: lengths do not match"'):
        engine.read_get_payload_result("engine_getPayloadV5", "fusaka", result)


def test_bundle_commitment_count() -> None:
    """A bundle with two commitments for one blob breaks the length rule."""
    result = _example("engine_getPayloadV4")
    bundle = result["blobsBundle"]
    bundle["commitments"] = bundle["commitments"] * 2
    bundle["proofs"] = bundle["proofs"] * 2
    with raises(engine.EngineError, _INVALID + '"blobsBundle: lengths do not match"'):
        engine.read_get_payload_result("engine_getPayloadV4", "pectra", result)


@pytest.mark.parametrize(
    ("key", "size", "message"),
    [
        ("commitments", 47, '"commitment: 47 bytes, not 48"'),
        ("proofs", 49, '"proof: 49 bytes, not 48"'),
        ("blobs", 131071, '"blob: 131071 bytes, not 131072"'),
    ],
)
def test_bundle_item_size(key: str, size: int, message: str) -> None:
    """A commitment or a proof has 48 bytes, and a blob 131072."""
    result = _example("engine_getPayloadV3")
    result["blobsBundle"][key] = ["0x" + "00" * size]
    with raises(engine.EngineError, _INVALID + message):
        engine.read_get_payload_result("engine_getPayloadV3", "dencun", result)


@pytest.mark.parametrize(
    ("method", "fork"),
    [
        ("engine_getPayloadV1", "shapella"),
        ("engine_getPayloadV3", "pectra"),
        ("engine_getPayloadV4", "dencun"),
        ("engine_getPayloadV5", "glamsterdam"),
    ],
)
def test_fork_not_served(method: str, fork: str) -> None:
    """A version reads no result at a fork that it does not serve."""
    version = method.removeprefix("engine_getPayloadV")
    message = _INVALID + f'"result: version {version} does not serve the fork"'
    with raises(engine.EngineError, message):
        engine.read_get_payload_result(method, fork, EXAMPLES[method])


@pytest.mark.parametrize(
    ("method", "fork", "key"),
    [
        ("engine_getPayloadV2", "shapella", "blockValue"),
        ("engine_getPayloadV3", "dencun", "shouldOverrideBuilder"),
        ("engine_getPayloadV4", "pectra", "executionRequests"),
    ],
)
def test_missing_field(method: str, fork: str, key: str) -> None:
    """A result without a field of its version does not decode."""
    result = _example(method)
    del result[key]
    with raises(engine.EngineError, _INVALID + '"result: not the fields of its version"'):
        engine.read_get_payload_result(method, fork, result)


def test_extra_field() -> None:
    """A result of version 3 with the requests of version 4 does not decode."""
    result = _example("engine_getPayloadV3")
    result["executionRequests"] = []
    with raises(engine.EngineError, _INVALID + '"result: not the fields of its version"'):
        engine.read_get_payload_result("engine_getPayloadV3", "dencun", result)


def test_override_not_boolean() -> None:
    """The override flag is a JSON boolean, not a string."""
    result = _example("engine_getPayloadV3")
    result["shouldOverrideBuilder"] = "false"
    with raises(engine.EngineError, _INVALID + '"shouldOverrideBuilder: not a boolean"'):
        engine.read_get_payload_result("engine_getPayloadV3", "dencun", result)


def test_requests_out_of_order() -> None:
    """Execution requests whose types do not increase do not decode."""
    result = _example("engine_getPayloadV4")
    result["executionRequests"].reverse()
    with raises(engine.EngineError, _INVALID + '"executionRequests: out of order or too short"'):
        engine.read_get_payload_result("engine_getPayloadV4", "pectra", result)


def test_payload_of_wrong_fork() -> None:
    """Version 2 at Paris reads a payload of version 1, so withdrawals do not decode."""
    with raises(engine.EngineError, _INVALID + '"withdrawals: present before its fork"'):
        engine.read_get_payload_result(
            "engine_getPayloadV2", "paris", EXAMPLES["engine_getPayloadV2"]
        )


def test_block_value_leading_zero() -> None:
    """A block value with a leading zero is not a quantity."""
    result = _example("engine_getPayloadV2")
    result["blockValue"] = "0x01"
    with raises(engine.EngineError, _INVALID + '"blockValue: leading zero"'):
        engine.read_get_payload_result("engine_getPayloadV2", "shapella", result)


def test_requests_too_short() -> None:
    """An execution request of one byte has a type and no data, so it does not decode."""
    result = _example("engine_getPayloadV4")
    result["executionRequests"] = ["0x00"]
    with raises(engine.EngineError, _INVALID + '"executionRequests: out of order or too short"'):
        engine.read_get_payload_result("engine_getPayloadV4", "pectra", result)


def test_bundle_fields() -> None:
    """A bundle without its commitments is not a bundle."""
    result = _example("engine_getPayloadV3")
    del result["blobsBundle"]["commitments"]
    with raises(engine.EngineError, _INVALID + '"blobsBundle: not the fields of a bundle"'):
        engine.read_get_payload_result("engine_getPayloadV3", "dencun", result)


@pytest.mark.parametrize(
    ("method", "fork", "message"),
    [
        ("engine_getPayloadV7", "glamsterdam", "no method engine_getPayloadV7"),
        ("engine_newPayloadV1", "paris", "no method engine_newPayloadV1"),
        ("engine_getPayloadV1", "hegota", "fork hegota not yet specified"),
    ],
)
def test_unknown_method_or_fork(method: str, fork: str, message: str) -> None:
    """A method other than a version of engine_getPayload, or a fork after Glamsterdam, gives 0."""
    with raises(engine.EngineError, message) as error:
        engine.read_get_payload_result(method, fork, EXAMPLES["engine_getPayloadV1"])
    assert error.value.code == 0
