"""The checks of engine_newPayload against the engine blockchain tests of execution-specs."""

import json
from collections import Counter
from pathlib import Path

import pytest

from ethlib import engine
from raising import raises

from .cases import check, config

_FILE = Path(__file__).resolve().parents[4] / "tests" / "engine" / "new_payload.json"
CASES = json.loads(_FILE.read_text())


def _id(case: dict) -> str:
    return f"{case['network']}-{Path(case['file']).stem}-{case['test'][-50:]}-{case['payload']}"


@pytest.mark.parametrize("case", CASES, ids=_id)
def test_case(case: dict) -> None:
    check(
        case["network"], case["method"], case["params"], case["validationError"], case["errorCode"]
    )


def test_counts() -> None:
    """The file holds 90 valid payloads, 75 JSON-RPC errors and 82 invalid payloads."""
    kinds = Counter(
        check(c["network"], c["method"], c["params"], c["validationError"], c["errorCode"])
        for c in CASES
    )
    # A check before execution rejects 80 of the invalid payloads.
    # The 2 others are Amsterdam block access lists with accounts out of order, or one twice.
    # That is found when the block runs, so without the parent's state the payload is syncing.
    assert kinds == {"valid": 90, "error": 75, "invalid": 80, "execution": 2}


def test_wrong_version() -> None:
    """A version of the method rejects a payload of a fork that it does not take."""
    case = next(c for c in CASES if c["network"] == "Prague" and c["validationError"] is None)
    with raises(
        engine.EngineError, "engine error: EthLib.Engine.EngineError.unsupportedFork"
    ) as error:
        engine.new_payload(config("Prague"), "engine_newPayloadV3", case["params"][:3])
    assert error.value.code == 38005


def test_unknown_method() -> None:
    """A method that is not a version of engine_newPayload has code 0."""
    with raises(engine.EngineError, "no method engine_newPayloadV6") as error:
        engine.new_payload(config("Paris"), "engine_newPayloadV6", [])
    assert error.value.code == 0


def test_extra_data_above_32_bytes() -> None:
    """Extra data of 33 bytes does not have the type of the field, so it is an invalid parameter."""
    case = next(c for c in CASES if c["network"] == "Paris" and c["validationError"] is None)
    payload = dict(case["params"][0], extraData="0x" + "00" * 33)
    with raises(
        engine.EngineError,
        'engine error: EthLib.Engine.EngineError.invalidParams "extraData: 33 bytes, more than 32"',
    ) as error:
        engine.new_payload(config("Paris"), "engine_newPayloadV1", [payload])
    assert error.value.code == 32602


def _prague_v4() -> list:
    """The parameters of a valid payload of the network Prague, for engine_newPayloadV4."""
    case = next(c for c in CASES if c["network"] == "Prague" and c["validationError"] is None)
    return case["params"]


def test_v5_without_block_access_list() -> None:
    """Version 5 rejects a payload without its block access list as an invalid parameter."""
    with raises(
        engine.EngineError,
        "engine error: EthLib.Engine.EngineError.invalidParams "
        '"payload: not the fields of version 4"',
    ) as error:
        engine.new_payload(config("Amsterdam"), "engine_newPayloadV5", _prague_v4())
    assert error.value.code == 32602


def test_v5_before_amsterdam() -> None:
    """Version 5 rejects a payload of a fork before Amsterdam as an unsupported fork."""
    params = _prague_v4()
    payload = dict(params[0], blockAccessList="0xc0", slotNumber="0x0")
    with raises(
        engine.EngineError, "engine error: EthLib.Engine.EngineError.unsupportedFork"
    ) as error:
        engine.new_payload(config("Prague"), "engine_newPayloadV5", [payload, *params[1:]])
    assert error.value.code == 38005


def test_v4_at_amsterdam() -> None:
    """Version 4 rejects a payload of Amsterdam as an unsupported fork."""
    with raises(
        engine.EngineError, "engine error: EthLib.Engine.EngineError.unsupportedFork"
    ) as error:
        engine.new_payload(config("Amsterdam"), "engine_newPayloadV4", _prague_v4())
    assert error.value.code == 38005


@pytest.mark.parametrize("access_list", ["0x01", "0xc000", "0x"])
def test_v5_block_access_list_not_rlp(access_list: str) -> None:
    """A block access list that is not the RLP form of one makes the payload invalid."""
    # 0x01 is a byte string, 0xc000 an empty list with a trailing byte, and 0x no item at all.
    params = _prague_v4()
    payload = dict(params[0], blockAccessList=access_list, slotNumber="0x0")
    status = engine.new_payload(config("Amsterdam"), "engine_newPayloadV5", [payload, *params[1:]])
    assert status["status"] == "INVALID"
    assert status["latestValidHash"] is None
    assert status["validationError"] == "406: the block access list is not the RLP form of one"


def test_v5_without_slot_number() -> None:
    """Version 5 rejects a payload without its slot number as an invalid parameter."""
    params = _prague_v4()
    payload = dict(params[0], blockAccessList="0xc0")
    with raises(
        engine.EngineError,
        "engine error: EthLib.Engine.EngineError.invalidParams "
        '"payload: not the fields of version 4"',
    ) as error:
        engine.new_payload(config("Amsterdam"), "engine_newPayloadV5", [payload, *params[1:]])
    assert error.value.code == 32602
