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
    """The file holds 78 valid payloads, 46 JSON-RPC errors and 43 invalid payloads."""
    kinds = Counter(
        check(c["network"], c["method"], c["params"], c["validationError"], c["errorCode"])
        for c in CASES
    )
    assert kinds == {"valid": 78, "error": 46, "invalid": 43}


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
    with raises(engine.EngineError, "no method engine_newPayloadV5") as error:
        engine.new_payload(config("Paris"), "engine_newPayloadV5", [])
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
