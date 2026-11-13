"""The decoders of payload statuses and forkchoice responses, against `tests/engine`."""

import json
from pathlib import Path

import pytest

from ethlib import engine
from raising import raises

from .cases import config

_DIR = Path(__file__).resolve().parents[4] / "tests" / "engine"
PAYLOADS = json.loads((_DIR / "new_payload.json").read_text())
EXAMPLES = json.loads((_DIR / "openrpc.json").read_text())

STATUS_EXAMPLES = [c for c in EXAMPLES if c["method"].startswith("engine_newPayload")]
RESPONSE_EXAMPLES = [c for c in EXAMPLES if c["method"].startswith("engine_forkchoiceUpdated")]

_INVALID = "engine error: EthLib.Engine.EngineError.invalidParams "
_HASH = "0x" + "ab" * 32


def _data(value: str | None) -> bytes | None:
    return None if value is None else bytes.fromhex(value.removeprefix("0x"))


def _fields(status: dict) -> tuple[str, bytes | None, str | None]:
    # The fields of a status as the decoder returns them: a name, bytes or None, text or None.
    return (status["status"], _data(status["latestValidHash"]), status["validationError"])


def test_example_counts() -> None:
    """The OpenRPC file has 6 status examples of engine_newPayload and 3 forkchoice responses."""
    assert (len(STATUS_EXAMPLES), len(RESPONSE_EXAMPLES)) == (6, 3)


@pytest.mark.parametrize("case", STATUS_EXAMPLES, ids=lambda c: c["example"].replace(" ", "-"))
def test_status_example(case: dict) -> None:
    """Each payload status of an OpenRPC example decodes to its three fields."""
    assert engine.read_payload_status(case["result"]) == _fields(case["result"])


@pytest.mark.parametrize("case", RESPONSE_EXAMPLES, ids=lambda c: c["example"].replace(" ", "-"))
def test_response_example(case: dict) -> None:
    """Each forkchoice response of an OpenRPC example decodes to its status and its payload ID."""
    response = case["result"]
    assert engine.read_forkchoice_response(response) == (
        *_fields(response["payloadStatus"]),
        _data(response["payloadId"]),
    )


def _status_id(case: dict) -> str:
    return f"{case['network']}-{Path(case['file']).stem}-{case['test'][-50:]}-{case['payload']}"


@pytest.mark.parametrize("case", [c for c in PAYLOADS if c["errorCode"] is None], ids=_status_id)
def test_new_payload_status(case: dict) -> None:
    """The status of each fixture request of engine_newPayload without an error reads back."""
    status = engine.new_payload(config(case["network"]), case["method"], case["params"])
    assert engine.read_payload_status(status) == _fields(status)


def test_restricted_statuses() -> None:
    """A forkchoice response reads each of its three statuses, and an absent ID as None."""
    for name in ["VALID", "INVALID", "SYNCING"]:
        response = {
            "payloadStatus": {"status": name, "latestValidHash": _HASH, "validationError": "x"}
        }
        expected = (name, bytes.fromhex("ab" * 32), "x", None)
        assert engine.read_forkchoice_response(response) == expected


@pytest.mark.parametrize(
    ("response", "message"),
    [
        (
            {"payloadStatus": {"status": "VALID"}, "payloadId": None, "x": 1},
            _INVALID + '"forkchoiceUpdatedResponse: unknown field"',
        ),
        ({"payloadId": None}, _INVALID + '"forkchoiceUpdatedResponse: no field payloadStatus"'),
        (
            {"payloadStatus": {"status": "VALID"}, "payloadId": "0x" + "00" * 7},
            _INVALID + '"payloadId: 7 bytes, not 8"',
        ),
    ],
)
def test_malformed_response(response: dict, message: str) -> None:
    """A response with an unknown field, no status, or an ID of the wrong length is invalid."""
    with raises(engine.EngineError, message) as error:
        engine.read_forkchoice_response(response)
    assert error.value.code == 32602


def test_absent_fields() -> None:
    """A status without its hash and its error, or with them `null`, reads them as absent."""
    expected = ("SYNCING", None, None)
    assert engine.read_payload_status({"status": "SYNCING"}) == expected
    assert (
        engine.read_payload_status(
            {"status": "SYNCING", "latestValidHash": None, "validationError": None}
        )
        == expected
    )


@pytest.mark.parametrize(
    ("status", "message"),
    [
        ({"status": "VALIDATED"}, _INVALID + '"payloadStatus: no status VALIDATED"'),
        ({"status": "valid"}, _INVALID + '"payloadStatus: no status valid"'),
        ({"latestValidHash": _HASH}, _INVALID + '"payloadStatus: no field status"'),
        ({"status": "VALID", "extra": 1}, _INVALID + '"payloadStatus: unknown field"'),
        (
            {"status": "VALID", "latestValidHash": "0x" + "ab" * 31},
            _INVALID + '"latestValidHash: 31 bytes, not 32"',
        ),
        ({"status": "VALID", "validationError": 7}, _INVALID + '"validationError: not a string"'),
    ],
)
def test_malformed_status(status: dict, message: str) -> None:
    """An unknown name or field, no status, a short hash or a non-string error is invalid."""
    with raises(engine.EngineError, message) as error:
        engine.read_payload_status(status)
    assert error.value.code == 32602


@pytest.mark.parametrize("name", ["ACCEPTED", "INVALID_BLOCK_HASH"])
def test_unrestricted_status(name: str) -> None:
    """A status may be ACCEPTED or INVALID_BLOCK_HASH, but a forkchoice response may not."""
    assert engine.read_payload_status({"status": name}) == (name, None, None)
    with raises(engine.EngineError, _INVALID + '"payloadStatus: not a status of the method"'):
        engine.read_forkchoice_response({"payloadStatus": {"status": name}, "payloadId": None})
