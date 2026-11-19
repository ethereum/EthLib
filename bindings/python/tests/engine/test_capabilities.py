"""The answers of engine_exchangeCapabilities and engine_getClientVersionV1."""

# Rules of the two methods.
#
# Repository: ethereum/execution-apis
# Commit: 3284ee80c3da3e516c53782dde75157cccf1ebdc
# Files: src/engine/common.md, src/engine/identification.md

import json
import re
from pathlib import Path
from typing import Any

import pytest

from ethlib import engine
from raising import raises

_DIR = Path(__file__).resolve().parents[4] / "tests" / "engine"
[EXAMPLE] = [
    case
    for case in json.loads((_DIR / "openrpc.json").read_text())
    if case["method"] == "engine_exchangeCapabilities"
]
CAPABILITIES = "engine_exchangeCapabilities"
CLIENT_VERSION = "engine_getClientVersionV1"

_INVALID = "engine error: EthLib.Engine.EngineError.invalidParams "

# Step 2 of engine_exchangeCapabilities: each name ends with `V` and its version.
_VERSIONED = re.compile(r"engine_[A-Za-z]+V[1-9][0-9]*")

# The last version of each method that EthLib defines; each has every version from 1.
# The order is that of EthLib's table; the source fixes no order.
_DEFINED = {
    "newPayload": 5,
    "forkchoiceUpdated": 4,
    "getPayload": 6,
    "getPayloadBodiesByHash": 2,
    "getPayloadBodiesByRange": 2,
    "getBlobs": 4,
    "exchangeTransitionConfiguration": 1,
    "getClientVersion": 1,
}

# The example version and commit of ClientVersionV1 in identification.md.
# The code is one that no program has reserved.
CLIENT: dict[str, Any] = {
    "code": "ZZ",
    "name": "example",
    "version": "1.0.0-alpha.1",
    "commit": "0xfa4ff922",
}
OWN = ("XY", "node", "v4.6.0", bytes.fromhex("01020304"))


def _invalid(reason: str) -> str:
    return _INVALID + json.dumps(reason)


def _client_version(params: list[Any]) -> list[dict[str, Any]]:
    return engine.get_client_version(*OWN, CLIENT_VERSION, params)


def test_example_shape() -> None:
    """The request of the example gets a list of versioned names without the method itself."""
    # The example result lists another program's methods, so only its shape is checked.
    result = engine.exchange_capabilities(CAPABILITIES, EXAMPLE["params"])
    assert all(_VERSIONED.fullmatch(name) for name in result)
    assert len(set(result)) == len(result)
    assert CAPABILITIES not in result


def test_answer() -> None:
    """The answer lists every version of every method that EthLib defines, whatever the request."""
    expected = [
        f"engine_{method}V{version}"
        for method, last in _DEFINED.items()
        for version in range(1, last + 1)
    ]
    assert engine.exchange_capabilities(CAPABILITIES, EXAMPLE["params"]) == expected
    assert engine.exchange_capabilities(CAPABILITIES, [[]]) == expected
    assert engine.exchange_capabilities(CAPABILITIES, [["engine_unknown"]]) == expected


@pytest.mark.parametrize(
    ("params", "reason"),
    [
        ([["engine_newPayloadV1", 7]], "capability: not a string"),
        ([{"engine_newPayloadV1": 1}], "capabilities: not an array"),
        ([], "params: got 0, expected 1"),
        ([[], []], "params: got 2, expected 1"),
    ],
    ids=["number", "object", "none", "two"],
)
def test_capabilities_malformed(params: list[Any], reason: str) -> None:
    """A request that is not one array of strings is an invalid parameter."""
    with raises(engine.EngineError, _invalid(reason)) as error:
        engine.exchange_capabilities(CAPABILITIES, params)
    assert error.value.code == 32602


@pytest.mark.parametrize("method", ["engine_exchangeCapabilitiesV1", CLIENT_VERSION])
def test_capabilities_other_method(method: str) -> None:
    """A request for another method has code 0."""
    with raises(engine.EngineError, f"no method {method}") as error:
        engine.exchange_capabilities(method, [[]])
    assert error.value.code == 0


def test_client_version() -> None:
    """The node answers an array of its own version object alone."""
    assert _client_version([CLIENT]) == [
        {"code": "XY", "name": "node", "version": "v4.6.0", "commit": "0x01020304"}
    ]


@pytest.mark.parametrize("code", ["zz", "Zz", "BU"])
def test_client_code_any_letters(code: str) -> None:
    """Step 2: any two letters are a code, whatever their case and whether reserved."""
    client = CLIENT | {"code": code}
    assert _client_version([client])[0]["code"] == "XY"


@pytest.mark.parametrize(
    ("key", "value", "reason"),
    [
        ("code", "Z", "code: not two letters"),
        ("code", "ZZZ", "code: not two letters"),
        ("code", "Z1", "code: not two letters"),
        ("code", 7, "code: not a string"),
        ("name", 7, "name: not a string"),
        ("commit", "0xfa4ff9", "commit: 3 bytes, not 4"),
        ("commit", "fa4ff922", "commit: no 0x marker"),
    ],
)
def test_client_version_malformed_field(key: str, value: Any, reason: str) -> None:
    """A field that is not of its type is an invalid parameter."""
    with raises(engine.EngineError, _invalid(reason)) as error:
        _client_version([CLIENT | {key: value}])
    assert error.value.code == 32602


@pytest.mark.parametrize(
    "client",
    [
        {key: value for key, value in CLIENT.items() if key != "commit"},
        CLIENT | {"extra": "x"},
    ],
    ids=["missing", "extra"],
)
def test_client_version_fields(client: dict[str, Any]) -> None:
    """The request holds exactly the four fields."""
    message = _invalid("clientVersion: not the fields of the structure")
    with raises(engine.EngineError, message) as error:
        _client_version([client])
    assert error.value.code == 32602


@pytest.mark.parametrize("params", [[], [CLIENT, CLIENT]], ids=["none", "two"])
def test_client_version_parameter_count(params: list[Any]) -> None:
    """The request holds exactly one parameter."""
    count = len(params)
    with raises(engine.EngineError, _invalid(f"params: got {count}, expected 1")) as error:
        _client_version(params)
    assert error.value.code == 32602


def test_client_version_own_code() -> None:
    """A node whose own code is not two letters has code 0."""
    with raises(engine.EngineError, "own: a code XYZ, not two letters") as error:
        engine.get_client_version("XYZ", *OWN[1:], CLIENT_VERSION, [CLIENT])
    assert error.value.code == 0


def test_client_version_own_commit() -> None:
    """A node whose own commit is not four bytes has code 0."""
    with raises(engine.EngineError, "expected 4 bytes, got 3") as error:
        engine.get_client_version(*OWN[:3], bytes(3), CLIENT_VERSION, [CLIENT])
    assert error.value.code == 0
