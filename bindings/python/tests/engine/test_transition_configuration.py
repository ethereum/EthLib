"""The answers of engine_exchangeTransitionConfigurationV1 to valid and invalid requests."""

# Rules of the method and of its configuration.
#
# ethereum/execution-apis, src/engine/paris.md, commit 3284ee80c3da3e516c53782dde75157cccf1ebdc.
# ethereum/EIPs, EIPS/eip-3675.md, commit 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445.

import copy
import json
from pathlib import Path
from typing import Any

import pytest

from ethlib import engine
from raising import raises

_DIR = Path(__file__).resolve().parents[4] / "tests" / "engine"
[EXAMPLE] = [
    case
    for case in json.loads((_DIR / "openrpc.json").read_text())
    if case["method"] == "engine_exchangeTransitionConfigurationV1"
]
METHOD = "engine_exchangeTransitionConfigurationV1"

_INVALID = "engine error: EthLib.Engine.EngineError.invalidParams "

ZERO_HASH = bytes(32)
# The mainnet terminal total difficulty of EIP-3675, "Definitions".
MAINNET_TTD = 58_750_000_000_000_000_000_000
# The value of step 7 of the method while the terminal total difficulty is not decided.
UNDECIDED_TTD = 2**256 - 2**10


def _invalid(reason: str) -> str:
    return _INVALID + json.dumps(reason)


def _params() -> list[Any]:
    return copy.deepcopy(EXAMPLE["params"])


def test_example() -> None:
    """The node of the example, configured with its values, answers the example result."""
    result = engine.exchange_transition_configuration(0, ZERO_HASH, 1, METHOD, EXAMPLE["params"])
    assert result == EXAMPLE["result"]


def test_answer_ignores_request() -> None:
    """The node answers its own configuration, whatever configuration the request holds."""
    hash_ = bytes(range(32))
    result = engine.exchange_transition_configuration(
        MAINNET_TTD, hash_, 0, METHOD, EXAMPLE["params"]
    )
    assert result == {
        "terminalTotalDifficulty": "0xc70d808a128d7380000",
        "terminalBlockHash": "0x" + hash_.hex(),
        "terminalBlockNumber": "0x0",
    }


def test_undecided() -> None:
    """The undecided terminal total difficulty of step 7 crosses unchanged."""
    params = _params()
    params[0]["terminalTotalDifficulty"] = hex(UNDECIDED_TTD)
    result = engine.exchange_transition_configuration(UNDECIDED_TTD, ZERO_HASH, 0, METHOD, params)
    assert result == {
        "terminalTotalDifficulty": hex(UNDECIDED_TTD),
        "terminalBlockHash": "0x" + "00" * 32,
        "terminalBlockNumber": "0x0",
    }


def test_block_number_zero() -> None:
    """A consensus node may send 0 as the terminal block number."""
    params = _params()
    params[0]["terminalBlockNumber"] = "0x0"
    result = engine.exchange_transition_configuration(0, ZERO_HASH, 1, METHOD, params)
    assert result == EXAMPLE["result"]


@pytest.mark.parametrize(
    ("key", "value", "reason"),
    [
        ("terminalBlockNumber", "0x01", "terminalBlockNumber: leading zero"),
        ("terminalTotalDifficulty", hex(2**256), "terminalTotalDifficulty: above 2^256"),
        ("terminalBlockNumber", hex(2**64), "terminalBlockNumber: above 2^64"),
        ("terminalBlockHash", "0x" + "00" * 31, "terminalBlockHash: 31 bytes, not 32"),
    ],
)
def test_malformed_field(key: str, value: str, reason: str) -> None:
    """A field that is not of its type is an invalid parameter."""
    params = _params()
    params[0][key] = value
    with raises(engine.EngineError, _invalid(reason)) as error:
        engine.exchange_transition_configuration(0, ZERO_HASH, 1, METHOD, params)
    assert error.value.code == 32602


def test_missing_field() -> None:
    """The request holds all three fields."""
    params = _params()
    del params[0]["terminalBlockNumber"]
    message = _invalid("transitionConfiguration: not the fields of the structure")
    with raises(engine.EngineError, message) as error:
        engine.exchange_transition_configuration(0, ZERO_HASH, 1, METHOD, params)
    assert error.value.code == 32602


@pytest.mark.parametrize("params", [[], [None, None]], ids=["none", "two"])
def test_parameter_count(params: list[Any]) -> None:
    """The request holds exactly one parameter."""
    count = len(params)
    with raises(engine.EngineError, _invalid(f"params: got {count}, expected 1")) as error:
        engine.exchange_transition_configuration(0, ZERO_HASH, 1, METHOD, params)
    assert error.value.code == 32602


def test_other_method() -> None:
    """A request for another method has code 0."""
    method = "engine_exchangeTransitionConfigurationV2"
    with raises(engine.EngineError, f"no method {method}") as error:
        engine.exchange_transition_configuration(0, ZERO_HASH, 1, method, _params())
    assert error.value.code == 0


@pytest.mark.parametrize(
    ("difficulty", "number", "message"),
    [
        (2**256, 1, f"config: a total difficulty of {2**256}, not below 2^256"),
        (0, 2**64, f"config: a block number of {2**64}, not below 2^64"),
    ],
)
def test_configuration_out_of_range(difficulty: int, number: int, message: str) -> None:
    """A configuration that does not fit its fields has code 0."""
    with raises(engine.EngineError, message) as error:
        engine.exchange_transition_configuration(difficulty, ZERO_HASH, number, METHOD, _params())
    assert error.value.code == 0
