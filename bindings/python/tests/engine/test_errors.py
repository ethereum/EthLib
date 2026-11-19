"""The error object of each Engine API error, against the table of errors of the source."""

# The table of errors.
#
# Repository: ethereum/execution-apis
# Commit: 3284ee80c3da3e516c53782dde75157cccf1ebdc
# File: src/engine/common.md, section Errors

import json
from pathlib import Path

import pytest

from ethlib import engine
from ethlib.errors import EngineError
from raising import raises

# The rows of the table that an Engine API method can return, as code and message.
# The table gives each of them `null` data.
# It also has the other JSON-RPC errors, which no Engine API method of EthLib returns.
TABLE = {
    -32602: "Invalid params",
    -38001: "Unknown payload",
    -38002: "Invalid forkchoice state",
    -38003: "Invalid payload attributes",
    -38004: "Too large request",
    -38005: "Unsupported fork",
    -38006: "Too deep reorg",
}

_CONTRACT = Path(__file__).resolve().parents[3] / "contract" / "contract.json"


@pytest.mark.parametrize("code", sorted(TABLE, reverse=True))
def test_error_object(code: int) -> None:
    """The error object of each code has the message of its row and `null` data."""
    error = json.loads(engine.error_object(-code))
    assert error == {"code": code, "message": TABLE[code], "data": None}


def test_codes_of_the_type() -> None:
    """The Engine error type has one constructor for each row, and no other code."""
    codes = {
        entry["code"]
        for method in json.loads(_CONTRACT.read_text())["methods"]
        for error in method["errors"]
        if error["type"] == "EthLib.Engine.EngineError"
        for entry in error["codes"]
    }
    assert codes == {-code for code in TABLE}


@pytest.mark.parametrize("code", [0, 32000, 32700, 38000, 38007])
def test_other_code(code: int) -> None:
    """A code of no Engine API error raises with code 0."""
    with raises(EngineError, f"no Engine API error has the code {code}") as caught:
        engine.error_object(code)
    assert caught.value.code == 0
