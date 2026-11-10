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
    """The file holds 93 valid payloads, 75 JSON-RPC errors and 82 invalid payloads."""
    kinds = Counter(
        check(c["network"], c["method"], c["params"], c["validationError"], c["errorCode"])
        for c in CASES
    )
    # A check before execution rejects 80 of the invalid payloads.
    # The 2 others are Amsterdam block access lists with accounts out of order, or one twice.
    # That is found when the block runs, so without the parent's state the payload is syncing.
    assert kinds == {"valid": 93, "error": 75, "invalid": 80, "execution": 2}


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


def _is_typed(transaction: str) -> bool:
    """Whether a transaction of a payload is typed: its first byte is a type, below 0x80."""
    return int(transaction[2:4], 16) < 0x80


def _wrapped(transaction: str) -> str:
    """A typed transaction in the form of a block body: a long RLP string around its bytes."""
    raw = bytes.fromhex(transaction.removeprefix("0x"))
    # A string of 56 bytes or more: 0xb7 plus the size of its length, then its big-endian length.
    length = len(raw).to_bytes((len(raw).bit_length() + 7) // 8, "big")
    return "0x" + (bytes([0xB7 + len(length)]) + length + raw).hex()


# A payload holds a typed transaction as its bytes, by the transactions field of the Engine API.
# A block body holds the same bytes inside an RLP string, as EIP-2718 sets out.
# EIP-2718 reads a first byte up to 0x7f as a type, and one from 0xc0 as a legacy transaction.
# The wrapped form starts with 0xb8 or 0xb9 here, so it starts no transaction.
_METHODS = [f"engine_newPayloadV{version}" for version in range(1, 6)]


@pytest.mark.parametrize("method", _METHODS)
def test_typed_transaction_wrapped_in_rlp_string(method: str) -> None:
    """A typed transaction wrapped in an RLP string does not decode, so the payload is invalid."""
    case = next(
        c
        for c in CASES
        if c["method"] == method
        and c["validationError"] is None
        and c["errorCode"] is None
        and any(_is_typed(tx) for tx in c["params"][0]["transactions"])
    )
    network, payload = case["network"], case["params"][0]
    index = next(i for i, tx in enumerate(payload["transactions"]) if _is_typed(tx))
    # The payload as the fixture gives it passes, so the wrapped form alone makes it invalid.
    assert engine.new_payload(config(network), method, case["params"])["status"] == "SYNCING"
    transactions = list(payload["transactions"])
    wrapped = _wrapped(transactions[index])
    transactions[index] = wrapped
    # The block hash stays that of the fixture, so the transactions root of the header is wrong too.
    # The transactions decode before the block hash is checked, so the error names the transaction.
    params = [dict(payload, transactions=transactions), *case["params"][1:]]
    status = engine.new_payload(config(network), method, params)
    first = int(wrapped[2:4], 16)
    assert first in (0xB8, 0xB9)
    assert status == {
        "status": "INVALID",
        "latestValidHash": None,
        "validationError": f"401: transaction {index} does not decode: "
        f"EthLib.Execution.Transactions.TransactionError.unsupportedType {first}",
    }
