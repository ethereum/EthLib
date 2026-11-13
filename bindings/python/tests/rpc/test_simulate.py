"""The checks of eth_simulateV1 before its blocks run, and the overrides of its accounts."""

import json
from collections.abc import Mapping
from pathlib import Path
from typing import Any, Final

import pytest

from ethlib.execution import rpc
from ethlib.state import state_root
from raising import raises

from .chain import FIXTURES, genesis_state, read_fixture, replay_chain

# The vendored fixtures of the method.
SIMULATE: Final = sorted((FIXTURES / "eth_simulateV1").glob("*.io"))

# The code of a request that passes every check before the execution.
# The execution of the simulated blocks is not yet specified, so the node fails with this code.
NOT_YET_SPECIFIED: Final = -32603

# The number and the time of the head of the test chain.
HEAD_NUMBER: Final = 60
HEAD_TIME: Final = 0x258


def _answer_codes(requests: list[str]) -> list[int]:
    """The error code of the response of the chain to each request."""
    codes = []
    for text in replay_chain().serve(requests):
        assert text is not None
        response = json.loads(text)
        assert set(response) == {"jsonrpc", "id", "error"}
        codes.append(response["error"]["code"])
    return codes


def _request(payload: Mapping[str, Any], *block: str) -> str:
    """The text of an eth_simulateV1 request with the payload and the optional base block."""
    params = [payload, *block]
    return json.dumps({"jsonrpc": "2.0", "id": 1, "method": "eth_simulateV1", "params": params})


def test_every_fixture_fails_before_execution() -> None:
    """Each vendored fixture expects an error, so none is checked for its result."""
    assert len(SIMULATE) == 17
    for path in SIMULATE:
        (exchange,) = read_fixture(path).exchanges
        assert "error" in exchange.response, path.name


@pytest.mark.parametrize("path", SIMULATE, ids=lambda path: path.stem)
def test_fixture(path: Path) -> None:
    """The view answers the code of the fixture, and the source fixes no message."""
    (exchange,) = read_fixture(path).exchanges
    assert _answer_codes([exchange.request]) == [exchange.response["error"]["code"]]


# Requests that pass every check before the execution, and requests that fail one.
CHECKS = [
    pytest.param({"blockStateCalls": [{}]}, NOT_YET_SPECIFIED, id="one-empty-block"),
    pytest.param({"blockStateCalls": []}, NOT_YET_SPECIFIED, id="no-block"),
    # A gap counts toward the limit of 256 blocks: 256 blocks fit, 257 do not.
    pytest.param(
        {"blockStateCalls": [{"blockOverrides": {"number": hex(HEAD_NUMBER + 256)}}]},
        NOT_YET_SPECIFIED,
        id="gap-to-limit",
    ),
    pytest.param(
        {"blockStateCalls": [{"blockOverrides": {"number": hex(HEAD_NUMBER + 257)}}]},
        -38026,
        id="gap-above-limit",
    ),
    pytest.param(
        {"blockStateCalls": [{"blockOverrides": {"number": hex(HEAD_NUMBER)}}]},
        -38020,
        id="number-of-base",
    ),
    pytest.param(
        {"blockStateCalls": [{"blockOverrides": {"time": hex(HEAD_TIME)}}]},
        -38021,
        id="time-of-base",
    ),
    pytest.param(
        {"blockStateCalls": [{"blockOverrides": {"Number": "0x3d"}}]}, -32602, id="key-in-case"
    ),
    pytest.param(
        {"blockStateCalls": [{"blockOverrides": {"number": hex(2**64)}}]},
        -32602,
        id="number-above-uint64",
    ),
    # The precompile of ECRECOVER moves to another address, or to its own.
    pytest.param(
        {
            "blockStateCalls": [
                {"stateOverrides": {f"0x{1:040x}": {"movePrecompileToAddress": f"0x{0xC2:040x}"}}}
            ]
        },
        NOT_YET_SPECIFIED,
        id="move-precompile",
    ),
    pytest.param(
        {
            "blockStateCalls": [
                {"stateOverrides": {f"0x{1:040x}": {"movePrecompileToAddress": f"0x{1:040x}"}}}
            ]
        },
        -38022,
        id="move-precompile-to-itself",
    ),
]


@pytest.mark.parametrize(("payload", "code"), CHECKS)
def test_checks(payload: Mapping[str, Any], code: int) -> None:
    """A request on the head gets the code of the first check that it fails."""
    assert _answer_codes([_request(payload)]) == [code]


def test_base_block_is_latest_by_default() -> None:
    """Without a base block, the request runs on the head, as with the tag latest."""
    payload = {"blockStateCalls": [{"blockOverrides": {"number": hex(HEAD_NUMBER)}}]}
    requests = [
        _request(payload),
        _request(payload, "latest"),
        _request(payload, hex(HEAD_NUMBER - 1)),
    ]
    assert _answer_codes(requests) == [-38020, -38020, NOT_YET_SPECIFIED]


def test_gap_block_times() -> None:
    """A gap block comes a block time after the block before, and the next block comes after it."""
    base = hex(HEAD_NUMBER - 1)
    (text,) = replay_chain().serve(
        [
            json.dumps(
                {
                    "jsonrpc": "2.0",
                    "id": 1,
                    "method": "eth_getBlockByNumber",
                    "params": [base, False],
                }
            )
        ]
    )
    assert text is not None
    time = int(json.loads(text)["result"]["timestamp"], 16)
    # On block 59, block 61 leaves a gap of one block, 12 seconds after block 59.
    for offset, code in ((12, -38021), (13, NOT_YET_SPECIFIED)):
        overrides = {"number": hex(HEAD_NUMBER + 1), "time": hex(time + offset)}
        payload = {"blockStateCalls": [{"blockOverrides": overrides}]}
        assert _answer_codes([_request(payload, base)]) == [code]


# An account with a nonce, a balance, code and two slots, and the address of another account.
ADDRESS: Final = f"0x{0xC0:040x}"
OTHER: Final = f"0x{0xC1:040x}"
ALLOC: Final = {
    ADDRESS: {"nonce": 1, "balance": 5, "code": "0x6000", "storage": {"0x01": 7, "0x02": 8}},
    OTHER: {"balance": 3},
}


def _slot(key: int) -> str:
    """A storage key or value as the 32-byte hex string of the schema."""
    return f"0x{key:064x}"


def _root(alloc: Mapping[str, Mapping[str, Any]]) -> bytes:
    """The state root of an allocation."""
    return state_root(genesis_state(alloc))


def _with(**account: Any) -> dict[str, dict[str, Any]]:
    """The allocation with the account at the address changed."""
    return {**ALLOC, ADDRESS: {**ALLOC[ADDRESS], **account}}


OVERRIDES = [
    pytest.param({"balance": "0x9"}, _with(balance=9), id="balance"),
    pytest.param({"nonce": "0x4"}, _with(nonce=4), id="nonce"),
    pytest.param({"code": "0x6001"}, _with(code="0x6001"), id="code"),
    pytest.param(
        {"stateDiff": {_slot(2): _slot(9), _slot(3): _slot(4)}},
        _with(storage={"0x01": 7, "0x02": 9, "0x03": 4}),
        id="stateDiff-keeps-other-slots",
    ),
    pytest.param(
        {"state": {_slot(2): _slot(9)}}, _with(storage={"0x02": 9}), id="state-clears-other-slots"
    ),
    pytest.param({"state": {}}, _with(storage={}), id="state-empty"),
    pytest.param({"movePrecompileToAddress": f"0x{0xC2:040x}"}, ALLOC, id="move-changes-nothing"),
    pytest.param({}, ALLOC, id="empty"),
    pytest.param(
        {"nonce": "0x4", "balance": "0x9", "code": "0x6001", "stateDiff": {_slot(3): _slot(4)}},
        _with(nonce=4, balance=9, code="0x6001", storage={"0x01": 7, "0x02": 8, "0x03": 4}),
        id="every-field",
    ),
]


@pytest.mark.parametrize(("override", "after"), OVERRIDES)
def test_override(override: Mapping[str, Any], after: Mapping[str, Mapping[str, Any]]) -> None:
    """An override sets the fields that it gives, and keeps the others and the other account."""
    state = genesis_state(ALLOC)
    assert rpc.apply_overrides(state, {ADDRESS: override}) == _root(after)


def test_override_creates_account() -> None:
    """An override of an address without an account creates it, unless it only moves it."""
    state = genesis_state(ALLOC)
    absent = f"0x{0xC3:040x}"
    created = {**ALLOC, absent: {"nonce": 2}}
    assert rpc.apply_overrides(state, {absent: {"nonce": "0x2"}}) == _root(created)
    moved = {absent: {"movePrecompileToAddress": OTHER}}
    assert rpc.apply_overrides(state, moved) == _root(ALLOC)


REJECTED = [
    pytest.param(
        {ADDRESS: {"balance": "0x1", "bogusField": "0x1"}},
        "account override: unknown key bogusField",
        id="unknown-key",
    ),
    pytest.param(
        {ADDRESS: {"Balance": "0x1"}}, "account override: unknown key Balance", id="key-in-case"
    ),
    pytest.param(
        {ADDRESS: {"state": {}, "stateDiff": {}}},
        "account override: both state and stateDiff",
        id="state-and-stateDiff",
    ),
    pytest.param(
        {ADDRESS: {"state": {}, "stateDiff": None}},
        "account override: both state and stateDiff",
        id="state-and-null-stateDiff",
    ),
    pytest.param(
        {ADDRESS: {}, ADDRESS.upper().replace("0X", "0x"): {}},
        "stateOverrides: an address twice",
        id="address-twice",
    ),
    pytest.param(
        {
            ADDRESS: {
                "stateDiff": {
                    _slot(0xAB): _slot(1),
                    _slot(0xAB).upper().replace("0X", "0x"): _slot(2),
                }
            }
        },
        "stateDiff: a slot twice",
        id="slot-twice",
    ),
    pytest.param({ADDRESS: {"nonce": hex(2**64)}}, "nonce: above 2^64", id="nonce-above-uint64"),
    pytest.param([], "stateOverrides: not an object", id="not-an-object"),
    pytest.param({ADDRESS: 1}, "account override: not an object", id="account-not-an-object"),
    pytest.param({ADDRESS: {"state": []}}, "state: not an object", id="state-not-an-object"),
    pytest.param({ADDRESS: {"code": b"\x00"}}, "stateOverrides: not a JSON value", id="bytes"),
]


@pytest.mark.parametrize(("overrides", "reason"), REJECTED)
def test_rejected_override(overrides: object, reason: str) -> None:
    """An object outside the schema raises the code of invalid parameters, with its reason."""
    with raises(rpc.RpcError, reason) as error:
        rpc.apply_overrides(genesis_state(ALLOC), overrides)
    assert error.value.code == 32602
