"""The simulated blocks of eth_simulateV1, its checks, and the overrides of its accounts."""

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

# The answer of a request that passes every check and runs its blocks.
RESULT: Final = None

# The number and the time of the head of the test chain.
HEAD_NUMBER: Final = 60
HEAD_TIME: Final = 0x258


def _answer_codes(requests: list[str]) -> list[int | None]:
    """The error code of the response of the chain to each request, or None for a result."""
    codes: list[int | None] = []
    for text in replay_chain().serve(requests):
        assert text is not None
        response = json.loads(text)
        assert set(response) in ({"jsonrpc", "id", "error"}, {"jsonrpc", "id", "result"})
        codes.append(response["error"]["code"] if "error" in response else RESULT)
    return codes


def _call(call: Mapping[str, Any]) -> dict[str, Any]:
    """A call result without the message of its error, after checking the prefix of a revert."""
    if "error" not in call:
        return dict(call)
    error = dict(call["error"])
    message = error.pop("message")
    # The schema fixes the start of the message of a revert, and leaves the rest to the client.
    assert error["code"] != 3 or message.startswith("execution reverted")
    return {**call, "error": error}


def _blocks(response: Mapping[str, Any]) -> list[dict[str, Any]]:
    """The blocks of a response, without the error messages of their calls."""
    return [
        {**block, "calls": [_call(call) for call in block["calls"]]} for block in response["result"]
    ]


def _request(payload: Mapping[str, Any], *block: str) -> str:
    """The text of an eth_simulateV1 request with the payload and the optional base block."""
    params = [payload, *block]
    return json.dumps({"jsonrpc": "2.0", "id": 1, "method": "eth_simulateV1", "params": params})


def test_every_fixture_is_vendored() -> None:
    """The suite holds every fixture of the method at the pinned commit."""
    assert len(SIMULATE) == 95


@pytest.mark.parametrize("path", SIMULATE, ids=lambda path: path.stem)
def test_fixture(path: Path) -> None:
    """The view answers the code or the blocks of the fixture; the source fixes no message."""
    (exchange,) = read_fixture(path).exchanges
    (text,) = replay_chain().serve([exchange.request])
    assert text is not None
    response = json.loads(text)
    if "error" in exchange.response:
        assert response["error"]["code"] == exchange.response["error"]["code"]
    else:
        assert "result" in response, response.get("error")
        assert _blocks(response) == _blocks(exchange.response)


# Requests that pass every check before the execution, and requests that fail one.
CHECKS = [
    pytest.param({"blockStateCalls": [{}]}, RESULT, id="one-empty-block"),
    pytest.param({"blockStateCalls": []}, RESULT, id="no-block"),
    # A gap counts toward the limit of 256 blocks: 256 blocks fit, 257 do not.
    pytest.param(
        {"blockStateCalls": [{"blockOverrides": {"number": hex(HEAD_NUMBER + 256)}}]},
        RESULT,
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
        RESULT,
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
def test_checks(payload: Mapping[str, Any], code: int | None) -> None:
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
    assert _answer_codes(requests) == [-38020, -38020, RESULT]


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
    for offset, code in ((12, -38021), (13, RESULT)):
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


# The sender and the recipient of the example of "ETH transfer logs" in the notes of the method.
SENDER: Final = "0xc000000000000000000000000000000000000000"
RECIPIENT: Final = "0xc100000000000000000000000000000000000000"

# An account that the code of the recipient pays, without a balance in the genesis file.
THIRD: Final = "0xc200000000000000000000000000000000000000"

# The address of the logs that tracing adds before EIP-7708, and the system address of EIP-7708.
TRACE_ADDRESS: Final = "0x" + "ee" * 20
SYSTEM_ADDRESS: Final = "0x" + "ff" * 19 + "fe"

# The Keccak-256 hash of `Transfer(address,address,uint256)`, the first topic of a transfer log.
TRANSFER_TOPIC: Final = "0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef"

# The time at which the test chain activates Amsterdam, and a block before it.
AMSTERDAM_TIME: Final = json.loads((FIXTURES / "genesis.json").read_text())["config"][
    "amsterdamTime"
]
BEFORE_AMSTERDAM: Final = hex(50)

# The three accounts as topics: 32-byte words with zeros in front.
SENDER_TOPIC: Final = "0x000000000000000000000000c000000000000000000000000000000000000000"
RECIPIENT_TOPIC: Final = "0x000000000000000000000000c100000000000000000000000000000000000000"
THIRD_TOPIC: Final = "0x000000000000000000000000c200000000000000000000000000000000000000"

# The topics and the data of the transfer of 0x3e8 wei from the sender to the recipient.
TRANSFER: Final = (
    [TRANSFER_TOPIC, SENDER_TOPIC, RECIPIENT_TOPIC],
    "0x00000000000000000000000000000000000000000000000000000000000003e8",
)

# The topics and the data of the transfer of 0x1f4 wei from the recipient to the third account.
FORWARDED: Final = (
    [TRANSFER_TOPIC, RECIPIENT_TOPIC, THIRD_TOPIC],
    "0x00000000000000000000000000000000000000000000000000000000000001f4",
)

# PUSH1 0 four times, PUSH2 0x1f4, PUSH20 the third account, GAS, CALL, STOP.
FORWARD: Final = "0x60006000600060006101f473" + THIRD[2:] + "5af100"

# PUSH1 0, PUSH1 0, REVERT.
REVERT: Final = "0x60006000fd"


def _transfer_block(
    trace: bool,
    base: str,
    code: str | None = None,
    extra: Mapping[str, dict[str, str]] | None = None,
    calls: int = 1,
) -> dict[str, Any]:
    """The simulated block of transfers of 0x3e8 wei, with the code of the recipient if any."""
    overrides: dict[str, dict[str, str]] = {SENDER: {"balance": hex(10**18)}, **(extra or {})}
    if code is not None:
        overrides[RECIPIENT] = {"code": code}
    call = {"from": SENDER, "to": RECIPIENT, "value": "0x3e8"}
    payload = {
        "blockStateCalls": [{"stateOverrides": overrides, "calls": [call] * calls}],
        "traceTransfers": trace,
    }
    (text,) = replay_chain().serve([_request(payload, base)])
    assert text is not None
    (block,) = json.loads(text)["result"]
    return block


def _logs(call: Mapping[str, Any]) -> list[tuple[str, list[str], str, str]]:
    """The address, the topics, the data and the index of each log of a call result."""
    return [(log["address"], log["topics"], log["data"], log["logIndex"]) for log in call["logs"]]


def test_transfer_log_before_amsterdam() -> None:
    """Before Amsterdam, a traced transfer reports the log of the example of the notes."""
    block = _transfer_block(True, BEFORE_AMSTERDAM)
    (call,) = block["calls"]
    assert (call["status"], call["gasUsed"]) == ("0x1", "0x5208")
    assert _logs(call) == [(TRACE_ADDRESS, *TRANSFER, "0x0")]
    (log,) = call["logs"]
    assert (log["blockNumber"], log["blockHash"]) == (block["number"], block["hash"])
    assert (log["transactionIndex"], log["removed"]) == ("0x0", False)


def test_no_transfer_log_without_trace() -> None:
    """Without tracing, a transfer before Amsterdam reports no log."""
    (call,) = _transfer_block(False, BEFORE_AMSTERDAM)["calls"]
    assert call["status"] == "0x1"
    assert _logs(call) == []


def test_no_transfer_log_on_revert() -> None:
    """A transfer whose call reverts reports no log."""
    (call,) = _transfer_block(True, BEFORE_AMSTERDAM, REVERT)["calls"]
    assert call["status"] == "0x0"
    assert _logs(call) == []


def test_transfer_log_numbered_with_code_logs() -> None:
    """A transfer log is numbered with the logs of the code, in the order they are written."""
    # PUSH1 0, PUSH1 0, LOG0: a log with no topic and no data.
    (call,) = _transfer_block(True, BEFORE_AMSTERDAM, "0x60006000a0")["calls"]
    assert _logs(call) == [(TRACE_ADDRESS, *TRANSFER, "0x0"), (RECIPIENT, [], "0x", "0x1")]


def test_transfer_log_of_inner_call() -> None:
    """A CALL with value inside the code logs its transfer after the transfer of the call."""
    (call,) = _transfer_block(True, BEFORE_AMSTERDAM, FORWARD)["calls"]
    assert call["status"] == "0x1"
    assert _logs(call) == [(TRACE_ADDRESS, *TRANSFER, "0x0"), (TRACE_ADDRESS, *FORWARDED, "0x1")]


def test_no_transfer_log_of_reverted_inner_call() -> None:
    """The transfer of an inner call that reverts is not logged; the outer transfer is."""
    block = _transfer_block(True, BEFORE_AMSTERDAM, FORWARD, {THIRD: {"code": REVERT}})
    (call,) = block["calls"]
    assert call["status"] == "0x1"
    assert _logs(call) == [(TRACE_ADDRESS, *TRANSFER, "0x0")]


def test_transfer_log_of_selfdestruct() -> None:
    """A SELFDESTRUCT that sends the balance of the code logs that transfer."""
    # PUSH20 the third account, SELFDESTRUCT: the recipient sends the 0x3e8 wei it received.
    (call,) = _transfer_block(True, BEFORE_AMSTERDAM, "0x73" + THIRD[2:] + "ff")["calls"]
    sent = ([TRANSFER_TOPIC, RECIPIENT_TOPIC, THIRD_TOPIC], TRANSFER[1])
    assert _logs(call) == [(TRACE_ADDRESS, *TRANSFER, "0x0"), (TRACE_ADDRESS, *sent, "0x1")]


def test_transfer_log_index_continues_across_calls() -> None:
    """The second call of a block numbers its transfer log after the log of the first call."""
    first, second = _transfer_block(True, BEFORE_AMSTERDAM, calls=2)["calls"]
    assert _logs(first) == [(TRACE_ADDRESS, *TRANSFER, "0x0")]
    assert _logs(second) == [(TRACE_ADDRESS, *TRANSFER, "0x1")]
    assert second["logs"][0]["transactionIndex"] == "0x1"


def test_header_does_not_depend_on_trace() -> None:
    """The header of a simulated block, with its bloom, is the same with tracing or without."""
    blocks = [_transfer_block(trace, BEFORE_AMSTERDAM) for trace in (False, True)]
    headers = [{key: value for key, value in block.items() if key != "calls"} for block in blocks]
    assert headers[0] == headers[1]
    assert int(headers[0]["logsBloom"], 16) == 0


def test_trace_changes_nothing_from_amsterdam() -> None:
    """From Amsterdam, the protocol logs the transfer itself, so tracing changes nothing."""
    blocks = [_transfer_block(trace, hex(HEAD_NUMBER)) for trace in (False, True)]
    assert blocks[0] == blocks[1]
    assert int(blocks[0]["logsBloom"], 16) != 0
    (call,) = blocks[0]["calls"]
    assert _logs(call) == [(SYSTEM_ADDRESS, *TRANSFER, "0x0")]


def test_transfer_logs_across_amsterdam() -> None:
    """One simulation logs through tracing just before Amsterdam and through EIP-7708 from it."""
    call = {"from": SENDER, "to": RECIPIENT, "value": "0x3e8"}
    payload = {
        "blockStateCalls": [
            {
                "blockOverrides": {"time": hex(AMSTERDAM_TIME - 1)},
                "stateOverrides": {SENDER: {"balance": hex(10**18)}},
                "calls": [call],
            },
            {"blockOverrides": {"time": hex(AMSTERDAM_TIME)}, "calls": [call]},
        ],
        "traceTransfers": True,
    }
    (text,) = replay_chain().serve([_request(payload, BEFORE_AMSTERDAM)])
    assert text is not None
    before, after = json.loads(text)["result"]
    assert [_logs(c) for c in before["calls"]] == [[(TRACE_ADDRESS, *TRANSFER, "0x0")]]
    assert [_logs(c) for c in after["calls"]] == [[(SYSTEM_ADDRESS, *TRANSFER, "0x0")]]
