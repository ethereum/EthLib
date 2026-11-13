"""Block access-list queries against the pinned execution-apis chain and access lists."""

import json
from collections.abc import Sequence
from copy import deepcopy
from dataclasses import replace
from typing import Any

import pytest

from ethlib.cryptography.keccak import keccak256
from ethlib.execution import rpc
from ethlib.serialization import rlp
from raising import raises

from .chain import FIXTURES, block_hash, replay_chain

METHODS = ("eth_getBlockAccessList", "debug_getRawBlockAccessList")
UNKNOWN = "0x" + "11" * 32
ADDRESS = "0x" + "00" * 20
BAD_PARAMS: list[tuple[list[object], str]] = [
    ([], "missing parameter"),
    (["latest", "extra"], "the method takes one parameter"),
    ([UNKNOWN, "extra"], "the method takes one parameter"),
    ([True], "block: not a string or an object"),
    (["0x03c"], "block: not a block number, tag or hash"),
    (
        [{"blockNumber": "0x3c", "blockHash": UNKNOWN}],
        "block: not one block number or one block hash",
    ),
    (
        [{"blockHash": UNKNOWN, "requireCanonical": None}],
        "block: requireCanonical is not a boolean",
    ),
]
NOT_FOUND = {"code": -32001, "message": "Resource not found"}
PRUNED = {"code": 4444, "message": "Pruned history unavailable"}
INVALID_PARAMS = {"code": -32602, "message": "Invalid params"}


def _request(method: str, params: Sequence[object]) -> str:
    return json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params})


@pytest.fixture(scope="module")
def answers() -> dict[str, dict[str, Any]]:
    chain = replay_chain()
    blocks: list[object] = [hex(n) for n in (0, 27, 56, 57, 58, 59, 60, 61)] + [
        "latest",
        "safe",
        "finalized",
        "earliest",
        "pending",
        UNKNOWN,
        "0x" + block_hash(chain.blocks[60]).hex(),
        {"blockNumber": "0x3c"},
        {"blockHash": "0x" + block_hash(chain.blocks[60]).hex(), "requireCanonical": True},
    ]
    calls = [(method, [block]) for method in METHODS for block in blocks]
    calls += [("eth_getHeaderByNumber", [hex(n)]) for n in range(57, 61)]
    calls += [("eth_getBlockByNumber", [hex(n), False]) for n in range(57, 61)]
    calls += [(method, params) for method in METHODS for params, _ in BAD_PARAMS]
    requests = [_request(method, params) for method, params in calls]
    texts = chain.serve(requests)
    parsed = {}
    for request, text in zip(requests, texts, strict=True):
        assert text is not None
        response = json.loads(text)
        assert response["jsonrpc"] == "2.0"
        assert response["id"] == 1
        kind = "error" if "error" in response else "result"
        assert set(response) == {"jsonrpc", "id", kind}
        parsed[request] = response
    return parsed


def _word(value: str) -> str:
    return f"0x{int(value, 16):064x}"


def _account(entry: dict[str, Any]) -> dict[str, Any]:
    # The pinned tools/chain/bal files use another JSON form than the method's schema.
    # None of these four blocks changes code; the separate code-change case covers that field.
    assert set(entry) == {
        "address",
        "storageChanges",
        "storageReads",
        "balanceChanges",
        "nonceChanges",
        "codeChanges",
    }
    assert entry["codeChanges"] is None
    return {
        "address": entry["address"],
        "storageChanges": [
            {
                "key": _word(slot["slot"]),
                "changes": [
                    {"index": change["blockAccessIndex"], "value": _word(change["postValue"])}
                    for change in slot["slotChanges"]
                ],
            }
            for slot in entry["storageChanges"] or []
        ],
        "storageReads": [_word(slot) for slot in entry["storageReads"] or []],
        "balanceChanges": [
            {"index": change["blockAccessIndex"], "value": change["postBalance"]}
            for change in entry["balanceChanges"] or []
        ],
        "nonceChanges": [
            {"index": change["blockAccessIndex"], "value": change["postNonce"]}
            for change in entry["nonceChanges"] or []
        ],
        "codeChanges": [],
    }


@pytest.mark.parametrize("number", range(57, 61))
def test_pinned_access_lists(number: int, answers: dict[str, dict[str, Any]]) -> None:
    # Source: execution-apis 3284ee80, tools/chain/bal/block-000NN.json, copied byte for byte.
    pinned = json.loads((FIXTURES / "bal" / f"block-{number:05d}.json").read_text())
    decoded = answers[_request(METHODS[0], [hex(number)])]["result"]
    raw = bytes.fromhex(answers[_request(METHODS[1], [hex(number)])]["result"][2:])
    header = answers[_request("eth_getHeaderByNumber", [hex(number)])]["result"]
    block = answers[_request("eth_getBlockByNumber", [hex(number), False])]["result"]
    assert set(pinned) == {
        "number",
        "hash",
        "timestamp",
        "blockAccessListHash",
        "blockAccessListRootOfList",
        "transactions",
        "blockAccessList",
    }
    assert decoded == [_account(entry) for entry in pinned["blockAccessList"]]
    assert (
        "0x" + keccak256(raw).hex()
        == pinned["blockAccessListHash"]
        == pinned["blockAccessListRootOfList"]
        == header["blockAccessListHash"]
    )
    assert rpc.encode_block_access_list(decoded) == raw
    assert header["hash"] == pinned["hash"]
    assert int(header["number"], 16) == pinned["number"] == number
    assert int(header["timestamp"], 16) == pinned["timestamp"]
    assert block["transactions"] == pinned["transactions"]


@pytest.mark.parametrize("method", METHODS)
def test_lookup_forms(method: str, answers: dict[str, dict[str, Any]]) -> None:
    expected = answers[_request(method, ["0x3c"])]["result"]
    hash_string = "0x" + block_hash(replay_chain().blocks[60]).hex()
    for block in [
        "latest",
        "safe",
        "finalized",
        hash_string,
        {"blockNumber": "0x3c"},
        {"blockHash": hash_string, "requireCanonical": True},
    ]:
        assert answers[_request(method, [block])]["result"] == expected


@pytest.mark.parametrize(("safe", "finalized"), [(59, 58), (27, 56)])
def test_distinct_forkchoice_tags(safe: int, finalized: int) -> None:
    """Safe and finalized select their own blocks, including blocks before Amsterdam."""
    chain = replay_chain()
    chain = replace(
        chain,
        forkchoice=tuple(block_hash(chain.blocks[n]) for n in (60, safe, finalized)),
    )
    calls = [
        (method, tag, n)
        for method in METHODS
        for tag, n in [("safe", safe), ("finalized", finalized)]
    ]
    responses = chain.serve([_request(method, [tag]) for method, tag, _ in calls])
    for (method, _, number), text in zip(calls, responses, strict=True):
        assert text is not None
        response = json.loads(text)
        if number < 57:
            assert response == {
                "jsonrpc": "2.0",
                "id": 1,
                "error": {**NOT_FOUND, "data": "block predates Amsterdam"},
            }
            continue
        pinned = json.loads((FIXTURES / "bal" / f"block-{number:05d}.json").read_text())
        assert set(response) == {"jsonrpc", "id", "result"}
        assert response["jsonrpc"] == "2.0" and response["id"] == 1
        if method == METHODS[0]:
            assert response["result"] == [_account(entry) for entry in pinned["blockAccessList"]]
        else:
            assert (
                "0x" + keccak256(bytes.fromhex(response["result"][2:])).hex()
                == pinned["blockAccessListHash"]
            )


def test_forged_access_list_commitment() -> None:
    # EIP-7928, State Transition Function: reject a list whose hash differs from the header.
    chain = replay_chain()
    fork, raw = chain.blocks[60]
    block = rlp.decode(raw)
    pinned = json.loads((FIXTURES / "bal" / "block-00060.json").read_text())
    assert "0x" + block[0][-2].hex() == pinned["blockAccessListHash"]
    block[0][-2] = bytes(32)
    forged = (fork, rlp.encode(block))
    zero = bytes(32)
    chain = replace(
        chain,
        blocks=(*chain.blocks[:60], forged),
        forkchoice=(block_hash(forged), zero, zero),
    )
    with raises(rpc.RpcError, "block 60: block invalid: wrongBlockAccessListHash") as error:
        chain.serve([_request(method, ["latest"]) for method in METHODS])
    assert error.value.code == 256


def test_future_schedule_keeps_past_answers(answers: dict[str, dict[str, Any]]) -> None:
    """A fork after the head cannot change the access list of a block already executed."""
    chain = replay_chain()
    chain = replace(
        chain,
        config={
            **chain.config,
            "activations": [*chain.config["activations"], ["hegota", "time", 700]],
        },
    )
    requests = [_request(method, ["0x3c"]) for method in METHODS]
    responses = chain.serve(requests)
    for request, text in zip(requests, responses, strict=True):
        assert text is not None
        assert json.loads(text) == answers[request]


def test_unsupported_block_fork_is_rejected() -> None:
    """A block at an unspecified fork cannot be read under the last supported fork's rules."""
    chain = replay_chain()
    chain = replace(chain, blocks=(("hegota", chain.blocks[0][1]), *chain.blocks[1:]))
    with raises(rpc.RpcError, "fork hegota not yet specified") as error:
        chain.serve([_request(METHODS[0], ["latest"])])
    assert error.value.code == 0


def test_unknown_after_pre_amsterdam_head() -> None:
    """A head before Amsterdam does not turn an unknown block into a known pre-fork block."""
    chain = replay_chain()
    zero = bytes(32)
    chain = replace(
        chain,
        blocks=chain.blocks[:57],
        forkchoice=(block_hash(chain.blocks[56]), zero, zero),
    )
    requests = [_request(method, ["0x39"]) for method in METHODS]
    responses = chain.serve(requests)
    parsed = [json.loads(text) for text in responses if text is not None]
    assert parsed == [
        {"jsonrpc": "2.0", "id": 1, "result": None},
        {"jsonrpc": "2.0", "id": 1, "error": {**NOT_FOUND, "data": "unknown block"}},
    ]


@pytest.mark.parametrize("block", ["0x3d", UNKNOWN])
def test_unknown(block: str, answers: dict[str, dict[str, Any]]) -> None:
    assert answers[_request(METHODS[0], [block])]["result"] is None
    assert answers[_request(METHODS[1], [block])]["error"] == {**NOT_FOUND, "data": "unknown block"}


@pytest.mark.parametrize("method", METHODS)
@pytest.mark.parametrize("block", ["0x0", "0x1b", "0x38", "earliest"])
def test_before_amsterdam(method: str, block: str, answers: dict[str, dict[str, Any]]) -> None:
    assert answers[_request(method, [block])]["error"] == {
        **NOT_FOUND,
        "data": "block predates Amsterdam",
    }


def test_pending(answers: dict[str, dict[str, Any]]) -> None:
    assert answers[_request(METHODS[0], ["pending"])]["result"] is None
    # The source leaves the raw getter's pending policy open; this view has no pending block.
    assert answers[_request(METHODS[1], ["pending"])]["error"] == {
        **NOT_FOUND,
        "data": "unknown block",
    }


@pytest.mark.parametrize("method", METHODS)
@pytest.mark.parametrize(("params", "reason"), BAD_PARAMS)
def test_bad_parameters(
    method: str, params: list[object], reason: str, answers: dict[str, dict[str, Any]]
) -> None:
    assert answers[_request(method, params)]["error"] == {**INVALID_PARAMS, "data": reason}


def test_pruning(answers: dict[str, dict[str, Any]]) -> None:
    chain = replay_chain()
    calls = [(method, ["latest"]) for method in METHODS]
    calls += [(method, ["0x1b"]) for method in METHODS]
    calls += [
        (METHODS[0], ["pending"]),
        (METHODS[0], ["0x39"]),
        ("eth_getHeaderByNumber", ["0x3c"]),
    ]
    requests = [_request(method, params) for method, params in calls]
    responses = rpc.serve(
        chain.config,
        chain.state,
        chain.blocks,
        chain.forkchoice,
        chain.network_id,
        requests,
        check_seal=False,
        pruned_access_lists=[27, 60],
    )
    parsed = [json.loads(text) for text in responses if text is not None]
    assert len(parsed) == len(requests)
    assert [answer["error"] for answer in parsed[:4]] == [
        PRUNED,
        PRUNED,
        {**NOT_FOUND, "data": "block predates Amsterdam"},
        {**NOT_FOUND, "data": "block predates Amsterdam"},
    ]
    assert parsed[4]["result"] is None
    for request, answer in zip(requests[5:], parsed[5:], strict=True):
        assert answer == answers[request]


def test_empty_encoding() -> None:
    # src/debug/getters.yaml at the pin: a block with no state access returns the RLP list 0xc0.
    assert rpc.encode_block_access_list([]) == b"\xc0"


CODE_CHANGE: dict[str, object] = {
    "address": ADDRESS,
    "storageChanges": [],
    "storageReads": [],
    "balanceChanges": [],
    "nonceChanges": [],
    "codeChanges": [{"index": "0x0", "code": "0x6000"}],
}


def test_code_change_encoding() -> None:
    # Source: ethereum/EIPs 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445, EIP-7928, RLP Encoding.
    # One account changes only its code to 0x6000 at index 0.
    # The change is c4 80 82 60 00; its list is c5 ..., the account df ..., the outer list e0 ... .
    expected = bytes.fromhex("e0df94" + "00" * 20 + "c0c0c0c0c5c480826000")
    assert rpc.encode_block_access_list([CODE_CHANGE]) == expected


def test_scalar_limits_and_bytecode_encoding() -> None:
    # EIP-7928 at EIPs 46976b2a, RLP Encoding: integers are minimal; bytecode keeps its bytes.
    # One account changes slot 1 to zero and reads slot 2; indexes, balance and nonce are maximal.
    # Account contents are 101 bytes (f8 65); the outer contents are 103 bytes (f8 67).
    account = {
        "address": ADDRESS,
        "storageChanges": [
            {
                "key": "0x" + "00" * 31 + "01",
                "changes": [{"index": "0xffffffff", "value": "0x" + "00" * 32}],
            }
        ],
        "storageReads": ["0x" + "00" * 31 + "02"],
        "balanceChanges": [{"index": "0xffffffff", "value": "0x" + "ff" * 32}],
        "nonceChanges": [{"index": "0xffffffff", "value": "0xffffffffffffffff"}],
        "codeChanges": [{"index": "0xffffffff", "code": "0x006000"}],
    }
    expected = bytes.fromhex(
        "f867f86594"
        + "00" * 20
        + "cac901c7c684ffffffff80"
        + "c102"
        + "e7e684ffffffffa0"
        + "ff" * 32
        + "cfce84ffffffff88"
        + "ff" * 8
        + "cac984ffffffff83006000"
    )
    assert rpc.encode_block_access_list([account]) == expected


@pytest.mark.parametrize(
    ("field", "value", "message"),
    [
        ("codeChanges", None, "codeChanges: not an array"),
        ("extra", [], "block access list: wrong fields"),
        ("extra", None, "block access list: wrong fields"),
        ("storageReads", ["0x00"], "storage word: 1 bytes, not 32"),
        ("storageChanges", [{"key": "0x00", "changes": []}], "storage word: 1 bytes, not 32"),
        ("balanceChanges", [{"index": "0x0", "value": hex(2**256)}], "value: above 2^256"),
        (
            "codeChanges",
            [{"index": "0x0", "code": b"\x60\x00"}],
            "block access list: not a JSON value",
        ),
        ("codeChanges", [{"index": "0x100000000", "code": "0x"}], "index: above 2^32"),
        ("nonceChanges", [{"index": "0x0", "value": "0x10000000000000000"}], "value: above 2^64"),
    ],
)
def test_malformed_list(field: str, value: object, message: str) -> None:
    account = deepcopy(CODE_CHANGE)
    account[field] = value
    with raises(rpc.RpcError, message) as error:
        rpc.encode_block_access_list([account])
    assert error.value.code == 32602
