"""Block access-list queries against the pinned execution-apis chain and access lists."""

import json
from collections.abc import Sequence
from copy import deepcopy
from typing import Any

import pytest

from ethlib.cryptography.keccak import keccak256
from ethlib.execution import rpc
from raising import raises

from .chain import FIXTURES, block_hash, replay_chain

METHODS = ("eth_getBlockAccessList", "debug_getRawBlockAccessList")
UNKNOWN = "0x" + "11" * 32
ADDRESS = "0x" + "00" * 20
BAD_PARAMS: list[list[object]] = [
    [],
    ["latest", "extra"],
    [True],
    ["0x03c"],
    [{"blockNumber": "0x3c", "blockHash": UNKNOWN}],
]


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
    calls += [(method, params) for method in METHODS for params in BAD_PARAMS]
    requests = [_request(method, params) for method, params in calls]
    texts = chain.serve(requests)
    assert all(text is not None for text in texts)
    return {
        request: json.loads(text)
        for request, text in zip(requests, texts, strict=True)
        if text is not None
    }


def _word(value: str) -> str:
    return f"0x{int(value, 16):064x}"


def _account(entry: dict[str, Any]) -> dict[str, Any]:
    # The pinned tools/chain/bal files use another JSON form than the method's schema.
    # None of these four blocks changes code; the separate code-change case covers that field.
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
    assert decoded == [_account(entry) for entry in pinned["blockAccessList"]]
    assert (
        "0x" + keccak256(raw).hex()
        == pinned["blockAccessListHash"]
        == header["blockAccessListHash"]
    )
    assert rpc.encode_block_access_list(decoded) == raw
    assert header["hash"] == pinned["hash"]


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


@pytest.mark.parametrize("block", ["0x3d", UNKNOWN])
def test_unknown(block: str, answers: dict[str, dict[str, Any]]) -> None:
    assert answers[_request(METHODS[0], [block])]["result"] is None
    assert answers[_request(METHODS[1], [block])]["error"]["code"] == -32001


@pytest.mark.parametrize("method", METHODS)
@pytest.mark.parametrize("block", ["0x0", "0x1b", "0x38", "earliest"])
def test_before_amsterdam(method: str, block: str, answers: dict[str, dict[str, Any]]) -> None:
    assert answers[_request(method, [block])]["error"]["code"] == -32001


def test_pending(answers: dict[str, dict[str, Any]]) -> None:
    assert answers[_request(METHODS[0], ["pending"])]["result"] is None
    # The source leaves the raw getter's pending policy open; this view has no pending block.
    assert answers[_request(METHODS[1], ["pending"])]["error"]["code"] == -32001


@pytest.mark.parametrize("method", METHODS)
@pytest.mark.parametrize(
    "params",
    [[], ["latest", "extra"], [True], ["0x03c"], [{"blockNumber": "0x3c", "blockHash": UNKNOWN}]],
)
def test_bad_parameters(
    method: str, params: list[object], answers: dict[str, dict[str, Any]]
) -> None:
    assert answers[_request(method, params)]["error"]["code"] == -32602


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
    assert [answer["error"]["code"] for answer in parsed[:4]] == [4444, 4444, -32001, -32001]
    assert parsed[4]["result"] is None
    for request, answer in zip(requests[5:], parsed[5:], strict=True):
        assert answer == answers[request]


def test_empty_encoding() -> None:
    # The raw getter's example in src/debug/getters.yaml at the pin gives [] as RLP 0xc0.
    assert rpc.encode_block_access_list([]) == b"\xc0"


CODE_CHANGE: dict[str, Any] = {
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


@pytest.mark.parametrize(
    ("field", "value", "message"),
    [
        ("codeChanges", None, "codeChanges: not an array"),
        ("extra", [], "block access list: wrong fields"),
        ("extra", None, "block access list: wrong fields"),
        ("storageReads", ["0x00"], "storage word: 1 bytes, not 32"),
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
