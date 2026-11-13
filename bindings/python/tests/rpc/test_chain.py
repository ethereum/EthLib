"""The official JSON-RPC fixtures, answered by a chain view built from the test chain."""

import json
from collections.abc import Callable
from dataclasses import replace
from pathlib import Path
from typing import Any, Final

import pytest

from ethlib.cryptography.keccak import keccak256
from ethlib.execution import rpc, trie
from ethlib.serialization import rlp
from raising import raises

from .chain import FIXTURES, ReplayChain, block_hash, read_fixture, replay_chain

# Each method that the view serves, with the schema of its result in `src/eth` of the source.
# A result that is an object has no reader of its schema, so it maps to None.
RESULT_SCHEMAS: Final[dict[str, rpc.Schema | None]] = {
    "eth_blockNumber": "uint",
    "eth_chainId": "uint",
    "net_version": "uintDecimal",
    "eth_getTransactionByHash": None,
    "eth_getTransactionByBlockHashAndIndex": None,
    "eth_getTransactionByBlockNumberAndIndex": None,
    "eth_getHeaderByHash": None,
    "eth_getHeaderByNumber": None,
    "eth_getBlockByHash": None,
    "eth_getBlockByNumber": None,
    "eth_getBlockTransactionCountByHash": "uint",
    "eth_getBlockTransactionCountByNumber": "uint",
    "debug_getRawHeader": "bytes",
    "debug_getRawBlock": "bytes",
    "debug_getRawTransaction": "bytes",
    "debug_getRawReceipts": None,
}

# Every fixture of a method that the view serves.
SERVED: Final = sorted(
    path for method in RESULT_SCHEMAS for path in (FIXTURES / method).glob("*.io")
)


@pytest.fixture(scope="module")
def answers() -> dict[str, dict[str, Any]]:
    """The response of the view to each request of the served fixtures, by its text."""
    requests = sorted(
        {exchange.request for path in SERVED for exchange in read_fixture(path).exchanges}
    )
    responses = replay_chain().serve(requests)
    answers = {}
    for request, text in zip(requests, responses, strict=True):
        assert text is not None, request
        answers[request] = json.loads(text)
    return answers


def test_every_method_has_fixtures() -> None:
    """Each served method has a fixture, so a missing directory does not pass silently."""
    assert {path.parent.name for path in SERVED} == set(RESULT_SCHEMAS)


@pytest.mark.parametrize("path", SERVED, ids=lambda path: f"{path.parent.name}/{path.stem}")
def test_fixture(path: Path, answers: dict[str, dict[str, Any]]) -> None:
    """The view answers each request of the fixture as the fixture expects."""
    fixture = read_fixture(path)
    for exchange in fixture.exchanges:
        got, expected = answers[exchange.request], exchange.response
        assert got["jsonrpc"] == "2.0"
        assert got["id"] == expected["id"]
        if "error" in expected:
            # The source fixes the code of an error, and its data where a fixture gives it.
            assert set(got) == {"jsonrpc", "id", "error"}
            assert got["error"]["code"] == expected["error"]["code"]
            if "data" in expected["error"]:
                assert got["error"]["data"] == expected["error"]["data"]
            continue
        assert set(got) == {"jsonrpc", "id", "result"}
        # Every result reads under the schema of its method, when a reader has one.
        schema = RESULT_SCHEMAS[fixture.method]
        if schema is not None:
            rpc.read_param(schema, got["result"])
        # A fixture marked speconly is checked against the schema only, as the source says.
        # Without a reader of the schema, such a fixture would check nothing, so none may exist.
        assert schema is not None or not fixture.speconly
        if not fixture.speconly:
            assert got["result"] == expected["result"]


def test_chain_links() -> None:
    """The chain is a genesis block, the parent of the first block, then 60 blocks to the head."""
    chain = replay_chain()
    assert len(chain.blocks) == 61
    _, first = chain.blocks[1]
    # The parent hash is the first field of the header of the first block.
    assert rlp.decode(first)[0][0] == block_hash(chain.blocks[0])
    assert chain.forkchoice[0] == block_hash(chain.blocks[-1])


def _answer(text: str) -> Any:
    (response,) = replay_chain().serve([text])
    assert response is not None
    return json.loads(response)


def _error(text: str) -> dict[str, Any]:
    answer = _answer(text)
    assert set(answer) == {"jsonrpc", "id", "error"}
    return answer


def _transaction_hash(block: rpc.ChainBlock, index: int) -> bytes:
    """The hash of a transaction of a block, from the raw block: the hash of its envelope."""
    _, raw = block
    item = rlp.decode(raw)[1][index]
    # A legacy transaction is an RLP list; a typed one is already its envelope bytes.
    return keccak256(rlp.encode(item) if isinstance(item, list) else item)


def _call(method: str, params: list[object]) -> Any:
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    answer = _answer(json.dumps(request))
    assert set(answer) == {"jsonrpc", "id", "result"}
    return answer["result"]


def test_transaction_at_index() -> None:
    """Both lookups by block and index read the transaction at that index, not the first one."""
    chain = replay_chain()
    expected = "0x" + _transaction_hash(chain.blocks[1], 1).hex()
    by_hash = "0x" + block_hash(chain.blocks[1]).hex()
    for method, block in [
        ("eth_getTransactionByBlockNumberAndIndex", "0x1"),
        ("eth_getTransactionByBlockHashAndIndex", by_hash),
    ]:
        result = _call(method, [block, "0x1"])
        assert result["hash"] == expected
        assert result["transactionIndex"] == "0x1"
        assert result["blockNumber"] == "0x1"
        # The lookup by hash returns the same object.
        assert _call("eth_getTransactionByHash", [expected]) == result


def test_headers() -> None:
    """A block has one header by number and by hash, with its hash and one key per RLP item."""
    chain = replay_chain()
    hashes = ["0x" + block_hash(block).hex() for block in chain.blocks]
    by_number = [("eth_getHeaderByNumber", hex(number)) for number in range(len(hashes))]
    by_hash = [("eth_getHeaderByHash", block) for block in hashes]
    requests = [
        json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": [param]})
        for method, param in by_number + by_hash
    ]
    texts = chain.serve(requests)
    results = [json.loads(text)["result"] for text in texts if text is not None]
    assert len(results) == 2 * len(hashes)
    headers = results[: len(hashes)]
    assert headers == results[len(hashes) :]
    for number, ((_, raw), header) in enumerate(zip(chain.blocks, headers, strict=True)):
        assert header["hash"] == hashes[number]
        assert header["number"] == hex(number)
        # The object holds the hash and one key for each field of the RLP header, none other.
        assert len(header) == len(rlp.decode(raw)[0]) + 1


def test_blocks() -> None:
    """A block object holds its header and lists its transaction hashes, which give its count."""
    chain = replay_chain()
    hashes = ["0x" + block_hash(block).hex() for block in chain.blocks]
    calls = [
        call
        for number, block in enumerate(hashes)
        for call in [
            ("eth_getBlockByNumber", [hex(number), False]),
            ("eth_getBlockByHash", [block, True]),
            ("eth_getHeaderByHash", [block]),
            ("eth_getBlockTransactionCountByNumber", [hex(number)]),
        ]
    ]
    requests = [
        json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params})
        for method, params in calls
    ]
    texts = chain.serve(requests)
    results = [json.loads(text)["result"] for text in texts if text is not None]
    assert len(results) == 4 * len(hashes)
    for number in range(len(hashes)):
        short, full, header, count = results[4 * number : 4 * number + 4]
        assert {key: short[key] for key in header} == header
        assert {key: full[key] for key in header} == header
        assert [entry["hash"] for entry in full["transactions"]] == short["transactions"]
        assert count == hex(len(short["transactions"]))


def test_raw_getters() -> None:
    """Each raw block is the RLP form of the block, and its parts match the hashes and roots."""
    chain = replay_chain()
    transactions = [
        "0x" + _transaction_hash(block, index).hex()
        for block in chain.blocks
        for index in range(len(rlp.decode(block[1])[1]))
    ]
    calls = [
        call
        for number in range(len(chain.blocks))
        for call in [
            ("debug_getRawBlock", [hex(number)]),
            ("debug_getRawHeader", [hex(number)]),
            ("debug_getRawReceipts", [hex(number)]),
        ]
    ] + [("debug_getRawTransaction", [transaction]) for transaction in transactions]
    requests = [
        json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params})
        for method, params in calls
    ]
    texts = chain.serve(requests)
    results = [json.loads(text)["result"] for text in texts if text is not None]
    assert len(results) == len(calls)
    for number, block in enumerate(chain.blocks):
        raw_block, raw_header, raw_receipts = results[3 * number : 3 * number + 3]
        _, raw = block
        assert raw_block == "0x" + raw.hex()
        assert keccak256(bytes.fromhex(raw_header[2:])) == block_hash(block)
        # One receipt for each transaction, whose trie by index has the receipts root of the header.
        header, transactions_of_block, *_ = rlp.decode(raw)
        assert len(raw_receipts) == len(transactions_of_block)
        entries = [
            # An index is the RLP of its minimal big-endian bytes, so 0 is the empty string.
            (
                rlp.encode(index.to_bytes((index.bit_length() + 7) // 8, "big")),
                bytes.fromhex(receipt[2:]),
            )
            for index, receipt in enumerate(raw_receipts)
        ]
        assert trie.root(entries) == header[5]
    # The bytes of each transaction hash to the hash that names it in the request.
    raw_transactions = results[3 * len(chain.blocks) :]
    assert len(raw_transactions) == len(transactions) > 0
    for transaction, raw_transaction in zip(transactions, raw_transactions, strict=True):
        assert "0x" + keccak256(bytes.fromhex(raw_transaction[2:])).hex() == transaction


# Each raw getter asked for a block or a transaction that the view does not hold.
# The test chain holds blocks 0 to 60, so 0x3d is the first number that it does not hold.
UNKNOWN = [
    pytest.param("debug_getRawHeader", ["0x3d"], "unknown block", id="header"),
    pytest.param("debug_getRawBlock", ["0x3e8"], "unknown block", id="block"),
    pytest.param("debug_getRawReceipts", ["0x3d"], "unknown block", id="receipts-number"),
    pytest.param("debug_getRawReceipts", ["0x" + "11" * 32], "unknown block", id="receipts-hash"),
    pytest.param("debug_getRawTransaction", ["0x" + "11" * 32], "unknown transaction", id="tx"),
    # The view built from the test chain has no pending block.
    pytest.param("debug_getRawHeader", ["pending"], "unknown block", id="pending"),
]


@pytest.mark.parametrize(("method", "params", "data"), UNKNOWN)
def test_raw_unknown(method: str, params: list[object], data: str) -> None:
    """A raw getter has the code -32001 for what the view does not hold."""
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    answer = _error(json.dumps(request))
    assert answer["error"] == {"code": -32001, "message": "Resource not found", "data": data}


def test_raw_tags() -> None:
    """The tags latest and earliest name the head and the lowest block."""
    chain = replay_chain()
    assert _call("debug_getRawBlock", ["latest"]) == "0x" + chain.blocks[-1][1].hex()
    assert _call("debug_getRawBlock", ["earliest"]) == "0x" + chain.blocks[0][1].hex()


def test_pending_header() -> None:
    """The header of the tag `pending` is null, as the method says."""
    assert _call("eth_getHeaderByNumber", ["pending"]) is None


# Each lookup by block and index that finds no transaction, so its result is null.
NOT_FOUND = [
    pytest.param("eth_getTransactionByBlockNumberAndIndex", ["0x3e8", "0x0"], id="unknown-number"),
    pytest.param(
        "eth_getTransactionByBlockHashAndIndex", ["0x" + "11" * 32, "0x0"], id="unknown-hash"
    ),
    pytest.param(
        "eth_getTransactionByBlockNumberAndIndex", ["0x1", "0x10000000000000000"], id="past-end"
    ),
    pytest.param("eth_getTransactionByBlockNumberAndIndex", ["0x0", "0x0"], id="empty-block"),
]


@pytest.mark.parametrize(("method", "params"), NOT_FOUND)
def test_transaction_not_found(method: str, params: list[object]) -> None:
    """A block that the view does not hold, or an index past its end, gives null."""
    assert _call(method, params) is None


def test_unknown_method() -> None:
    """A method that the view does not serve has the code -32601, with its name as data."""
    answer = _error('{"jsonrpc":"2.0","id":7,"method":"eth_mining"}')
    assert answer["id"] == 7
    assert answer["error"] == {"code": -32601, "message": "Method not found", "data": "eth_mining"}


def test_extra_parameter() -> None:
    """A method with no parameters rejects one, with the code -32602."""
    answer = _error('{"jsonrpc":"2.0","id":"a","method":"eth_chainId","params":[1]}')
    assert answer["id"] == "a"
    assert answer["error"] == {
        "code": -32602,
        "message": "Invalid params",
        "data": "the method takes no parameter",
    }


def test_not_json() -> None:
    """A text that is not JSON has the code -32700, and the identifier null."""
    answer = _error('{"jsonrpc":"2.0",')
    assert answer["id"] is None
    assert set(answer["error"]) == {"code", "message", "data"}
    assert answer["error"]["code"] == -32700
    assert answer["error"]["message"] == "Parse error"


def test_not_a_request() -> None:
    """A JSON value that is not a request has the code -32600, and its identifier when it reads."""
    answer = _error('{"jsonrpc":"1.0","id":1,"method":"eth_chainId"}')
    assert answer["id"] == 1
    assert answer["error"] == {
        "code": -32600,
        "message": "Invalid Request",
        "data": "request: jsonrpc is not 2.0",
    }


def test_notification() -> None:
    """A request without an identifier is a notification, and gets no response."""
    assert replay_chain().serve(['{"jsonrpc":"2.0","method":"eth_chainId"}']) == [None]


def test_batch() -> None:
    """A batch gets the responses to its requests, without those of its notifications."""
    batch = (
        '[{"jsonrpc":"2.0","id":1,"method":"eth_chainId"},'
        '{"jsonrpc":"2.0","method":"eth_blockNumber"},'
        '{"jsonrpc":"2.0","id":2,"method":"eth_blockNumber"}]'
    )
    assert _answer(batch) == [
        {"jsonrpc": "2.0", "id": 1, "result": "0xc72dd9d5e883e"},
        {"jsonrpc": "2.0", "id": 2, "result": "0x3c"},
    ]


def test_batch_of_notifications() -> None:
    """A batch of notifications gets no response."""
    batch = '[{"jsonrpc":"2.0","method":"eth_chainId"}]'
    assert replay_chain().serve([batch]) == [None]


def test_empty_batch() -> None:
    """An empty batch is an invalid request."""
    answer = _error("[]")
    assert answer["id"] is None
    assert answer["error"] == {
        "code": -32600,
        "message": "Invalid Request",
        "data": "batch: empty array",
    }


def test_invalid_request_keeps_its_identifier() -> None:
    """An invalid request whose identifier reads carries it back."""
    answer = _error('{"jsonrpc":"2.0","id":5,"method":"eth_chainId","extra":1}')
    assert answer["id"] == 5
    assert answer["error"] == {
        "code": -32600,
        "message": "Invalid Request",
        "data": "request: a member other than jsonrpc, id, method and params",
    }


def _build(chain: ReplayChain, *, check_seal: bool = False) -> None:
    """Build a view from the chain, and answer no request."""
    rpc.serve(
        chain.config,
        chain.state,
        chain.blocks,
        chain.forkchoice,
        chain.network_id,
        [],
        check_seal=check_seal,
    )


# Each input that builds no view, with the message and the code of its error.
# A block error carries its code; any other bad input has code 0.
BAD_INPUTS = [
    pytest.param(
        lambda c: replace(c, forkchoice=(block_hash(c.blocks[-2]),) * 3),
        "the head is not the last block",
        0,
        id="head-not-last",
    ),
    pytest.param(
        lambda c: replace(c, state=rlp.encode([])),
        "the state is not the state of the lowest block",
        0,
        id="state-mismatch",
    ),
    pytest.param(lambda c: replace(c, blocks=()), "no block", 0, id="no-block"),
    pytest.param(
        lambda c: replace(c, blocks=(("frontier", c.blocks[0][1]),) + c.blocks[1:]),
        "the lowest block is not at its active fork",
        0,
        id="lowest-fork",
    ),
    pytest.param(
        lambda c: replace(c, blocks=c.blocks[:1] + c.blocks[2:]),
        "block 2: block invalid: wrongNumber",
        207,
        id="out-of-order",
    ),
]


@pytest.mark.parametrize(("change", "message", "code"), BAD_INPUTS)
def test_bad_input(change: Callable[[ReplayChain], ReplayChain], message: str, code: int) -> None:
    """An input that breaks a rule of the view builds no view, and says which rule."""
    with raises(rpc.RpcError, message) as error:
        _build(change(replay_chain()))
    assert error.value.code == code


def test_seal_checked() -> None:
    """With the seal checked, the first block fails, since the test chain carries no real seal."""
    pow_error = "EthLib.Execution.Blocks.PowError.wrongMixDigest"
    with raises(rpc.RpcError, f"block 1: block invalid: proofOfWork ({pow_error})") as error:
        _build(replay_chain(), check_seal=True)
    assert error.value.code == 216


def test_network_id() -> None:
    """The network ID is an input of the view, which net_version answers in decimal."""
    chain = replace(replay_chain(), network_id=1)
    (response,) = chain.serve(['{"jsonrpc":"2.0","id":1,"method":"net_version"}'])
    assert response is not None
    assert json.loads(response) == {"jsonrpc": "2.0", "id": 1, "result": "1"}
