"""The official JSON-RPC fixtures, answered by a chain view built from the test chain."""

import json
from collections.abc import Callable
from dataclasses import replace
from pathlib import Path
from typing import Any, Final

import pytest

from ethlib.execution import rpc
from ethlib.serialization import rlp
from raising import raises

from .chain import FIXTURES, ReplayChain, block_hash, read_fixture, replay_chain

# Each method that the view serves, with the schema of its result in `src/eth` of the source.
RESULT_SCHEMAS: Final[dict[str, rpc.Schema]] = {
    "eth_blockNumber": "uint",
    "eth_chainId": "uint",
    "net_version": "uintDecimal",
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
        # Every result reads under the schema of its method.
        rpc.read_param(RESULT_SCHEMAS[fixture.method], got["result"])
        # A fixture marked speconly is checked against the schema only, as the source says.
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
