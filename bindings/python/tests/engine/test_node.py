"""Scripts of Engine API calls on one execution node, which keeps its blocks between calls."""

# The node starts from a Paris genesis block without accounts, as its valid head.
# Each payload is an empty block, so its state stays empty and its execution needs no account.

from typing import Any

from ethlib import engine
from ethlib.cryptography.keccak import keccak256
from ethlib.serialization import rlp

from .cases import BLOCK_FORKS, DEPOSIT_CONTRACT_ADDRESS
from .test_terminal_block import CONFIG as POW_CONFIG, GENESIS as POW_GENESIS

# A Python value from Lean holds only integers that are not negative.
# So the negative code of an error object reaches Python as its decimal text.

CONFIG = {
    "chainId": 1,
    "depositContractAddress": DEPOSIT_CONTRACT_ADDRESS,
    "activations": [[fork, "block", 0] for fork in BLOCK_FORKS],
}

# The root of an empty trie, and the hash of an empty list of ommers.
EMPTY_ROOT = keccak256(rlp.encode(b""))
EMPTY_OMMERS = keccak256(rlp.encode([]))

GAS_LIMIT = 30_000_000
GENESIS_BASE_FEE = 1_000_000_000
ZERO = bytes(32)


def _number(n: int) -> bytes:
    """The bytes of a number for RLP: big-endian, without leading zeros."""
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _base_fee(number: int) -> int:
    """The base fee of an empty block: EIP-1559 lowers it by an eighth after each empty block."""
    fee = GENESIS_BASE_FEE
    for _ in range(number):
        fee -= fee // 8
    return fee


def _header(
    parent: bytes, number: int, *, extra: bytes = b"", state_root: bytes = EMPTY_ROOT
) -> bytes:
    """The RLP form of a Paris header with no transaction, at the time of its number."""
    return rlp.encode(
        [
            parent,
            EMPTY_OMMERS,
            bytes(20),
            state_root,
            EMPTY_ROOT,
            EMPTY_ROOT,
            bytes(256),
            b"",
            _number(number),
            _number(GAS_LIMIT),
            b"",
            _number(number),
            extra,
            ZERO,
            bytes(8),
            _number(_base_fee(number)),
        ]
    )


GENESIS = _header(ZERO, 0)
ANCHOR = ("paris", GENESIS, [])


def _hex(raw: bytes) -> str:
    """The Engine API data of bytes."""
    return "0x" + raw.hex()


class Block:
    """An empty block of a script: its header, its hash and its payload."""

    def __init__(
        self, parent: bytes, number: int, *, extra: bytes = b"", state_root: bytes = EMPTY_ROOT
    ) -> None:
        self.header = _header(parent, number, extra=extra, state_root=state_root)
        self.hash = keccak256(self.header)
        self.payload = {
            "parentHash": _hex(parent),
            "feeRecipient": _hex(bytes(20)),
            "stateRoot": _hex(state_root),
            "receiptsRoot": _hex(EMPTY_ROOT),
            "logsBloom": _hex(bytes(256)),
            "prevRandao": _hex(ZERO),
            "blockNumber": hex(number),
            "gasLimit": hex(GAS_LIMIT),
            "gasUsed": "0x0",
            "timestamp": hex(number),
            "extraData": _hex(extra),
            "baseFeePerGas": hex(_base_fee(number)),
            "blockHash": _hex(self.hash),
            "transactions": [],
        }


G = keccak256(GENESIS)
B1 = Block(G, 1)
B2 = Block(B1.hash, 2)
# A sibling of the first block, and a block whose state root its execution does not give.
B1_SIDE = Block(G, 1, extra=b"\x01")
BAD = Block(G, 1, extra=b"\x02", state_root=keccak256(b"not the state"))


def _new_payload(block: Block) -> dict[str, Any]:
    """The request of version 1 for a block."""
    return {"jsonrpc": "2.0", "id": 1, "method": "engine_newPayloadV1", "params": [block.payload]}


def _update(head: bytes, safe: bytes = ZERO, finalized: bytes = ZERO) -> dict[str, Any]:
    """The request of version 1 for a forkchoice state, without payload attributes."""
    state = {
        "headBlockHash": _hex(head),
        "safeBlockHash": _hex(safe),
        "finalizedBlockHash": _hex(finalized),
    }
    return {
        "jsonrpc": "2.0",
        "id": 1,
        "method": "engine_forkchoiceUpdatedV1",
        "params": [state, None],
    }


def _run(*requests: dict[str, Any]) -> list[dict[str, Any]]:
    """The responses and forkchoice states of a script on a node that knows the genesis block."""
    return engine.run_node(CONFIG, rlp.encode([]), ANCHOR, list(requests))


def _status(status: str, latest: bytes | None, error: str | None = None) -> dict[str, Any]:
    """A payload status, with its latest valid hash."""
    return {
        "status": status,
        "latestValidHash": None if latest is None else _hex(latest),
        "validationError": error,
    }


def _update_result(status: str, latest: bytes | None) -> dict[str, Any]:
    """The result of an update without a build."""
    return {"payloadStatus": _status(status, latest), "payloadId": None}


def _forkchoice(head: bytes, safe: bytes = ZERO, finalized: bytes = ZERO) -> dict[str, str]:
    """A forkchoice state as the node reports it."""
    return {
        "headBlockHash": _hex(head),
        "safeBlockHash": _hex(safe),
        "finalizedBlockHash": _hex(finalized),
    }


def test_payload_then_update() -> None:
    """A payload on the head is valid, and an update to it then moves the head."""
    payload, update = _run(_new_payload(B1), _update(B1.hash))
    assert payload == {
        "response": {"result": _status("VALID", B1.hash)},
        "forkchoice": _forkchoice(G),
    }
    assert update == {
        "response": {"result": _update_result("VALID", B1.hash)},
        "forkchoice": _forkchoice(B1.hash),
    }


def test_update_without_payload() -> None:
    """Without the payload first, the node does not know the head, so the update is syncing."""
    (update,) = _run(_update(B1.hash))
    assert update["response"] == {"result": _update_result("SYNCING", None)}
    assert update["forkchoice"] == _forkchoice(G)


def test_unknown_parent() -> None:
    """A payload whose parent the node does not know is syncing, and stays unknown."""
    payload, again = _run(_new_payload(B2), _new_payload(B2))
    assert payload["response"] == {"result": _status("SYNCING", None)}
    assert again["response"] == payload["response"]


def test_chain_of_two() -> None:
    """A payload off the head is accepted, and the update to it runs it on its parent's state."""
    responses = _run(_new_payload(B1), _new_payload(B2), _update(B2.hash, B1.hash, G))
    assert responses[0]["response"] == {"result": _status("VALID", B1.hash)}
    # The parent of the second payload is valid but is not the head, so it does not run yet.
    assert responses[1]["response"] == {"result": _status("ACCEPTED", None)}
    assert responses[2] == {
        "response": {"result": _update_result("VALID", B2.hash)},
        "forkchoice": _forkchoice(B2.hash, B1.hash, G),
    }


def test_reorganization() -> None:
    """A sibling of the head is accepted, and an update runs it and makes it the head."""
    responses = _run(
        _new_payload(B1),
        _update(B1.hash),
        _new_payload(B1_SIDE),
        _new_payload(B1_SIDE),
        _update(B1_SIDE.hash),
    )
    assert responses[1]["forkchoice"] == _forkchoice(B1.hash)
    # The parent of the sibling is known and valid but is not the head: G <- B1, head B1.
    assert responses[2]["response"] == {"result": _status("ACCEPTED", None)}
    assert responses[3]["response"] == responses[2]["response"]
    assert responses[4] == {
        "response": {"result": _update_result("VALID", B1_SIDE.hash)},
        "forkchoice": _forkchoice(B1_SIDE.hash),
    }


def test_accepted_payload_that_fails() -> None:
    """An accepted payload that fails when the update runs it is invalid, and the head stays."""
    responses = _run(_new_payload(B1), _update(B1.hash), _new_payload(BAD), _update(BAD.hash))
    assert responses[2]["response"] == {"result": _status("ACCEPTED", None)}
    assert responses[3] == {
        "response": {"result": _update_result("INVALID", G)},
        "forkchoice": _forkchoice(B1.hash),
    }


def test_accepted_payload_sent_again_on_the_head() -> None:
    """An accepted payload sent again once its parent is the head runs, and is valid."""
    side = Block(G, 1, extra=b"\x03")
    responses = _run(
        _new_payload(B1), _update(B1.hash), _new_payload(side), _update(G), _new_payload(side)
    )
    assert responses[2]["response"] == {"result": _status("ACCEPTED", None)}
    assert responses[3]["forkchoice"] == _forkchoice(G)
    assert responses[4]["response"] == {"result": _status("VALID", side.hash)}


def test_descendant_of_an_invalid_payload() -> None:
    """A child of an invalid payload is invalid, with the latest valid block of its chain."""
    # G <- B1 <- B2, where B2 fails execution, then B3 on B2 and B4 on B3.
    b2 = Block(B1.hash, 2, state_root=keccak256(b"not the state"))
    b3 = Block(b2.hash, 3)
    b4 = Block(b3.hash, 4)
    responses = _run(
        _new_payload(B1),
        _update(B1.hash),
        _new_payload(b2),
        _new_payload(b3),
        _new_payload(b4),
        _update(b4.hash),
    )
    assert responses[2]["response"]["result"]["status"] == "INVALID"
    assert responses[2]["response"]["result"]["latestValidHash"] == _hex(B1.hash)
    assert responses[3]["response"] == {"result": _status("INVALID", B1.hash)}
    assert responses[4]["response"] == {"result": _status("INVALID", B1.hash)}
    assert responses[5] == {
        "response": {"result": _update_result("INVALID", B1.hash)},
        "forkchoice": _forkchoice(B1.hash),
    }


def test_child_of_a_payload_on_a_block_that_is_not_terminal() -> None:
    """A payload on a non-terminal block of proof of work, and its child, get the zero hash."""
    # The London genesis has a total difficulty of 99, below the terminal total of 100.
    b1 = Block(keccak256(POW_GENESIS), 1)
    b2 = Block(b1.hash, 2)
    payload, child = engine.run_node(
        POW_CONFIG,
        rlp.encode([]),
        ("london", POW_GENESIS, []),
        [_new_payload(b1), _new_payload(b2)],
        terminal_total_difficulty=100,
        total_difficulty=99,
    )
    assert payload["response"]["result"]["status"] == "INVALID"
    assert payload["response"]["result"]["latestValidHash"] == _hex(ZERO)
    assert child["response"] == {"result": _status("INVALID", ZERO)}


def test_update_to_a_child_of_a_failed_payload() -> None:
    """A child of an accepted payload that fails is invalid when an update names it."""
    child = Block(BAD.hash, 2)
    responses = _run(
        _new_payload(B1),
        _update(B1.hash),
        _new_payload(BAD),
        _new_payload(child),
        _update(child.hash),
    )
    assert [r["response"]["result"]["status"] for r in responses[2:4]] == ["ACCEPTED"] * 2
    assert responses[4] == {
        "response": {"result": _update_result("INVALID", G)},
        "forkchoice": _forkchoice(B1.hash),
    }


def test_update_to_an_accepted_child_of_an_accepted_payload() -> None:
    """An update runs the accepted blocks of the chain of its head, oldest first."""
    b2_side = Block(B1_SIDE.hash, 2)
    responses = _run(
        _new_payload(B1),
        _update(B1.hash),
        _new_payload(B1_SIDE),
        _new_payload(b2_side),
        _update(b2_side.hash),
    )
    assert [r["response"]["result"]["status"] for r in responses[2:4]] == ["ACCEPTED"] * 2
    assert responses[4] == {
        "response": {"result": _update_result("VALID", b2_side.hash)},
        "forkchoice": _forkchoice(b2_side.hash),
    }


def test_invalid_payload_is_remembered() -> None:
    """A payload that fails execution is invalid, again when resent, and never becomes the head."""
    payload, again, update = _run(_new_payload(BAD), _new_payload(BAD), _update(BAD.hash))
    assert payload["response"]["result"]["status"] == "INVALID"
    assert payload["response"]["result"]["latestValidHash"] == _hex(G)
    assert again["response"] == {"result": _status("INVALID", G)}
    assert update["response"] == {"result": _update_result("INVALID", G)}
    assert update["forkchoice"] == _forkchoice(G)


def test_invalid_forkchoice_state() -> None:
    """A safe block off the chain of the head is an error of the update, which keeps the head."""
    payload, update = _run(_new_payload(B1), _update(B1.hash, safe=B1_SIDE.hash))
    assert payload["response"]["result"]["status"] == "VALID"
    error = {"code": "-38002", "message": "Invalid forkchoice state", "data": None}
    assert update["response"] == {"error": error}
    assert update["forkchoice"] == _forkchoice(G)


def test_unknown_payload_id() -> None:
    """A node that started no build answers a request for a payload with an unknown payload ID."""
    request = {
        "jsonrpc": "2.0",
        "id": 1,
        "method": "engine_getPayloadV1",
        "params": [_hex(bytes(8))],
    }
    (response,) = _run(request)
    error = {"code": "-38001", "message": "Unknown payload", "data": None}
    assert response == {"response": {"error": error}, "forkchoice": _forkchoice(G)}
