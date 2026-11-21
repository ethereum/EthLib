"""Scripts of Engine API calls on one execution node, which keeps its blocks between calls."""

# The node starts from a Paris genesis block without accounts, as its valid head.
# Each payload is an empty block, so its state stays empty and its execution needs no account.

from typing import Any

from ethlib import engine
from ethlib.cryptography.keccak import keccak256
from ethlib.serialization import rlp

from .cases import BLOCK_FORKS, DEPOSIT_CONTRACT_ADDRESS

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
    """The second payload runs on the state that the first left."""
    responses = _run(_new_payload(B1), _new_payload(B2), _update(B2.hash, B1.hash, G))
    assert [r["response"]["result"]["status"] for r in responses[:2]] == ["VALID", "VALID"]
    assert responses[2]["forkchoice"] == _forkchoice(B2.hash, B1.hash, G)


def test_reorganization() -> None:
    """A sibling of the head runs on their common parent, and an update makes it the head."""
    responses = _run(
        _new_payload(B1), _update(B1.hash), _new_payload(B1_SIDE), _update(B1_SIDE.hash)
    )
    assert responses[2]["response"] == {"result": _status("VALID", B1_SIDE.hash)}
    assert responses[3]["forkchoice"] == _forkchoice(B1_SIDE.hash)


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
