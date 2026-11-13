"""The method `eth_sendRawTransaction`, answered by the view of the test chain."""

import json
from pathlib import Path
from typing import Any, Final

import pytest

from ethlib.cryptography.keccak import keccak256
from ethlib.serialization import rlp

from .chain import FIXTURES, read_fixture, replay_chain

# Every fixture of the method.
SENT: Final = sorted((FIXTURES / "eth_sendRawTransaction").glob("*.io"))


def _raw(path: Path) -> bytes:
    """The raw transaction that the request of a fixture sends."""
    (exchange,) = read_fixture(path).exchanges
    (param,) = json.loads(exchange.request)["params"]
    return bytes.fromhex(param.removeprefix("0x"))


def _send(raw: bytes) -> dict[str, Any]:
    request = {"jsonrpc": "2.0", "id": 1, "method": "eth_sendRawTransaction"}
    request["params"] = ["0x" + raw.hex()]
    (response,) = replay_chain().serve([json.dumps(request)])
    assert response is not None
    return json.loads(response)


def _error(raw: bytes) -> dict[str, Any]:
    answer = _send(raw)
    assert set(answer) == {"jsonrpc", "id", "error"}
    return answer["error"]


def _code(raw: bytes) -> int:
    return _error(raw)["code"]


def _fixture_fields(name: str) -> list[Any]:
    """The RLP fields of the raw transaction of a fixture, after its type byte if it has one."""
    raw = _raw(FIXTURES / "eth_sendRawTransaction" / name)
    return rlp.decode(raw[1:] if raw[0] < 0xC0 else raw)


def _chain_transaction(number: int, index: int) -> bytes:
    """The raw form of a transaction of a block of the chain: its envelope."""
    _, block = replay_chain().blocks[number]
    item = rlp.decode(block)[1][index]
    # A legacy transaction is an RLP list; a typed one is already its envelope bytes.
    return rlp.encode(item) if isinstance(item, list) else item


def test_every_fixture_is_sent() -> None:
    """The directory holds the five fixtures of the source, so none is skipped silently."""
    assert len(SENT) == 5


@pytest.mark.parametrize("path", SENT, ids=lambda path: path.stem)
def test_fixture(path: Path) -> None:
    """The view accepts the transaction of each fixture and returns its hash."""
    (exchange,) = read_fixture(path).exchanges
    (response,) = replay_chain().serve([exchange.request])
    assert response is not None
    assert json.loads(response) == exchange.response


@pytest.mark.parametrize("path", SENT, ids=lambda path: path.stem)
def test_hash(path: Path) -> None:
    """The hash is that of the raw bytes, but for a blob transaction in its network form."""
    raw = _raw(path)
    result = _send(raw)["result"]
    # The fixtures fix these hashes too; this test shows which bytes they hash.
    if raw[0] != 3:
        assert result == "0x" + keccak256(raw).hex()
        return
    # The network form is 0x03 || rlp([tx_payload_body, wrapper_version, blobs, ...]).
    body, version, blobs, commitments, proofs = rlp.decode(raw[1:])
    assert (version, len(blobs), len(commitments), len(proofs)) == (b"\x01", 1, 1, 128)
    assert result == "0x" + keccak256(b"\x03" + rlp.encode(body)).hex()
    assert result != "0x" + keccak256(raw).hex()


def test_nonce_too_low() -> None:
    """A transaction of the head has a nonce below that of its sender after the head."""
    # Its fee cap covers the base fee of the head, so it covers the lower base fee after it.
    # A blob transaction would need its network form, so the test takes one of another type.
    _, block = replay_chain().blocks[60]
    count = len(rlp.decode(block)[1])
    raws = [_chain_transaction(60, index) for index in range(count)]
    raw = next(raw for raw in raws if raw[0] != 3)
    assert _code(raw) == 1


def test_blob_transaction_without_blobs() -> None:
    """A blob transaction must come in its network form, not in the form of a block."""
    # Block 42 holds one blob transaction.
    _, block = replay_chain().blocks[42]
    (item,) = [item for item in rlp.decode(block)[1] if isinstance(item, bytes) and item[0] == 3]
    error = _error(item)
    assert error["code"] == -32000
    assert error["data"].startswith("EthLib.Execution.Transactions.TransactionError.decoding")


def _blob_form() -> list[Any]:
    return _fixture_fields("send-blob-tx.io")


def test_blob_proof_count() -> None:
    """A network form with one cell proof too few has counts that do not match."""
    body, version, blobs, commitments, proofs = _blob_form()
    raw = b"\x03" + rlp.encode([body, version, blobs, commitments, proofs[:-1]])
    error = {"code": -32000, "message": "Invalid input"}
    error["data"] = "the counts of blobs, commitments and proofs do not match"
    assert _error(raw) == error


def test_blob_versioned_hash() -> None:
    """A commitment that does not hash to the versioned hash of its blob is invalid input."""
    body, version, blobs, commitments, proofs = _blob_form()
    changed = bytes([commitments[0][0] ^ 1]) + commitments[0][1:]
    raw = b"\x03" + rlp.encode([body, version, blobs, [changed], proofs])
    error = {"code": -32000, "message": "Invalid input"}
    error["data"] = "a commitment does not hash to its versioned hash"
    assert _error(raw) == error


def _dynamic_fee(changes: dict[int, int]) -> bytes:
    """The dynamic fee transaction of a fixture with some fields changed, and the same signature.

    The signature then names another sender, which holds no ether.
    """
    fields = _fixture_fields("send-dynamic-fee-transaction.io")
    for index, value in changes.items():
        fields[index] = value.to_bytes((value.bit_length() + 7) // 8, "big")
    return b"\x02" + rlp.encode(fields)


# The fields of a dynamic fee transaction, from EIP-1559.
CHAIN_ID, PRIORITY_FEE, FEE_CAP, GAS = 0, 2, 3, 4

# Each changed transaction, with the code of the check that it fails.
CHECKS = [
    pytest.param({GAS: 1}, 800, id="intrinsic-gas"),
    pytest.param({PRIORITY_FEE: 2, FEE_CAP: 1}, 804, id="priority-fee-above-cap"),
    pytest.param({PRIORITY_FEE: 0, FEE_CAP: 1}, 806, id="fee-cap-below-base-fee"),
    pytest.param({CHAIN_ID: 1}, -32003, id="wrong-chain-id"),
]


@pytest.mark.parametrize(("changes", "code"), CHECKS)
def test_failed_check(changes: dict[int, int], code: int) -> None:
    """A failed inclusion check gets the code that names its condition, or -32003."""
    assert _code(_dynamic_fee(changes)) == code


def test_invalid_signature() -> None:
    """A signature with an `s` of 0 names no sender."""
    fields = rlp.decode(_raw(FIXTURES / "eth_sendRawTransaction/send-legacy-transaction.io"))
    fields[8] = b""
    assert _code(rlp.encode(fields)) == 1001


def test_insufficient_funds() -> None:
    """A changed value makes the signature name another sender, which holds nothing."""
    fields = rlp.decode(_raw(FIXTURES / "eth_sendRawTransaction/send-legacy-transaction.io"))
    fields[4] = b"\x01"
    assert _code(rlp.encode(fields)) == 809


@pytest.mark.parametrize(
    "raw", [b"", b"\x01", b"\x7f\x00"], ids=["empty", "type-only", "unknown-type"]
)
def test_undecodable(raw: bytes) -> None:
    """Bytes that hold no transaction are invalid input."""
    assert _code(raw) == -32000
