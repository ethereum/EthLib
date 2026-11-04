"""Proof verification against one `eth_getProof` response of ethereum/execution-apis."""

# The response proves one account in the state of block 60 of the test chain, and one of its
# slots. `getproof/README.md` gives the origin of the file and its licence.

import json
from pathlib import Path

import pytest

from ethlib.execution import trie
from ethlib.serialization import rlp

_FILE = Path(__file__).resolve().parent / "getproof" / "get-account-proof-with-storage.io"

# The response is the line after `<< `.
_RESPONSE = next(json.loads(line[3:])["result"]
                 for line in _FILE.read_text().splitlines() if line.startswith("<< "))

# The state root that the account proof starts from: the hash of its first node.
# The file holds no state root, so this test states it, as block 60 of `tests/chain.rlp` gives it.
STATE_ROOT = bytes.fromhex("a6bd32516beae9780a8c90563bb28c18f4299855f3f9d7c1de2db9a609ce63ec")


def _hex(text: str) -> bytes:
    return bytes.fromhex(text[2:])


def _scalar(text: str) -> bytes:
    # A scalar is its big-endian bytes with no leading zero, so zero is the empty string.
    value = int(text, 16)
    return value.to_bytes((value.bit_length() + 7) // 8, "big")


def test_account_proof() -> None:
    # The value of an account is the RLP list of its nonce, balance, storage root and code hash.
    account = rlp.encode([_scalar(_RESPONSE["nonce"]), _scalar(_RESPONSE["balance"]),
                          _hex(_RESPONSE["storageHash"]), _hex(_RESPONSE["codeHash"])])
    proof = [_hex(node) for node in _RESPONSE["accountProof"]]
    assert trie.verify_proof(STATE_ROOT, _hex(_RESPONSE["address"]), proof, secured=True) == account


def test_storage_proof() -> None:
    # The key of a slot is the slot on 32 bytes, and its value is the RLP encoding of the word.
    slot = _RESPONSE["storageProof"][0]
    key = int(slot["key"], 16).to_bytes(32, "big")
    proof = [_hex(node) for node in slot["proof"]]
    expected = rlp.encode(_scalar(slot["value"]))
    assert trie.verify_proof(_hex(_RESPONSE["storageHash"]), key, proof, secured=True) == expected


def test_rejects_tampered_node() -> None:
    # A changed byte in the root node no longer hashes to the state root.
    proof = [_hex(node) for node in _RESPONSE["accountProof"]]
    proof[0] = proof[0][:-1] + bytes([proof[0][-1] ^ 1])
    with pytest.raises(ValueError):
        trie.verify_proof(STATE_ROOT, _hex(_RESPONSE["address"]), proof, secured=True)


def test_rejects_short_root() -> None:
    proof = [_hex(node) for node in _RESPONSE["accountProof"]]
    with pytest.raises(ValueError):
        trie.verify_proof(STATE_ROOT[:31], _hex(_RESPONSE["address"]), proof, secured=True)
