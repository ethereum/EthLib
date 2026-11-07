"""Proof verification against one `eth_getProof` response of ethereum/execution-apis."""

# The response proves one account in the state of block 60 of the test chain, and one of its
# slots. `getproof/README.md` gives the origin of the file and its licence.

import json
from pathlib import Path

import pytest

from ethlib.errors import TrieError
from ethlib.execution import trie
from ethlib.serialization import rlp
from raising import raises

_FILE = Path(__file__).resolve().parent / "getproof" / "get-account-proof-with-storage.io"

# The response is the line after `<< `.
_RESPONSE = next(
    json.loads(line[3:])["result"]
    for line in _FILE.read_text().splitlines()
    if line.startswith("<< ")
)

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
    account = rlp.encode(
        [
            _scalar(_RESPONSE["nonce"]),
            _scalar(_RESPONSE["balance"]),
            _hex(_RESPONSE["storageHash"]),
            _hex(_RESPONSE["codeHash"]),
        ]
    )
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
    with raises(ValueError, "proof does not verify: EthLib.Execution.Trie.ProofError.hashMismatch"):
        trie.verify_proof(STATE_ROOT, _hex(_RESPONSE["address"]), proof, secured=True)


def test_rejects_short_root() -> None:
    proof = [_hex(node) for node in _RESPONSE["accountProof"]]
    with raises(ValueError, "bad root size: 31, expected 32"):
        trie.verify_proof(STATE_ROOT[:31], _hex(_RESPONSE["address"]), proof, secured=True)


# Hand-built proofs of the key 0x01 in a trie that does not hash its keys, one node each. The root
# is the hash of the node, so the proof gets past the hash and fails on the shape of the node.
_KEY = bytes([1])

_NODE_ERRORS = [
    pytest.param(
        # A leaf whose path starts with the nibble 4, which no flag and parity give.
        "4fa752b07e557b1947c490ba35fd16c769a0d3438f6dec179798210a7b74f6e7",
        "c24001",
        104,
        "EthLib.Execution.Trie.ProofError.hexPrefix "
        "(EthLib.Execution.Trie.HexPrefixError.invalidFirstNibble)",
        id="hex_prefix",
    ),
    pytest.param(
        # A list of three items, which is neither a leaf, an extension nor a branch.
        "8d3fc38cad3086ab848b1d779e0a7c77b164869d4546e1b6b9a4feb717dd8686",
        "c3010203",
        105,
        "EthLib.Execution.Trie.ProofError.invalidNode",
        id="invalid_node",
    ),
    pytest.param(
        # A branch whose child at the nibble 0, where the key goes, is a string of 5 bytes.
        "c8d66ee53b41a50fbf8280e8e0c5972d54fe8543bfa52a630b0b9e38234aecc1",
        "d685070707070780808080808080808080808080808080",
        106,
        "EthLib.Execution.Trie.ProofError.invalidReference",
        id="invalid_reference",
    ),
    pytest.param(
        # An extension whose path is empty, with the 32-byte reference 0x09 repeated as its child.
        "9241117e4ec9e0713a2e7db7d44fbb7347f42337308ee0fee823168c181cad79",
        "e200a0" + "09" * 32,
        107,
        "EthLib.Execution.Trie.ProofError.emptyExtension",
        id="empty_extension",
    ),
]


@pytest.mark.parametrize(("root", "node", "code", "name"), _NODE_ERRORS)
def test_rejects_malformed_node(root: str, node: str, code: int, name: str) -> None:
    """A node of a shape that no trie builds is rejected, with the code of its kind."""
    with raises(TrieError, f"proof does not verify: {name}") as error:
        trie.verify_proof(bytes.fromhex(root), _KEY, [bytes.fromhex(node)], secured=False)
    assert error.value.code == code


# A leaf at the path 0x01 with the value 0x05: the list of the path 0x2001 and the string 0x05.
_LEAF_ROOT = bytes.fromhex("5aa296fd5f7f7632ea2aa4071c09ffc08a6135c58510573f83c1e0c49dc276c4")
_LEAF = bytes.fromhex("c482200105")


def test_leaf_proof() -> None:
    assert trie.verify_proof(_LEAF_ROOT, _KEY, [_LEAF], secured=False) == bytes([5])


def test_rejects_unused_node() -> None:
    """A proof that holds a node beyond those of the path is rejected, even if the path holds."""
    with raises(
        TrieError, "proof does not verify: EthLib.Execution.Trie.ProofError.unusedNodes"
    ) as error:
        trie.verify_proof(_LEAF_ROOT, _KEY, [_LEAF, _LEAF], secured=False)
    assert error.value.code == 108
