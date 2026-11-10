"""The Merkle Patricia trie of the execution layer: its root, its proofs and its path encoding."""

# Both hash with Keccak-256, and a secured trie hashes each key before it becomes a path.

from collections.abc import Sequence

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import TrieError
from ethlib.serialization import rlp


def root(pairs: list[tuple[bytes, bytes]], secured: bool = False) -> bytes:
    """The 32-byte root of the trie that sets each pair in order, from an empty trie."""
    # An empty value removes its key.
    return _native.trie_root(secured, rlp.encode([[key, value] for key, value in pairs]))


def verify_proof(
    root: bytes, key: bytes, proof: list[bytes], secured: bool = False
) -> bytes | None:
    """The value of a key under a 32-byte root, or None when the key is not set."""
    # The proof lists the encodings of the nodes on the path of the key, from the root down.
    # A proof that does not verify raises TrieError, a ValueError.
    return _native.trie_verify_proof(root, secured, key, rlp.encode(list(proof)))


def verify_range(
    root: bytes, start: bytes, entries: Sequence[tuple[bytes, bytes]], proof: Sequence[bytes]
) -> bool:
    """Check a range of the trie of a 32-byte root from `start`, and whether keys follow it."""
    # Each entry is a 32-byte key, not hashed again, and its value, in increasing key order.
    # The proof holds the nodes on the paths of the start and of the last key, in any order.
    # With no proof, the entries must be the whole trie.
    # A range that does not verify raises TrieError with the code of its fault.
    return _native.trie_verify_range(root, start, list(entries), list(proof))


def verify_account_proof(state_root: bytes, answer: dict) -> list[bool] | None:
    """Check an answer of `eth_getProof` against a 32-byte state root, slot by slot."""
    # The answer is the `result` object of the response.
    # Its fields are those of `AccountProof` of execution-apis, and Lean reads their patterns.
    # A field that is missing or out of the pattern of its type raises TrieError with code 0.
    # An answer that does not hold raises TrieError with the code of its fault.
    #
    # None means that the proof shows no account at the address.
    # The nonce, the balance and each slot are then 0, and the slot proofs are not read.
    # Each hash is zero, or that of no code or of no storage.
    # Otherwise the fields hold.
    # Each slot is True when it is set and holds its value.
    # It is False when its proof shows that it is not set and its value is 0.
    return _native.trie_verify_account_proof(state_root, answer)


def hex_prefix(nibbles: Sequence[int], is_leaf: bool) -> bytes:
    """The hex-prefix encoding of a path of nibbles, HP of Appendix C of the Yellow Paper."""
    # A number of 16 or more raises TrieError with code 0, and a negative one ValueError.
    return _native.trie_hex_prefix(list(nibbles), is_leaf)


__all__ = [
    "root",
    "verify_proof",
    "verify_range",
    "verify_account_proof",
    "hex_prefix",
    "TrieError",
]
