"""The Merkle Patricia trie of the execution layer: its root, its proofs and its path encoding."""

# Both hash with Keccak-256, and a secured trie hashes each key before it becomes a path.

from ...errors import TrieError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native
from ...serialization import rlp


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


def hex_prefix(nibbles: list[int], is_leaf: bool) -> bytes:
    """The hex-prefix encoding of a path of nibbles, HP of Appendix C of the Yellow Paper."""
    # A value outside a byte raises OverflowError, and a byte of 16 or more TrieError with code 0.
    if any(not 0 <= n < 256 for n in nibbles):
        raise OverflowError("a nibble must be in [0, 256)")
    return _native.trie_hex_prefix(bytes(nibbles), is_leaf)


__all__ = ["root", "verify_proof", "hex_prefix", "TrieError"]
