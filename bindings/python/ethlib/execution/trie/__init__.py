"""The Merkle Patricia trie of the execution layer: its root, its proofs and its path encoding."""

# Both hash with Keccak-256, and a secured trie hashes each key before it becomes a path.

import re

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


# The patterns of the base types of execution-apis, in `src/schemas/base-types.yaml`.
_PATTERNS = {
    "address": re.compile(r"0x[0-9a-fA-F]{40}"),
    "bytes": re.compile(r"0x[0-9a-f]*"),
    "bytesMax32": re.compile(r"0x[0-9a-f]{0,64}"),
    "hash32": re.compile(r"0x[0-9a-f]{64}"),
    "uint64": re.compile(r"0x(0|[1-9a-f][0-9a-f]{0,15})"),
    "uint256": re.compile(r"0x(0|[1-9a-f][0-9a-f]{0,63})"),
}


def _digits(kind: str, text: str) -> str:
    """The hex digits of a value of a base type, which must match the pattern of the type."""
    if not isinstance(text, str) or not _PATTERNS[kind].fullmatch(text):
        raise ValueError(f"not a value of {kind}: {text!r}")
    return text[2:]


def _number(kind: str, text: str) -> int:
    """A value of a base type, read as a big-endian number."""
    return int(_digits(kind, text) or "0", 16)


def _data(kind: str, text: str) -> bytes:
    """A value of a base type, read as bytes, two hex digits for each byte."""
    digits = _digits(kind, text)
    if len(digits) % 2:
        raise ValueError(f"odd number of hex digits: {text!r}")
    return bytes.fromhex(digits)


def _scalar(value: int) -> bytes:
    # A scalar of RLP is its big-endian bytes without leading zeros, so 0 is no bytes.
    return value.to_bytes((value.bit_length() + 7) // 8, "big")


def verify_account_proof(state_root: bytes, answer: dict) -> list[bool] | None:
    """Check an answer of `eth_getProof` against a 32-byte state root, slot by slot."""
    # The answer is the `result` object of the response.
    # Its fields are those of `AccountProof` of execution-apis.
    # A field that does not match the pattern of its type raises ValueError.
    # An answer that does not hold raises TrieError.
    #
    # None means that the proof shows no account at the address.
    # The nonce, the balance and each slot are then 0, and the slot proofs are not read.
    # Each hash is zero, or that of no code or of no storage.
    # Otherwise the fields hold.
    # Each slot is True when it is set and holds its value.
    # It is False when its proof shows that it is not set and its value is 0.
    slots = [
        [
            # A storage key is read as a number, which the trie writes on 32 bytes.
            _number("bytesMax32", slot["key"]).to_bytes(32, "big"),
            _scalar(_number("uint256", slot["value"])),
            [_data("bytes", node) for node in slot["proof"]],
        ]
        for slot in answer["storageProof"]
    ]
    fields = [
        _data("address", answer["address"]),
        _scalar(_number("uint64", answer["nonce"])),
        _scalar(_number("uint256", answer["balance"])),
        _data("hash32", answer["codeHash"]),
        _data("hash32", answer["storageHash"]),
        [_data("bytes", node) for node in answer["accountProof"]],
        slots,
    ]
    outcome = _native.trie_verify_account_proof(state_root, rlp.encode(fields))
    if not outcome:
        return None
    return [byte == 1 for byte in outcome[1:]]


def hex_prefix(nibbles: list[int], is_leaf: bool) -> bytes:
    """The hex-prefix encoding of a path of nibbles, HP of Appendix C of the Yellow Paper."""
    # A value outside a byte raises OverflowError, and a byte of 16 or more TrieError with code 0.
    if any(not 0 <= n < 256 for n in nibbles):
        raise OverflowError("a nibble must be in [0, 256)")
    return _native.trie_hex_prefix(bytes(nibbles), is_leaf)


__all__ = ["root", "verify_proof", "verify_account_proof", "hex_prefix", "TrieError"]
