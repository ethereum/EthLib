"""The messages of the snap capability of devp2p, snap/1 and snap/2."""

from collections.abc import Sequence

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import SnapError

# The message IDs within the capability.
GET_ACCOUNT_RANGE = 0x00
ACCOUNT_RANGE = 0x01
GET_STORAGE_RANGES = 0x02
STORAGE_RANGES = 0x03
GET_BYTE_CODES = 0x04
BYTE_CODES = 0x05
GET_TRIE_NODES = 0x06
TRIE_NODES = 0x07
GET_BLOCK_ACCESS_LISTS = 0x08
BLOCK_ACCESS_LISTS = 0x09


def decode_message(version: int, message_id: int, data: bytes) -> bytes:
    """The canonical RLP data of message `message_id` with the data `data`, on snap/`version`."""
    return _native.snap_message_decode(version, message_id, data)


def codes_answer(version: int, request: bytes, response: bytes) -> bool:
    """Whether the ByteCodes data `response` answers the GetByteCodes data `request`."""
    return _native.snap_codes_answer(version, request, response)


def access_lists_answer(request: bytes, response: bytes, expected: list[bytes]) -> bool:
    """Whether the BlockAccessLists `response` answers the request, with these header hashes."""
    return _native.snap_access_lists_answer(request, response, expected)


def full_account(slim: bytes) -> bytes:
    """The full RLP form of an account in slim form."""
    return _native.snap_full_account(slim)


def verify_account_range(
    root: bytes, start: bytes, accounts: Sequence[tuple[bytes, bytes]], proof: Sequence[bytes]
) -> bool | None:
    """Check an AccountRange answer from `start` in the state trie of `root`."""
    # Each account is the hash of its address and its body in slim form.
    # None is the empty reply of a peer without the state, so test the result with `is None`.
    # Otherwise the result says whether the trie holds an account after the last one.
    # An answer that does not verify raises SnapError with the code of its fault.
    return _native.snap_verify_account_range(root, start, list(accounts), list(proof))


def verify_storage_ranges(
    roots: Sequence[bytes],
    start: bytes,
    slots: Sequence[Sequence[tuple[bytes, bytes]]],
    proof: Sequence[bytes],
) -> bool | None:
    """Check a StorageRanges answer against the storage roots of the requested accounts."""
    # Each range holds the hash of each slot and its value in the storage trie.
    # The start has 32 bytes, or none for the zero hash.
    # Any other start applies only when one account is requested.
    # With several, each range starts at the zero hash.
    # None is the empty reply of a peer without the state of the root or of a requested account.
    # Otherwise the result says whether the last account holds a slot after its range.
    # An answer that does not verify raises SnapError with the code of its fault.
    return _native.snap_verify_storage_ranges(
        list(roots), start, [list(range_) for range_ in slots], list(proof)
    )


__all__ = [
    "ACCOUNT_RANGE",
    "BLOCK_ACCESS_LISTS",
    "BYTE_CODES",
    "GET_ACCOUNT_RANGE",
    "GET_BLOCK_ACCESS_LISTS",
    "GET_BYTE_CODES",
    "GET_STORAGE_RANGES",
    "GET_TRIE_NODES",
    "STORAGE_RANGES",
    "TRIE_NODES",
    "SnapError",
    "access_lists_answer",
    "codes_answer",
    "decode_message",
    "full_account",
    "verify_account_range",
    "verify_storage_ranges",
]
