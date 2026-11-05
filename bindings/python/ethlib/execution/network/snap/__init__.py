"""The messages of the snap capability of devp2p, snap/1 and snap/2."""

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
]
