"""The messages of the eth capability of devp2p."""

from ...errors import EthWireError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native

# The message IDs within the capability.
STATUS = 0x00
NEW_BLOCK_HASHES = 0x01
GET_BLOCK_HEADERS = 0x03
BLOCK_HEADERS = 0x04
GET_BLOCK_BODIES = 0x05
BLOCK_BODIES = 0x06
NEW_BLOCK = 0x07
TRANSACTIONS = 0x02
NEW_POOLED_TRANSACTION_HASHES = 0x08
GET_POOLED_TRANSACTIONS = 0x09
POOLED_TRANSACTIONS = 0x0A
BLOCK_RANGE_UPDATE = 0x11


def decode_message(version: int, message_id: int, data: bytes) -> bytes:
    """The canonical RLP data of the message `message_id` with the data `data`, on eth/`version`."""
    return _native.eth_message_decode(version, message_id, data)


def check_status(version: int, schedule: bytes, number: int, timestamp: int, data: bytes) -> None:
    """Accept the Status `data` of a peer on eth/`version` at a head, or raise EthWireError."""
    _native.eth_check_status(version, schedule, number, timestamp, data)


def check_headers(version: int, request: bytes, response: bytes) -> None:
    """Accept the BlockHeaders data `response` as an answer to the GetBlockHeaders `request`."""
    _native.eth_check_headers(version, request, response)


def check_pooled(version: int, request: bytes, response: bytes) -> None:
    """Accept the PooledTransactions data `response` as an answer to the GetPooledTransactions."""
    _native.eth_check_pooled(version, request, response)


def wire_hash(tx: bytes) -> bytes:
    """The hash of the RLP item `tx` of a transaction, as it crosses the wire."""
    return _native.eth_wire_hash(tx)


__all__ = [
    "BLOCK_BODIES",
    "BLOCK_HEADERS",
    "BLOCK_RANGE_UPDATE",
    "GET_BLOCK_BODIES",
    "GET_BLOCK_HEADERS",
    "GET_POOLED_TRANSACTIONS",
    "NEW_BLOCK",
    "NEW_BLOCK_HASHES",
    "NEW_POOLED_TRANSACTION_HASHES",
    "POOLED_TRANSACTIONS",
    "STATUS",
    "TRANSACTIONS",
    "EthWireError",
    "check_headers",
    "check_pooled",
    "check_status",
    "decode_message",
    "wire_hash",
]
