"""The messages of the eth capability of devp2p."""

from ...errors import EthWireError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native

# The message IDs within the capability.
STATUS = 0x00
BLOCK_RANGE_UPDATE = 0x11


def decode_message(version: int, message_id: int, data: bytes) -> bytes:
    """The canonical RLP data of the message `message_id` with the data `data`, on eth/`version`."""
    return _native.eth_message_decode(version, message_id, data)


def check_status(version: int, schedule: bytes, number: int, timestamp: int, data: bytes) -> None:
    """Accept the Status `data` of a peer on eth/`version` at a head, or raise EthWireError."""
    _native.eth_check_status(version, schedule, number, timestamp, data)


__all__ = ["BLOCK_RANGE_UPDATE", "STATUS", "EthWireError", "check_status", "decode_message"]
