"""multistream-select 1.0: the framing of a message, and the two peers of a negotiation."""

from collections.abc import Sequence

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import MultistreamError as MultistreamError


def encode(message: bytes) -> bytes:
    """The bytes of one message: its length as an unsigned varint, its bytes, then a newline."""
    return _native.multistream_encode(message)


def decode(data: bytes) -> tuple[bytes, bytes]:
    """The message at the start of the bytes, without its newline, and the bytes after it."""
    return _native.multistream_decode(data)


def listen(supported: Sequence[bytes], data: bytes) -> tuple[str, bytes, bytes, bytes]:
    """State, agreed protocol, sent and unread bytes of a listener reading `data` from its start."""
    return _native.multistream_listen(list(supported), data)


def dial(proposals: Sequence[bytes], data: bytes) -> tuple[str, bytes, bytes, bytes]:
    """State, agreed or unexpected protocol, sent and unread bytes of a dialer reading `data`."""
    return _native.multistream_dial(list(proposals), data)


__all__ = ["MultistreamError", "decode", "dial", "encode", "listen"]
