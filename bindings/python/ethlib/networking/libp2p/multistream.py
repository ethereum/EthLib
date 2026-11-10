"""multistream-select 1.0 messages: a length, the bytes, then a newline that the length counts."""

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


__all__ = ["MultistreamError", "decode", "encode"]
