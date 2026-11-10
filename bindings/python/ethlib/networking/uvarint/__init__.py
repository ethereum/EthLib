"""The multiformats unsigned varint of libp2p: at most nine bytes, read from the input start."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import UvarintError as UvarintError


def encode(value: int) -> bytes:
    """The unsigned varint of a value in [0, 2^63); a larger value raises UvarintError."""
    return _native.uvarint_encode(value)


def decode(data: bytes) -> tuple[int, bytes]:
    """The value of the unsigned varint at the start of the bytes, and the bytes after it."""
    return _native.uvarint_decode(data)


__all__ = ["UvarintError", "decode", "encode"]
