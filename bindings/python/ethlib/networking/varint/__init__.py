"""The unsigned protobuf varint of a 64-bit value."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


def encode(value: int) -> bytes:
    """The varint of a value in [0, 2^64)."""
    return _native.varint_encode(value)


def decode(data: bytes) -> int:
    """The value that the bytes encode; anything but one minimal varint raises ValueError."""
    return _native.varint_decode(data)
