"""Snappy blocks and framed streams, as the consensus layer uses them."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import SnappyError as SnappyError


def decompress(block: bytes) -> bytes:
    """The data of a Snappy block; a rejected block raises SnappyError, a ValueError."""
    return _native.snappy_decompress(block)


def compress_literal(data: bytes) -> bytes:
    """The block that holds the data as one literal."""
    return _native.snappy_compress_literal(data)


def decode_frames(stream: bytes) -> bytes:
    """The data of a framed stream; a rejected stream raises SnappyError, a ValueError."""
    return _native.snappy_decode_frames(stream)


def encode_frames_literal(data: bytes) -> bytes:
    """The framed stream that holds the data in uncompressed chunks."""
    return _native.snappy_encode_frames_literal(data)


def masked_crc(data: bytes) -> int:
    """The masked CRC-32C that a data chunk stores for the data."""
    return _native.snappy_masked_crc(data)
