"""QUIC variable-length integer encoding."""

from ethlib.cryptography import _native
from ethlib.errors import QuicVarIntError as QuicVarIntError


def encode_varint(value: int) -> bytes:
    """Encode a value below 2^62 with its shortest QUIC representation."""
    return _native.quic_varint_encode(value)


def decode_varint(data: bytes) -> tuple[int, bytes]:
    """Read one QUIC integer and return its value and the trailing bytes."""
    return _native.quic_varint_decode(data)


__all__ = ["QuicVarIntError", "decode_varint", "encode_varint"]
