"""The QUIC variable-length integer of RFC 9000 §16: a value below 2^62 in 1, 2, 4 or 8 bytes."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import QuicVarintError as QuicVarintError


def encode_varint(value: int) -> bytes:
    """The shortest QUIC encoding of a value in [0, 2^62); a larger value raises QuicVarintError."""
    return _native.quic_varint_encode(value)


def decode_varint(data: bytes) -> tuple[int, bytes]:
    """The QUIC integer at the start of the bytes, longer forms included, and the bytes after it."""
    return _native.quic_varint_decode(data)


__all__ = ["QuicVarintError", "decode_varint", "encode_varint"]
