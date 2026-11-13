"""QUIC v1: the integers of RFC 9000 §16 and the packet keys of RFC 9001 §5."""

from typing import Literal, TypeAlias

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import QuicVarintError as QuicVarintError, Tls13Error as Tls13Error

# The two SHA-256 cipher suites whose packet keys EthLib derives.
CipherSuite: TypeAlias = Literal["TLS_AES_128_GCM_SHA256", "TLS_CHACHA20_POLY1305_SHA256"]


def encode_varint(value: int) -> bytes:
    """The shortest QUIC encoding of a value in [0, 2^62); a larger value raises QuicVarintError."""
    return _native.quic_varint_encode(value)


def decode_varint(data: bytes) -> tuple[int, bytes]:
    """The QUIC integer at the start of the bytes, longer forms included, and the bytes after it."""
    return _native.quic_varint_decode(data)


def initial_secrets(destination_connection_id: bytes) -> tuple[bytes, bytes]:
    """The client and server Initial secrets of QUIC v1, in that order, RFC 9001 §5.2."""
    return _native.quic_initial_secrets(destination_connection_id)


def packet_keys(suite: CipherSuite, secret: bytes) -> tuple[bytes, bytes, bytes]:
    """The payload key, IV and header-protection key, in that order, RFC 9001 §5.1."""
    return _native.quic_packet_keys(suite, secret)


__all__ = [
    "CipherSuite",
    "QuicVarintError",
    "Tls13Error",
    "decode_varint",
    "encode_varint",
    "initial_secrets",
    "packet_keys",
]
