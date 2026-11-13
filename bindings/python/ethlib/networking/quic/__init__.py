"""QUIC encodings and key derivation."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import QuicVarintError as QuicVarintError, Tls13Error as Tls13Error


def encode_varint(value: int) -> bytes:
    """The shortest QUIC encoding of a value in [0, 2^62); a larger value raises QuicVarintError."""
    return _native.quic_varint_encode(value)


def decode_varint(data: bytes) -> tuple[int, bytes]:
    """The QUIC integer at the start of the bytes, longer forms included, and the bytes after it."""
    return _native.quic_varint_decode(data)


__all__ = [
    "QuicVarintError",
    "Tls13Error",
    "decode_varint",
    "encode_varint",
    "hkdf_label",
    "expand_label",
    "initial_secrets",
    "packet_keys",
]


def hkdf_label(label: bytes, context: bytes, length: int) -> bytes:
    """Serialize the checked TLS 1.3 HKDF label."""
    return _native.tls13_hkdf_label(label, context, length)


def expand_label(secret: bytes, label: bytes, context: bytes, length: int) -> bytes:
    """Expand a SHA-256 secret using the TLS 1.3 label encoding."""
    return _native.tls13_expand_label(secret, label, context, length)


def initial_secrets(dcid: bytes) -> tuple[bytes, bytes]:
    """Derive the QUIC v1 client and server Initial secrets, in that order."""
    return _native.quic_initial_secrets(dcid)


def packet_keys(suite: str, secret: bytes) -> tuple[bytes, bytes, bytes]:
    """Derive a QUIC payload key, initialization vector and header-protection key."""
    return _native.quic_packet_keys(suite, secret)
