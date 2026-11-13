"""QUIC v1: integers (RFC 9000 §16), packet keys (RFC 9001 §5) and the TLS 1.3 key schedule."""

from typing import Any, Literal, NamedTuple, TypeAlias

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import (
    QuicError as QuicError,
    QuicVarintError as QuicVarintError,
    Tls13Error as Tls13Error,
)

# The two SHA-256 cipher suites whose packet keys EthLib derives.
CipherSuite: TypeAlias = Literal["TLS_AES_128_GCM_SHA256", "TLS_CHACHA20_POLY1305_SHA256"]


class KeySchedule(NamedTuple):
    """The no-PSK SHA-256 secrets of TLS 1.3 through the first application traffic secrets."""

    early: bytes
    handshake: bytes
    master: bytes
    client_handshake: bytes
    server_handshake: bytes
    client_application: bytes
    server_application: bytes


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


def tls_key_schedule(
    shared_secret: bytes, hello_transcript: bytes, server_transcript: bytes
) -> KeySchedule:
    """
    Derive the no-PSK SHA-256 schedule of TLS 1.3 from a shared secret and two transcripts.

    The hello transcript runs from ClientHello through ServerHello.
    The server transcript runs from ClientHello through the server's Finished message.
    Both include handshake headers and exclude record headers.
    Neither the shared secret nor the prefix relation of the transcripts is checked.
    """
    return KeySchedule(
        *_native.quic_tls_key_schedule(shared_secret, hello_transcript, server_transcript)
    )


def tls_derive_secret(secret: bytes, label: bytes, messages: bytes) -> bytes:
    """
    Derive a SHA-256 secret from encoded handshake messages.

    The label excludes the "tls13 " prefix, and the messages are hashed with SHA-256.
    """
    return _native.quic_tls_derive_secret(secret, label, messages)


def tls_finished(secret: bytes, transcript: bytes) -> bytes:
    """
    Compute Finished verify_data from a traffic secret and the transcript before that Finished.

    During the handshake the secret is the sender's handshake traffic secret.
    """
    return _native.quic_tls_finished(secret, transcript)


def encode_header(header: Any) -> bytes:
    """Encode a constructor tuple in the field order of Packet.Header, with width bits 0–3."""
    return _native.quic_header_encode(header)


def decode_header(short_connection_id_length: int, data: bytes) -> tuple[Any, bytes]:
    """Read an authenticated header and return its constructor tuple and remaining bytes."""
    return _native.quic_header_decode(short_connection_id_length, data)


def encode_frame(frame: Any) -> bytes:
    """Encode a constructor tuple in the field order of Frame.Frame, or a nullary name."""
    return _native.quic_frame_encode(frame)


def decode_frame(packet: str, data: bytes) -> tuple[Any, bytes]:
    """Read a frame allowed in initial, zero_rtt, handshake or one_rtt packets."""
    return _native.quic_frame_decode(packet, data)


def encode_packet_number(width: int, number: int) -> bytes:
    """Write the low 1–4 packet-number bytes, with width bits 0–3."""
    return _native.quic_packet_number_encode(width, number)


def decode_packet_number(width: int, truncated: int, expected: int) -> int:
    """Reconstruct the packet number closest to expected, with width bits 0–3."""
    return _native.quic_packet_number_decode(width, truncated, expected)


__all__ = [
    "QuicError",
    "encode_header",
    "decode_header",
    "encode_frame",
    "decode_frame",
    "encode_packet_number",
    "decode_packet_number",
    "CipherSuite",
    "KeySchedule",
    "QuicVarintError",
    "Tls13Error",
    "decode_varint",
    "encode_varint",
    "initial_secrets",
    "packet_keys",
    "tls_derive_secret",
    "tls_finished",
    "tls_key_schedule",
]
