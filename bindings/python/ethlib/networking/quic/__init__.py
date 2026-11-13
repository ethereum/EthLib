"""QUIC v1: wire codecs (RFC 9000), packet keys and protection (RFC 9001) and TLS 1.3 secrets."""

from typing import Literal, NamedTuple, TypeAlias, TypedDict

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import (
    QuicError as QuicError,
    QuicProtectionError as QuicProtectionError,
    QuicVarintError as QuicVarintError,
    Tls13Error as Tls13Error,
)

# The two SHA-256 cipher suites whose packet keys EthLib derives.
CipherSuite: TypeAlias = Literal["TLS_AES_128_GCM_SHA256", "TLS_CHACHA20_POLY1305_SHA256"]

# The packet types that carry frames, RFC 9000 §12.4, Table 3.
PacketType: TypeAlias = Literal["initial", "zero_rtt", "handshake", "one_rtt"]

# A header is a tuple: its packet type, then its connection IDs and other fields.
# Width is the two-bit packet-number length, 0 to 3 for 1 to 4 bytes.
# The number is the truncated packet number, and the Length counts it and the payload.
Header: TypeAlias = (
    tuple[Literal["initial"], list[int], list[int], list[int], int, int, int]
    | tuple[Literal["zero_rtt", "handshake"], list[int], list[int], int, int, int]
    | tuple[Literal["one_rtt"], list[int], bool, bool, int, int]
    | tuple[Literal["retry"], list[int], list[int], list[int], bytes, int]
    | tuple[Literal["version_negotiation"], list[int], list[int], int, list[int]]
)


class Ack(TypedDict):
    """The fields of an ACK frame, RFC 9000 §19.3."""

    largest: int
    delay: int
    first_range: int
    ranges: list[tuple[int, int]]
    ecn: tuple[int, int, int] | None


# A frame is its name alone, or a tuple of its name and its fields in wire order.
Frame: TypeAlias = (
    Literal["padding", "ping", "handshake_done"]
    | tuple[Literal["ack"], Ack]
    | tuple[Literal["reset_stream"], int, int, int]
    | tuple[Literal["stop_sending", "max_stream_data", "stream_data_blocked"], int, int]
    | tuple[Literal["crypto"], int, list[int]]
    | tuple[Literal["new_token"], list[int]]
    | tuple[Literal["stream"], int, int | None, bool, bool, list[int]]
    | tuple[Literal["max_data", "data_blocked", "retire_connection_id"], int]
    | tuple[Literal["max_streams", "streams_blocked"], bool, int]
    | tuple[Literal["new_connection_id"], int, int, list[int], bytes]
    | tuple[Literal["path_challenge", "path_response"], bytes]
    | tuple[Literal["connection_close"], int, int | None, list[int]]
)


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


def encode_header(header: Header) -> bytes:
    """Encode a header through its packet-number field, after checking its bounds, RFC 9000 §17."""
    return _native.quic_header_encode(header)


def decode_header(short_connection_id_length: int, data: bytes) -> tuple[Header, bytes]:
    """Read an authenticated header and return it with the bytes after it, RFC 9000 §17."""
    return _native.quic_header_decode(short_connection_id_length, data)


def encode_frame(frame: Frame) -> bytes:
    """Encode a well-formed frame with its one-byte type, RFC 9000 §19."""
    return _native.quic_frame_encode(frame)


def decode_frame(packet: PacketType, data: bytes) -> tuple[Frame, bytes]:
    """Read one frame allowed in the packet type and return it with the bytes after it, §12.4."""
    return _native.quic_frame_decode(packet, data)


def encode_packet_number(width: int, number: int) -> bytes:
    """Keep the low width + 1 bytes of a packet number, RFC 9000 §17.1."""
    return _native.quic_packet_number_encode(width, number)


def decode_packet_number(width: int, truncated: int, expected: int) -> int:
    """Rebuild a packet number from its low bytes; expected is 1 + the largest seen, or 0."""
    return _native.quic_packet_number_decode(width, truncated, expected)


def protect(
    suite: CipherSuite, secret: bytes, number: int, offset: int, header: bytes, plaintext: bytes
) -> bytes:
    """Seal a header that ends at its packet number; a payload too short to sample raises."""
    return _native.quic_protect(suite, secret, number, offset, header, plaintext)


def unprotect(
    suite: CipherSuite, secret: bytes, expected: int, offset: int, packet: bytes
) -> tuple[bytes, bytes]:
    """Return header and plaintext; expected is 1 + the largest authenticated number, or 0."""
    return _native.quic_unprotect(suite, secret, expected, offset, packet)


def retry_tag(original_dcid: bytes, retry: bytes) -> bytes:
    """Compute the integrity tag of a Retry packet given without its tag, RFC 9001 §5.8."""
    return _native.quic_retry_tag(original_dcid, retry)


__all__ = [
    "Ack",
    "CipherSuite",
    "Frame",
    "Header",
    "KeySchedule",
    "PacketType",
    "QuicError",
    "QuicProtectionError",
    "QuicVarintError",
    "Tls13Error",
    "decode_frame",
    "decode_header",
    "decode_packet_number",
    "decode_varint",
    "encode_frame",
    "encode_header",
    "encode_packet_number",
    "encode_varint",
    "initial_secrets",
    "packet_keys",
    "protect",
    "retry_tag",
    "tls_derive_secret",
    "tls_finished",
    "tls_key_schedule",
    "unprotect",
]
