"""TLS 1.3 handshake wire formats and SHA-256 transcripts, without a negotiation policy."""

from typing import Literal, TypeAlias, TypedDict

from ethlib.cryptography import _native
from ethlib.errors import TlsHandshakeError as TlsHandshakeError


class Extension(TypedDict):
    """An extension type and its exact data, in RFC 8446 §4.2 wire order."""

    kind: int
    data: list[int]


class ClientHello(TypedDict):
    """The variable fields of a TLS 1.3 ClientHello, RFC 8446 §4.1.2."""

    random: bytes
    legacy_session_id: list[int]
    cipher_suites: list[int]
    extensions: list[Extension]


class ServerHello(TypedDict):
    """The variable fields shared by ServerHello and HelloRetryRequest, RFC 8446 §4.1.3."""

    random: bytes
    legacy_session_id_echo: list[int]
    cipher_suite: int
    extensions: list[Extension]


class CertificateEntry(TypedDict):
    """Opaque certificate bytes and per-certificate extensions, RFC 8446 §4.4.2."""

    data: list[int]
    extensions: list[Extension]


class Certificate(TypedDict):
    """A request context and a certificate list, including an empty client list."""

    context: list[int]
    entries: list[CertificateEntry]


class CertificateRequest(TypedDict):
    """A certificate request context and its extensions, RFC 8446 §4.3.2."""

    context: list[int]
    extensions: list[Extension]


class KeyShareEntry(TypedDict):
    """A named group and its unvalidated key-exchange bytes, RFC 8446 §4.2.8."""

    group: int
    key_exchange: list[int]


# Algorithm identifiers are two-byte integers, without a supported-algorithm profile.
Message: TypeAlias = (
    tuple[Literal["client_hello"], ClientHello]
    | tuple[Literal["server_hello"], ServerHello]
    | tuple[Literal["encrypted_extensions"], list[Extension]]
    | tuple[Literal["certificate_request"], CertificateRequest]
    | tuple[Literal["certificate"], Certificate]
    | tuple[Literal["certificate_verify"], int, list[int]]
    | tuple[Literal["finished"], list[int]]
)

PayloadForm: TypeAlias = Literal[
    "supported_versions",
    "selected_version",
    "supported_groups",
    "signature_algorithms",
    "client_key_share",
    "server_key_share",
    "retry_key_share",
    "alpn",
    "quic_transport_parameters",
]

Payload: TypeAlias = (
    tuple[Literal["supported_versions", "supported_groups", "signature_algorithms"], list[int]]
    | tuple[Literal["selected_version", "retry_key_share"], int]
    | tuple[Literal["client_key_share"], list[KeyShareEntry]]
    | tuple[Literal["server_key_share"], KeyShareEntry]
    | tuple[Literal["alpn"], list[list[int]]]
    | tuple[Literal["quic_transport_parameters"], list[int]]
)


def encode_message(hash_length: int, message: Message) -> bytes:
    """Encode one handshake message with its header and the negotiated hash length."""
    return _native.quic_tls_message_encode(hash_length, message)


def decode_message(hash_length: int, data: bytes) -> tuple[Message, bytes]:
    """Read one message and trailing bytes; a truncated message raises TlsHandshakeError."""
    return _native.quic_tls_message_decode(hash_length, data)


def encode_payload(payload: Payload) -> Extension:
    """Encode a structured extension payload without selecting its algorithms or protocols."""
    return _native.quic_tls_payload_encode(payload)


def decode_payload(form: PayloadForm, extension: Extension) -> Payload:
    """Read all extension data in the form required by the enclosing handshake message."""
    return _native.quic_tls_payload_decode(form, extension)


def transcript(messages: list[bytes]) -> tuple[bytes, bytes]:
    """Return SHA-256 transcript bytes and their hash, with the HelloRetryRequest replacement."""
    return _native.quic_tls_transcript(messages)


def certificate_verify_input(server: bool, digest: bytes) -> bytes:
    """Build CertificateVerify's signed content from a SHA-256 transcript hash, RFC 8446 §4.4.3."""
    return _native.quic_tls_certificate_verify_input(server, digest)


__all__ = [
    "Certificate",
    "CertificateEntry",
    "CertificateRequest",
    "ClientHello",
    "Extension",
    "KeyShareEntry",
    "Message",
    "Payload",
    "PayloadForm",
    "ServerHello",
    "TlsHandshakeError",
    "certificate_verify_input",
    "decode_message",
    "decode_payload",
    "encode_message",
    "encode_payload",
    "transcript",
]
