"""TLS 1.3 handshake wire formats and SHA-256 transcripts, without a negotiation policy."""

from ethlib.cryptography import _native
from ethlib.errors import TlsHandshakeError as TlsHandshakeError
from ethlib.networking.quic._tls_types import (
    Certificate as Certificate,
    CertificateEntry as CertificateEntry,
    CertificateRequest as CertificateRequest,
    ClientHello as ClientHello,
    Extension as Extension,
    KeyShareEntry as KeyShareEntry,
    Message as Message,
    Payload as Payload,
    PayloadForm as PayloadForm,
    ServerHello as ServerHello,
)


def encode_message(hash_length: int, message: Message) -> bytes:
    """Encode one handshake message with its header, using the caller's hash length for Finished."""
    return _native.quic_tls_message_encode(hash_length, message)


def decode_message(hash_length: int, data: bytes) -> tuple[Message, bytes]:
    """Decode one complete message and return it with the bytes that follow it."""
    return _native.quic_tls_message_decode(hash_length, data)


def encode_payload(payload: Payload) -> Extension:
    """Encode a structured extension payload without selecting its algorithms or protocols."""
    return _native.quic_tls_payload_encode(payload)


def decode_payload(form: PayloadForm, extension: Extension) -> Payload:
    """Decode all of an extension's data in the form the caller names, which must match its type."""
    return _native.quic_tls_payload_decode(form, extension)


def transcript(messages: list[bytes]) -> tuple[bytes, bytes]:
    """Return SHA-256 transcript bytes and their hash, with the retry rule of RFC 8446 §4.4.1."""
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
