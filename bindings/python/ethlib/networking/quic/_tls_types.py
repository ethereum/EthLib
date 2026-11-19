"""The shared Python shapes of TLS handshake messages and extension payloads."""

from typing import Literal, TypeAlias, TypedDict


class Extension(TypedDict):
    """An extension type and its exact data, in RFC 8446 §4.2 wire order."""

    kind: int
    data: bytes


class ClientHello(TypedDict):
    """The variable fields of a TLS 1.3 ClientHello, RFC 8446 §4.1.2."""

    random: bytes
    legacy_session_id: bytes
    cipher_suites: list[int]
    extensions: list[Extension]


class ServerHello(TypedDict):
    """The variable fields shared by ServerHello and HelloRetryRequest, RFC 8446 §4.1.3."""

    random: bytes
    legacy_session_id_echo: bytes
    cipher_suite: int
    extensions: list[Extension]


class CertificateEntry(TypedDict):
    """Opaque certificate bytes and per-certificate extensions, RFC 8446 §4.4.2."""

    data: bytes
    extensions: list[Extension]


class Certificate(TypedDict):
    """A request context and a certificate list, including an empty client list."""

    context: bytes
    entries: list[CertificateEntry]


class CertificateRequest(TypedDict):
    """A certificate request context and its extensions, RFC 8446 §4.3.2."""

    context: bytes
    extensions: list[Extension]


class KeyShareEntry(TypedDict):
    """A named group and its opaque key-exchange bytes, RFC 8446 §4.2.8."""

    group: int
    key_exchange: bytes


# Algorithm identifiers are two-byte integers, without a supported-algorithm profile.
Message: TypeAlias = (
    tuple[Literal["client_hello"], ClientHello]
    | tuple[Literal["server_hello"], ServerHello]
    | tuple[Literal["encrypted_extensions"], list[Extension]]
    | tuple[Literal["certificate_request"], CertificateRequest]
    | tuple[Literal["certificate"], Certificate]
    | tuple[Literal["certificate_verify"], int, bytes]
    | tuple[Literal["finished"], bytes]
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
    | tuple[Literal["alpn"], list[bytes]]
    | tuple[Literal["quic_transport_parameters"], bytes]
)


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
]
