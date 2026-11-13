"""libp2p TLS certificates and peer authentication with an explicit algorithm policy."""

from typing import Any

from ethlib.cryptography import _native
from ethlib.errors import TlsCertificateError as TlsCertificateError


def read_certificate(data: bytes) -> tuple[Any, ...]:
    """The signed bytes, SPKI, validity, extensions, signature and unique-ID flags."""
    return _native.tls_certificate_read(data)


def authenticate(policy: dict[str, Any], now: int, chain: list[bytes]) -> bytes:
    """Authenticate one certificate using the caller's algorithm and unique-ID policy."""
    return _native.tls_certificate_authenticate(policy, now, chain)


def authenticate_peer(
    policy: dict[str, Any], now: int, expected: bytes, chain: list[bytes]
) -> bytes:
    """Authenticate one certificate and check that it identifies the intended peer."""
    return _native.tls_certificate_authenticate_peer(policy, now, expected, chain)


def verify_p256(spki: bytes, message: bytes, signature: bytes) -> bool:
    """Verify strict DER ECDSA/SHA-256 under an uncompressed P-256 SPKI."""
    return _native.tls_certificate_verify_p256(spki, message, signature)


__all__ = [
    "TlsCertificateError",
    "authenticate",
    "authenticate_peer",
    "read_certificate",
    "verify_p256",
]
