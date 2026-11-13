"""libp2p TLS certificates and peer authentication with an explicit algorithm policy."""

from collections.abc import Sequence
from typing import Literal, NamedTuple, TypeAlias, TypedDict

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import TlsCertificateError as TlsCertificateError

# The host-key types whose signatures EthLib checks.
HostAlgorithm: TypeAlias = Literal["secp256k1", "p256"]

# The certificate self-signature algorithms EthLib checks: ECDSA on P-256 with SHA-256.
CertificateAlgorithm: TypeAlias = Literal["p256_sha256"]


class Policy(TypedDict):
    """The accepted host and certificate algorithms, and whether to reject unique IDs."""

    host_algorithms: list[HostAlgorithm]
    certificate_algorithms: list[CertificateAlgorithm]
    reject_unique_ids: bool


class Extension(TypedDict):
    """An X.509 extension: its DER object identifier content, critical flag and value."""

    oid: bytes
    critical: bool
    value: bytes


class Certificate(NamedTuple):
    """The certificate fields that authentication reads, with the exact signed bytes."""

    tbs: bytes
    spki: bytes
    # A validity endpoint is a sign flag, then its absolute seconds from the Unix epoch.
    not_before: tuple[bool, int]
    not_after: tuple[bool, int]
    extensions: list[Extension]
    signature_algorithm: bytes
    signature: bytes
    issuer_unique_id: bool
    subject_unique_id: bool


def read_certificate(data: bytes) -> Certificate:
    """The fields of one strict DER certificate; malformed input raises TlsCertificateError."""
    return Certificate(*_native.tls_certificate_read(data))


def authenticate(policy: Policy, now: int, chain: Sequence[bytes]) -> bytes:
    """The peer ID that a chain of exactly one certificate proves at `now`, in Unix seconds."""
    return _native.tls_certificate_authenticate(dict(policy), now, list(chain))


def authenticate_peer(policy: Policy, now: int, expected: bytes, chain: Sequence[bytes]) -> bytes:
    """The peer ID of one authenticated certificate, which must equal the expected peer ID."""
    return _native.tls_certificate_authenticate_peer(dict(policy), now, expected, list(chain))


def verify_p256(spki: bytes, message: bytes, signature: bytes) -> bool:
    """Whether a DER ECDSA/SHA-256 signature verifies under an uncompressed P-256 public key."""
    return _native.tls_certificate_verify_p256(spki, message, signature)


__all__ = [
    "Certificate",
    "CertificateAlgorithm",
    "Extension",
    "HostAlgorithm",
    "Policy",
    "TlsCertificateError",
    "authenticate",
    "authenticate_peer",
    "read_certificate",
    "verify_p256",
]
