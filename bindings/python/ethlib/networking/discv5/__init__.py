"""The Node Discovery Protocol v5 (discv5): node distances and the "v4" handshake cryptography.

- A node ID is 32 bytes, and a private key is 32 big-endian bytes.
- A public key is a SEC 1 encoding of a point of secp256k1, compressed or not.

An invalid key or node ID raises ValueError.
"""

from typing import NamedTuple

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


class SessionKeys(NamedTuple):
    """The two 16-byte session keys of a handshake."""

    initiator_key: bytes
    recipient_key: bytes


def log_distance(a: bytes, b: bytes) -> int:
    """The number of bits of the XOR of two node IDs, 0 for equal IDs."""
    return _native.discv5_log_distance(a, b)


def ecdh(secret_key: bytes, public_key: bytes) -> bytes:
    """The 33-byte shared secret: the compressed point of the secret key times the public key."""
    return _native.discv5_ecdh(secret_key, public_key)


def derive_keys(
    ephemeral_key: bytes,
    dest_pubkey: bytes,
    node_id_a: bytes,
    node_id_b: bytes,
    challenge_data: bytes,
) -> SessionKeys:
    """The session keys from the ephemeral key of node A and the public key of node B."""
    raw = _native.discv5_derive_keys(
        ephemeral_key, dest_pubkey, node_id_a, node_id_b, challenge_data
    )
    return SessionKeys(raw[:16], raw[16:])


def id_sign(
    static_key: bytes, challenge_data: bytes, ephemeral_pubkey: bytes, node_id_b: bytes
) -> bytes:
    """The 64-byte ID signature r || s of node A."""
    return _native.discv5_id_sign(static_key, challenge_data, ephemeral_pubkey, node_id_b)


def id_verify(
    public_key: bytes,
    challenge_data: bytes,
    ephemeral_pubkey: bytes,
    node_id_b: bytes,
    signature: bytes,
) -> bool:
    """Whether an ID signature verifies under the public key of node A."""
    return _native.discv5_id_verify(
        public_key, challenge_data, ephemeral_pubkey, node_id_b, signature
    )


__all__ = ["SessionKeys", "log_distance", "ecdh", "derive_keys", "id_sign", "id_verify"]
