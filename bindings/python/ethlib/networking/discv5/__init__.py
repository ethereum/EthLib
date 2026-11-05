"""Node distances, handshake cryptography and packets of discv5.

An invalid input raises Discv5Error, a ValueError.
"""

import json
from typing import NamedTuple

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import Discv5Error


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


def _hex_fields(raw: bytes) -> dict:
    fields = json.loads(raw)
    return {k: bytes.fromhex(v[2:]) if isinstance(v, str) else v for k, v in fields.items()}


def decode_packet(dest_id: bytes, packet: bytes) -> dict:
    """The fields of a packet that node dest_id reads, with message_ad its additional data."""
    return _hex_fields(_native.discv5_decode_packet(dest_id, packet))


def reencode_packet(dest_id: bytes, packet: bytes) -> bytes:
    """The bytes of the decoded packet, written again by the encoder."""
    return _native.discv5_reencode_packet(dest_id, packet)


def encrypt_message(key: bytes, nonce: bytes, plaintext: bytes, ad: bytes) -> bytes:
    """AES-128-GCM of the plaintext, then the 16-byte tag."""
    return _native.discv5_encrypt_message(key, nonce, plaintext, ad)


def decrypt_message(key: bytes, nonce: bytes, message: bytes, ad: bytes) -> bytes:
    """The plaintext of an encrypted message that authenticates."""
    return _native.discv5_decrypt_message(key, nonce, message, ad)


def _bytes_of(value):
    if isinstance(value, str):
        return bytes.fromhex(value[2:])
    if isinstance(value, list):
        return [_bytes_of(v) for v in value]
    return value


def decode_message(plaintext: bytes) -> dict:
    """The type and the fields of a message plaintext."""
    fields = json.loads(_native.discv5_decode_message(plaintext))
    return {k: _bytes_of(v) for k, v in fields.items()}


def reencode_message(plaintext: bytes) -> bytes:
    """The plaintext of the decoded message, written again by the encoder."""
    return _native.discv5_reencode_message(plaintext)


__all__ = [
    "SessionKeys",
    "log_distance",
    "ecdh",
    "derive_keys",
    "id_sign",
    "id_verify",
    "decode_packet",
    "reencode_packet",
    "encrypt_message",
    "decrypt_message",
    "decode_message",
    "reencode_message",
    "Discv5Error",
]
