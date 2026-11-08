"""Node distances, handshake cryptography and packets of discv5."""

from typing import NamedTuple

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import Discv5Error

# An invalid input raises `Discv5Error`, a `ValueError`.


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
    return SessionKeys(
        *_native.discv5_derive_keys(
            ephemeral_key, dest_pubkey, node_id_a, node_id_b, challenge_data
        )
    )


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


def decode_packet(dest_id: bytes, packet: bytes) -> dict:
    """The fields of a packet that node dest_id reads, with message_ad its additional data."""
    return _native.discv5_decode_packet(dest_id, packet)


def reencode_packet(dest_id: bytes, packet: bytes) -> bytes:
    """The bytes of the decoded packet, written again by the encoder."""
    return _native.discv5_reencode_packet(dest_id, packet)


def encrypt_message(key: bytes, nonce: bytes, plaintext: bytes, ad: bytes) -> bytes:
    """AES-128-GCM of the plaintext, then the 16-byte tag."""
    return _native.discv5_encrypt_message(key, nonce, plaintext, ad)


def decrypt_message(key: bytes, nonce: bytes, message: bytes, ad: bytes) -> bytes:
    """The plaintext of an encrypted message that authenticates."""
    return _native.discv5_decrypt_message(key, nonce, message, ad)


def decode_message(plaintext: bytes) -> dict:
    """The type and the fields of a message plaintext."""
    return _native.discv5_decode_message(plaintext)


def reencode_message(plaintext: bytes) -> bytes:
    """The plaintext of the decoded message, written again by the encoder."""
    return _native.discv5_reencode_message(plaintext)


def make_whoareyou(
    dest_id: bytes, masking_iv: bytes, nonce: bytes, id_nonce: bytes, enr_seq: int
) -> tuple[bytes, bytes]:
    """Node B's WHOAREYOU packet for node dest_id, and its challenge data."""
    return _native.discv5_make_whoareyou(dest_id, masking_iv, nonce, id_nonce, enr_seq)


def read_whoareyou(dest_id: bytes, packet: bytes) -> dict:
    """The nonce, the ID nonce, the enr-seq and the challenge data of a WHOAREYOU packet."""
    return _native.discv5_read_whoareyou(dest_id, packet)


def seal_message(
    key: bytes,
    src_id: bytes,
    dest_id: bytes,
    masking_iv: bytes,
    nonce: bytes,
    plaintext: bytes,
) -> bytes:
    """An ordinary message packet from src_id to dest_id, under a 16-byte session key."""
    return _native.discv5_seal_message(key, src_id, dest_id, masking_iv, nonce, plaintext)


def open_message(key: bytes, src_id: bytes, dest_id: bytes, packet: bytes) -> bytes:
    """The plaintext of an ordinary message packet from src_id, under its session key."""
    return _native.discv5_open_message(key, src_id, dest_id, packet)


def seal_handshake(
    ephemeral_key: bytes,
    static_key: bytes,
    challenge_data: bytes,
    src_id: bytes,
    dest_id: bytes,
    dest_pubkey: bytes,
    masking_iv: bytes,
    nonce: bytes,
    record: bytes,
    plaintext: bytes,
) -> tuple[bytes, SessionKeys]:
    """Node A's handshake message packet for node B, and the session keys of node A."""
    packet, initiator_key, recipient_key = _native.discv5_seal_handshake(
        ephemeral_key,
        static_key,
        challenge_data,
        src_id,
        dest_id,
        dest_pubkey,
        masking_iv,
        nonce,
        record,
        plaintext,
    )
    return packet, SessionKeys(initiator_key, recipient_key)


def open_handshake(
    static_key: bytes, challenge_data: bytes, dest_id: bytes, src_pubkey: bytes, packet: bytes
) -> dict:
    """The source ID, the record, the plaintext and the session keys of a handshake packet."""
    fields = _native.discv5_open_handshake(static_key, challenge_data, dest_id, src_pubkey, packet)
    keys = SessionKeys(fields.pop("initiator_key"), fields.pop("recipient_key"))
    return {**fields, "keys": keys}


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
    "make_whoareyou",
    "read_whoareyou",
    "seal_message",
    "open_message",
    "seal_handshake",
    "open_handshake",
    "Discv5Error",
]
