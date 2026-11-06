"""leanSPHINCS signatures: key generation, signing and verification."""

from ethlib.cryptography._native import (
    SPHINCS_MESSAGE_LEN as MESSAGE_LEN,
    SPHINCS_PUB_KEY_SIZE as PUB_KEY_SIZE,
    SPHINCS_SEED_LEN as SEED_LEN,
    SPHINCS_SIG_SIZE as SIG_SIZE,
    sphincs_key_gen,
    sphincs_sign,
    sphincs_verify,
)
from ethlib.errors import SphincsError

# A malformed argument raises `TypeError` or `ValueError`.
# A rejected input raises `SphincsError`, with the code and the message of the Lean error.


def key_gen(seed: bytes) -> bytes:
    """
    The public key grown from a 32-byte seed.

    It builds the whole top tree, 2^10 one-time keys.
    """
    return sphincs_key_gen(seed)


def sign(seed: bytes, message: bytes) -> bytes:
    """
    Sign a 32-byte message with the key grown from a seed.

    The message digest picks the FORS instance, so signing needs no index and keeps no state.

    Never sign more than 2^30 messages with one key.

    Each signature weakens the FORS instance it uses.
    """
    return sphincs_sign(seed, message)


def verify(public_key: bytes, message: bytes, signature: bytes) -> bool:
    """Whether a signature signs a message under a public key."""
    return sphincs_verify(public_key, message, signature)


__all__ = [
    "key_gen",
    "sign",
    "verify",
    "MESSAGE_LEN",
    "PUB_KEY_SIZE",
    "SEED_LEN",
    "SIG_SIZE",
    "SphincsError",
]
