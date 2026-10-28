"""leanXMSS signatures: key generation, signing and verification only.

- Malformed arguments raise TypeError, ValueError or OverflowError.
- Inputs the spec rejects raise RuntimeError.
"""

from .._native import (
    xmss_key_gen,
    xmss_sign,
    xmss_verify,
    XMSS_MESSAGE_LEN as MESSAGE_LEN,
    XMSS_PUB_KEY_SIZE as PUB_KEY_SIZE,
    XMSS_SEED_LEN as SEED_LEN,
    XMSS_SIG_SIZE as SIG_SIZE,
)


def key_gen(seed: bytes) -> bytes:
    """The public key grown from a 32-byte seed.

    It builds the whole top tree, 2^16 one-time keys, so it takes a while.
    """
    return xmss_key_gen(seed)


def sign(seed: bytes, leaf_index: int, message: bytes) -> bytes:
    """Sign a 32-byte message at a leaf index below 2^32, with the key grown from a seed.

    Never sign two different messages at one leaf index: it breaks the key.
    """
    return xmss_sign(seed, leaf_index, message)


def verify(public_key: bytes, message: bytes, signature: bytes) -> bool:
    """Whether a signature signs a message under a public key.

    The leaf index travels inside the signature.
    """
    return xmss_verify(public_key, message, signature)


__all__ = [
    "key_gen",
    "sign",
    "verify",
    "MESSAGE_LEN",
    "PUB_KEY_SIZE",
    "SEED_LEN",
    "SIG_SIZE",
]
