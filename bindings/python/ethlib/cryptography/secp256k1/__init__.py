"""secp256k1 ECDSA, as Ethereum uses it.

- A public key is either SEC 1 encoding: 33 bytes compressed, or 65 bytes uncompressed.
- A hash is 32 bytes.
- A signature is 64 bytes: r then s, each a 32-byte big-endian integer.

Malformed arguments raise TypeError or ValueError, and so does a public key the spec rejects.
"""

from .._native import (
    secp256k1_verify,
    secp256k1_is_low_s,
    secp256k1_recover,
    SECP256K1_HASH_LEN as HASH_LEN,
    SECP256K1_SIGNATURE_LEN as SIGNATURE_LEN,
)


def verify(public_key: bytes, msg_hash: bytes, signature: bytes) -> bool:
    """Whether the signature on the hash is valid under the public key, by SEC 1 v2 §4.1.4.

    It accepts a high s, as ECDSA does.
    """
    return secp256k1_verify(public_key, msg_hash, signature)


def is_low_s(signature: bytes) -> bool:
    """Whether s is at most n / 2, the rule EIP-2 sets for transactions."""
    return secp256k1_is_low_s(signature)


def recover(msg_hash: bytes, signature: bytes, recovery_id: int) -> bytes:
    """The public key that signed the hash, by SEC 1 v2 §4.1.6, as 65 uncompressed bytes.

    The recovery id is 0 or 1: the parity of the y of the signer's point R.
    A signature with no key for that id raises ValueError.
    """
    return secp256k1_recover(msg_hash, signature, recovery_id)


__all__ = ["verify", "is_low_s", "recover", "HASH_LEN", "SIGNATURE_LEN"]
