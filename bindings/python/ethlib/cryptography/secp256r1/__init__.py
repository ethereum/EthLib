"""secp256r1 ECDSA verification, also called P-256."""

from ethlib.cryptography._native import (
    SECP256R1_HASH_LEN as HASH_LEN,
    SECP256R1_PUBLIC_KEY_LEN as PUBLIC_KEY_LEN,
    SECP256R1_SIGNATURE_LEN as SIGNATURE_LEN,
    secp256r1_verify,
)
from ethlib.errors import Secp256r1Error

# A public key is 64 bytes: x then y, each a 32-byte big-endian integer below p.
# A hash is 32 bytes.
# A signature is 64 bytes: r then s, each a 32-byte big-endian integer.
#
# An argument that is not bytes raises `TypeError`.
# Bytes of the wrong length or range raise `Secp256r1Error`, a `ValueError` with a code.


def verify(public_key: bytes, msg_hash: bytes, signature: bytes) -> bool:
    """
    Whether the signature on the hash is valid under the public key, by SEC 1 v2 §4.1.4.

    A key off the curve verifies nothing.
    """
    return secp256r1_verify(public_key, msg_hash, signature)


__all__ = ["verify", "PUBLIC_KEY_LEN", "HASH_LEN", "SIGNATURE_LEN", "Secp256r1Error"]
