"""
Key derivation with SHA-256: HKDF of RFC 5869 and the Concatenation KDF of SP 800-56C.

The input keying material and the shared secret are secret.

EthLib makes no constant-time claim.
"""

from ethlib.cryptography._native import (
    concat_kdf_sha256 as native_concat_kdf_sha256,
    hkdf_sha256 as native_hkdf_sha256,
    hmac_sha256 as native_hmac_sha256,
)
from ethlib.errors import ConcatKdfError, HkdfError


def hkdf_extract(salt: bytes, ikm: bytes) -> bytes:
    """
    HKDF-Extract of RFC 5869 §2.2: the 32-byte pseudorandom key `HMAC-SHA-256(salt, IKM)`.

    An empty salt gives the same key as 32 zero bytes, the RFC's default.

    A non-`bytes` argument raises `TypeError`.
    """
    return native_hmac_sha256(salt, ikm)


def hkdf(salt: bytes, ikm: bytes, info: bytes, length: int) -> bytes:
    """HKDF-SHA-256 of RFC 5869 §2: `length` bytes of output keying material."""
    return native_hkdf_sha256(salt, ikm, info, length)


def concat_kdf(z: bytes, fixed_info: bytes, length: int) -> bytes:
    """The Concatenation KDF of SP 800-56C Rev. 2 §4.1 with SHA-256: `length` bytes of key."""
    return native_concat_kdf_sha256(z, fixed_info, length)


__all__ = [
    "ConcatKdfError",
    "HkdfError",
    "concat_kdf",
    "hkdf",
    "hkdf_extract",
]
