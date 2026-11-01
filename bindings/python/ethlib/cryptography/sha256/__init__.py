"""The SHA-256 hash function, FIPS 180-4 §6.2.

The function is total: every byte string has a digest.
A non-`bytes` argument raises `TypeError`, as the wrapper checks its argument.
"""

from .._native import sha256 as native_sha256


def sha256(data: bytes) -> bytes:
    """The 32-byte SHA-256 digest of the message, FIPS 180-4 §6.2."""
    return native_sha256(data)


__all__ = [
    "sha256",
]
