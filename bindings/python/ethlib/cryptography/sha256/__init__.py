"""The SHA-256 hash function, FIPS 180-4 §6.2."""

from .._native import sha256 as native_sha256


def sha256(data: bytes) -> bytes:
    """The 32-byte SHA-256 digest of the message.

    Every byte string has a digest.

    A non-`bytes` argument raises `TypeError`.
    """
    return native_sha256(data)


__all__ = [
    "sha256",
]
