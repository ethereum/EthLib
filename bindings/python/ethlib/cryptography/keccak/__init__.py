"""The Keccak-256 hash function: FIPS 202 Keccak[r = 1088, c = 512] with Keccak's padding."""

from .._native import keccak256 as native_keccak256


def keccak256(data: bytes) -> bytes:
    """The 32-byte Keccak-256 digest of the message.

    Every byte string has a digest.

    It differs from SHA3-256, whose padding starts with `0x06` instead of `0x01`.

    A non-`bytes` argument raises `TypeError`.
    """
    return native_keccak256(data)


__all__ = [
    "keccak256",
]
