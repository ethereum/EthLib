"""
CRC-32C, the Castagnoli CRC of RFC 3720 §12.1.

It detects errors and authenticates nothing: anyone can recompute it.
"""

from ethlib.cryptography._native import crc32c as native_crc32c


def digest(data: bytes) -> bytes:
    """
    The four CRC-32C digest bytes of the message, in the order of RFC 3720 §12.1.

    Every byte string has a digest.

    A non-`bytes` argument raises `TypeError`.
    """
    return native_crc32c(data)


def crc32c(data: bytes) -> int:
    """
    CRC-32C as a number: the digest bytes read least significant byte first.

    It is CRC-32/ISCSI of the CRC catalogue.

    A non-`bytes` argument raises `TypeError`.
    """
    return int.from_bytes(native_crc32c(data), "little")


__all__ = [
    "crc32c",
    "digest",
]
