"""CRC-32C, the Castagnoli CRC of RFC 3720 §12.1."""

from ethlib.cryptography import _native


def digest(data: bytes) -> bytes:
    """
    The four CRC-32C digest bytes of the message, in the order of RFC 3720 §12.1.

    Every byte string has a digest.

    It detects errors and authenticates nothing: anyone can recompute it.
    """
    return _native.crc32c(data)


def crc32c(data: bytes) -> int:
    """
    CRC-32C as a number: the digest bytes read least significant byte first.

    It is CRC-32/ISCSI of the CRC catalogue.
    """
    return _native.crc32c_number(data)


__all__ = [
    "crc32c",
    "digest",
]
