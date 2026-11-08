"""CRC-32, the CRC of ISO 3309 and ITU-T V.42 that gzip (RFC 1952) and EIP-2124 use."""

from ethlib.cryptography import _native


def digest(data: bytes) -> bytes:
    """The four CRC-32 digest bytes of the message, least significant byte first."""
    return _native.crc32(data)


def crc32(data: bytes) -> int:
    """CRC-32 as a number, the value of RFC 1952 §8 and of `zlib.crc32`."""
    return _native.crc32_number(data)


__all__ = [
    "crc32",
    "digest",
]
