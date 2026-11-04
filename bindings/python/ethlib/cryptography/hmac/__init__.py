"""HMAC-SHA-256, RFC 2104 §2.

The key is secret, and EthLib makes no constant-time claim.
"""

from .._native import hmac_sha256 as native_hmac_sha256


def hmac_sha256(key: bytes, message: bytes) -> bytes:
    """The 32-byte HMAC-SHA-256 tag of the message under the key.

    Every key and every message has a tag.

    A non-`bytes` argument raises `TypeError`.
    """
    return native_hmac_sha256(key, message)


__all__ = [
    "hmac_sha256",
]
