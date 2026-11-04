"""The Keccak-256 hash function: FIPS 202 Keccak[r = 1088, c = 512] with Keccak's padding."""

from .._native import keccak256 as native_keccak256
from .._native import keccak_f1600 as native_keccak_f1600


def keccak256(data: bytes) -> bytes:
    """The 32-byte Keccak-256 digest of the message.

    Every byte string has a digest.

    It differs from SHA3-256, whose padding starts with `0x06` instead of `0x01`.

    A non-`bytes` argument raises `TypeError`.
    """
    return native_keccak256(data)


def keccak_f1600(state: bytes) -> bytes:
    """The Keccak-f[1600] permutation of a 200-byte state string.

    Lane `i` is bytes `8i` to `8i + 7`, the first least significant, as in FIPS 202 §3.1.3.

    A state of another length raises `ValueError`, and a non-`bytes` argument raises `TypeError`.
    """
    return native_keccak_f1600(state)


__all__ = [
    "keccak256",
    "keccak_f1600",
]
