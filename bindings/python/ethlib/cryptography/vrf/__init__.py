"""The VRF tree: verification of an opening, and the secret and the output of a seed.

- Malformed arguments raise TypeError, ValueError or OverflowError.
- Verification never raises on bytes: it returns None for every input it rejects.
"""

from .._native import vrf_evaluate, vrf_secret, vrf_verify


def verify(root: bytes, index: int, opening: bytes) -> bytes | None:
    """The 32-byte output at an index, or None when the opening does not verify.

    A root that is not 32 bytes, an opening that is not 1056 bytes,
    and an index from 2^32 on all give None.
    """
    return vrf_verify(root, index, opening)


def secret(seed: bytes, index: int) -> bytes:
    """The 32-byte secret of an index below 2^32, from a 32-byte seed.

    The seed is secret, and the computation is not constant-time.
    """
    return vrf_secret(seed, index)


def evaluate(seed: bytes, index: int) -> bytes:
    """The 32-byte output at an index below 2^32, from a 32-byte seed.

    The seed is secret, and the computation is not constant-time.
    """
    return vrf_evaluate(seed, index)


__all__ = [
    "verify",
    "secret",
    "evaluate",
]
