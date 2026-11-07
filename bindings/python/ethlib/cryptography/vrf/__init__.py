"""The VRF tree: verify an opening, and compute the secret and the output of a seed."""

# Malformed arguments raise TypeError, ValueError or OverflowError.
# Verification never raises on bytes: it returns None for every input it rejects.

from ethlib.cryptography._native import vrf_evaluate, vrf_secret, vrf_verify
from ethlib.errors import VrfError


def verify(root: bytes, index: int, opening: bytes) -> bytes | None:
    """The 32-byte output at an index, or None when the opening does not verify."""
    # A root that is not 32 bytes gives None.
    # So does an opening that is not 1056 bytes, or an index from 2^32 on.
    return vrf_verify(root, index, opening)


def secret(seed: bytes, index: int) -> bytes:
    """The secret of an index below 2^32, from a secret 32-byte seed, not in constant time."""
    return vrf_secret(seed, index)


def evaluate(seed: bytes, index: int) -> bytes:
    """The output at an index below 2^32, from a secret 32-byte seed, not in constant time."""
    return vrf_evaluate(seed, index)


__all__ = [
    "VrfError",
    "verify",
    "secret",
    "evaluate",
]
