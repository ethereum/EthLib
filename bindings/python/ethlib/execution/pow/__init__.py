"""Proof of work of the execution layer, before Paris."""

from ...errors import BlockError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


def _number(n: int) -> bytes:
    """The shortest big-endian bytes of a non-negative integer."""
    if n < 0:
        raise ValueError("a block quantity cannot be negative")
    return n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")


def block_difficulty(
    fork: str,
    number: int,
    timestamp: int,
    parent_timestamp: int,
    parent_difficulty: int,
    parent_ommers: int,
) -> int:
    """The difficulty of a block at a fork, from its parent and its parent's ommer count."""
    numbers = (number, timestamp, parent_timestamp, parent_difficulty, parent_ommers)
    result = _native.pow_block_difficulty(fork.encode(), *map(_number, numbers))
    return int.from_bytes(result, "big")


__all__ = [
    "BlockError",
    "block_difficulty",
]
