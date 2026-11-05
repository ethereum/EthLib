"""Proof of work of the execution layer, before Paris."""

from collections.abc import Sequence

from ...errors import BlockError
from ...serialization import rlp

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


def seal_hash(fork: str, header: bytes) -> bytes:
    """The Keccak-256 hash of a header without its mix digest and nonce."""
    return _native.pow_seal_hash(fork.encode(), header)


def check_proof_of_work(fork: str, header: bytes) -> bool:
    """Check the proof of work of a header in RLP form, at a fork before Paris."""
    return _native.pow_check(fork.encode(), header)


def chain_forks(forks: str | Sequence[tuple[str, int]]) -> bytes:
    """The RLP form of the forks of a chain with their first blocks; a name alone starts at 0."""
    if isinstance(forks, str):
        forks = [(forks, 0)]
    return rlp.encode([[name.encode(), first.to_bytes((first.bit_length() + 7) // 8, "big")]
                       for name, first in forks])


def validate_ommers(forks: str | Sequence[tuple[str, int]], recent: list[bytes], block: bytes,
                    check_seal: bool = True) -> bool:
    """Check the ommers of a block against the last seven blocks of its chain, each at its fork."""
    items = rlp.encode([rlp.decode(b) for b in recent])
    return _native.pow_validate_ommers(chain_forks(forks), items, block, check_seal)


__all__ = [
    "BlockError",
    "block_difficulty",
    "chain_forks",
    "check_proof_of_work",
    "seal_hash",
    "validate_ommers",
]
