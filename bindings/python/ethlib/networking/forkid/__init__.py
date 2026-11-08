"""The fork identifier of EIP-2124 and EIP-6122."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import ForkIdError

# A fork activates at a block number or at a timestamp.
BLOCK = 0
TIME = 1


def schedule(
    genesis_hash: bytes,
    genesis_time: int,
    forks: list[tuple[str, int, int]],
    merge_fork_block: int | None = None,
) -> bytes:
    """The RLP schedule of a chain, from its forks as (name, BLOCK or TIME, value)."""
    return _native.fork_id_schedule(genesis_hash, genesis_time, merge_fork_block, forks)


def fork_id(schedule: bytes, number: int, timestamp: int) -> tuple[bytes, int]:
    """The fork hash and the next fork of a node at a head."""
    return _native.fork_id(schedule, number, timestamp)


def mainnet_fork_id(number: int, timestamp: int) -> tuple[bytes, int]:
    """The fork hash and the next fork of a mainnet node at a head."""
    return _native.mainnet_fork_id(number, timestamp)


def encode(fork_hash: bytes, fork_next: int) -> bytes:
    """The RLP fork identifier [FORK_HASH, FORK_NEXT]."""
    return _native.fork_id_encode(fork_hash, fork_next)


def validate(schedule: bytes, number: int, timestamp: int, remote: bytes) -> None:
    """Accept the RLP fork identifier `remote` at a head, or raise ForkIdError."""
    _native.fork_id_validate(schedule, number, timestamp, remote)


__all__ = [
    "BLOCK",
    "TIME",
    "ForkIdError",
    "encode",
    "fork_id",
    "mainnet_fork_id",
    "schedule",
    "validate",
]
