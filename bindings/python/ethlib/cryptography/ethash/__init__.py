"""Ethash, the proof of work of Ethereum before Paris."""

from ...errors import EthashError
from .. import _native


def _number(n: int) -> bytes:
    """The shortest big-endian bytes of a non-negative integer."""
    if n < 0:
        raise ValueError("an Ethash number cannot be negative")
    return n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")


def cache_size(block_number: int) -> int:
    """The bytes in the cache of the epoch of a block."""
    return int.from_bytes(_native.ethash_cache_size(_number(block_number)), "big")


def dataset_size(block_number: int) -> int:
    """The bytes in the dataset of the epoch of a block."""
    return int.from_bytes(_native.ethash_dataset_size(_number(block_number)), "big")


def seed(block_number: int) -> bytes:
    """The 32-byte seed of the epoch of a block."""
    return _native.ethash_seed(_number(block_number))


def cache(block_number: int) -> bytes:
    """The cache of the epoch of a block: its items in order, 64 bytes each."""
    return _native.ethash_cache(_number(block_number))


def dataset_item(cache: bytes, index: int) -> bytes:
    """The 64-byte dataset item at an index, from a cache given as its bytes."""
    return _native.ethash_dataset_item(cache, _number(index))


def hashimoto_light(
    dataset_size: int, cache: bytes, header_hash: bytes, nonce: bytes
) -> tuple[bytes, bytes]:
    """The mix digest and the result of the proof-of-work function, from a cache."""
    out = _native.ethash_hashimoto_light(_number(dataset_size), cache, header_hash, nonce)
    return out[:32], out[32:]


__all__ = [
    "EthashError",
    "cache",
    "cache_size",
    "dataset_item",
    "dataset_size",
    "hashimoto_light",
    "seed",
]
