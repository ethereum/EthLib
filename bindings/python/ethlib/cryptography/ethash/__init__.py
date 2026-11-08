"""Ethash, the proof of work of Ethereum before Paris."""

from ethlib.cryptography import _native
from ethlib.errors import EthashError


def cache_size(block_number: int) -> int:
    """The bytes in the cache of the epoch of a block."""
    return _native.ethash_cache_size(block_number)


def dataset_size(block_number: int) -> int:
    """The bytes in the dataset of the epoch of a block."""
    return _native.ethash_dataset_size(block_number)


def seed(block_number: int) -> bytes:
    """The 32-byte seed of the epoch of a block."""
    return _native.ethash_seed(block_number)


def cache(block_number: int) -> bytes:
    """The cache of the epoch of a block: its items in order, 64 bytes each."""
    return _native.ethash_cache(block_number)


def dataset_item(cache: bytes, index: int) -> bytes:
    """The 64-byte dataset item at an index, from a cache given as its bytes."""
    return _native.ethash_dataset_item(cache, index)


def hashimoto_light(
    dataset_size: int, cache: bytes, header_hash: bytes, nonce: bytes
) -> tuple[bytes, bytes]:
    """The mix digest and the result of the proof-of-work function, from a cache."""
    return _native.ethash_hashimoto_light(dataset_size, cache, header_hash, nonce)


__all__ = [
    "EthashError",
    "cache",
    "cache_size",
    "dataset_item",
    "dataset_size",
    "hashimoto_light",
    "seed",
]
