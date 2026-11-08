"""The Ethash sizes, seed, cache and dataset items against their pinned sources."""

import json
import os
import random
import re
from pathlib import Path

import pytest

from ethlib.cryptography import ethash
from ethlib.cryptography.keccak import keccak256, keccak512
from ethlib.errors import EthashError
from raising import raises

_DIR = Path(__file__).resolve().parent

# The two cases of ethereum/tests PoWTests/ethash_tests.json, both at epoch 0.
_POW = json.loads((_DIR / "vectors" / "ethash_tests.json").read_text())

# The cache of epoch 0 is 16 MiB and takes seconds, so its test runs weekly.
SLOW = os.environ.get("ETHLIB_SLOW_VECTORS") == "1"


def _table(name: str) -> list[int]:
    """The list `name = [...]` of the appendix of the vendored Ethash specification."""
    text = (_DIR / "spec" / "index.md.txt").read_text()
    body = re.search(rf"{name} = \[(.*?)\]", text, re.S)
    assert body is not None, name
    return [int(x) for x in re.findall(r"\d+", body.group(1))]


_DATA_SIZES = _table("data_sizes")
_CACHE_SIZES = _table("cache_sizes")

# Invariant: the appendix tabulates 2048 epochs of each size.
assert len(_DATA_SIZES) == len(_CACHE_SIZES) == 2048


def test_sizes_of_every_tabulated_epoch() -> None:
    # The first block of each epoch, and the last one, give the tabulated sizes.
    for e in range(2048):
        for number in (30000 * e, 30000 * e + 29999):
            assert ethash.dataset_size(number) == _DATA_SIZES[e], e
            assert ethash.cache_size(number) == _CACHE_SIZES[e], e


@pytest.mark.parametrize("name", sorted(_POW))
def test_sizes_and_seed_of_the_pow_tests(name: str) -> None:
    case = _POW[name]
    # Both blocks are in epoch 0, so the number 0 stands for them.
    assert ethash.cache_size(0) == case["cache_size"]
    assert ethash.dataset_size(0) == case["full_size"]
    assert ethash.seed(0) == bytes.fromhex(case["seed"])


def test_seed_chain() -> None:
    # Each epoch hashes the seed of the epoch before, from 32 zero bytes.
    expected = bytes(32)
    for e in range(5):
        assert ethash.seed(30000 * e + 12345) == expected
        expected = keccak256(expected)


@pytest.mark.skipif(not SLOW, reason="the 16 MiB cache of epoch 0, run weekly")
def test_cache_digest_of_epoch_0() -> None:
    # Both cases give the same digest, of the whole cache of epoch 0.
    digests = {case["cache_hash"] for case in _POW.values()}
    assert len(digests) == 1
    assert keccak256(ethash.cache(0)).hex() == digests.pop()


def _fnv(a: int, b: int) -> int:
    """The FNV function of the Ethash specification."""
    return ((a * 0x01000193) ^ b) % 2**32


def _words(data: bytes) -> list[int]:
    return [int.from_bytes(data[i : i + 4], "little") for i in range(0, len(data), 4)]


def _bytes(words: list[int]) -> bytes:
    return b"".join(w.to_bytes(4, "little") for w in words)


def _reference_item(cache: list[list[int]], i: int) -> bytes:
    """`calc_dataset_item` of the Ethash specification, over `keccak512` of the bindings."""
    n = len(cache)
    mix = list(cache[i % n])
    mix[0] ^= i
    mix = _words(keccak512(_bytes(mix)))
    for j in range(256):
        parent = cache[_fnv(i ^ j, mix[j % 16]) % n]
        mix = [_fnv(a, b) for a, b in zip(mix, parent, strict=True)]
    return keccak512(_bytes(mix))


@pytest.mark.parametrize("items", [1, 2, 7, 64])
def test_dataset_item_against_the_specification(items: int) -> None:
    # A random cache of a few items, fixed by its seed, and a spread of indices.
    rng = random.Random(items)
    raw = bytes(rng.getrandbits(8) for _ in range(64 * items))
    cache = [_words(raw[64 * k : 64 * k + 64]) for k in range(items)]
    for index in (0, 1, items, 12345, 2**26 - 1):
        assert ethash.dataset_item(raw, index) == _reference_item(cache, index)


@pytest.mark.parametrize("cache", [b"", bytes(63), bytes(65)])
def test_dataset_item_rejects_a_bad_cache(cache: bytes) -> None:
    # A cache is a positive whole number of 64-byte items.
    message = f"Ethash: a cache is a positive multiple of 64 bytes, got {len(cache)}"
    with raises(EthashError, message):
        ethash.dataset_item(cache, 0)


def test_negative_block_number() -> None:
    with raises(ValueError, "cannot pass a negative int to Lean"):
        ethash.cache_size(-1)


def test_block_number_is_an_int() -> None:
    # A bool crosses as itself, not as 0 or 1, so Lean rejects it with code 0.
    with raises(EthashError, "expected an int") as error:
        ethash.cache_size(True)
    assert error.value.code == 0
