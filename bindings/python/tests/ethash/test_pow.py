"""The Ethash proof-of-work function and the header check against ethereum/tests."""

import json
import os
import random
from pathlib import Path

import pytest

from ethlib.cryptography import ethash
from ethlib.cryptography.keccak import keccak256, keccak512
from ethlib.errors import BlockError
from ethlib.execution.pow import check_proof_of_work, seal_hash
from ethlib.serialization import rlp

from .test_cache import _bytes, _fnv, _reference_item, _words

# The two cases of ethereum/tests PoWTests/ethash_tests.json, both at epoch 0.
_POW = json.loads((Path(__file__).resolve().parent / "vectors" / "ethash_tests.json").read_text())

# Each Ethash run builds the 16 MiB cache of epoch 0, which takes seconds, so these run weekly.
SLOW = os.environ.get("ETHLIB_SLOW_VECTORS") == "1"
slow = pytest.mark.skipif(not SLOW, reason="the cache of epoch 0, run weekly")

# Both headers have the 15 fields of a header before London.
FORK = "frontier"


def _difficulty(header: bytes) -> int:
    """The difficulty of a header, its eighth field."""
    return int.from_bytes(rlp.decode(header)[7], "big")


@pytest.mark.parametrize("name", sorted(_POW))
def test_seal_hash(name: str) -> None:
    # The header without its mix digest and nonce hashes to the case's header hash.
    case = _POW[name]
    assert seal_hash(FORK, bytes.fromhex(case["header"])) == bytes.fromhex(case["header_hash"])


@pytest.fixture(scope="module")
def cache_epoch_0() -> bytes:
    return ethash.cache(0)


@slow
@pytest.mark.parametrize("name", sorted(_POW))
def test_hashimoto_light(name: str, cache_epoch_0: bytes) -> None:
    # The function gives the case's mix digest and result.
    case = _POW[name]
    mix, result = ethash.hashimoto_light(
        case["full_size"],
        cache_epoch_0,
        bytes.fromhex(case["header_hash"]),
        bytes.fromhex(case["nonce"]),
    )
    assert mix == bytes.fromhex(case["mixHash"])
    assert result == bytes.fromhex(case["result"])


@slow
@pytest.mark.parametrize("name", sorted(_POW))
def test_header_result_is_above_its_target(name: str) -> None:
    # The cases carry the right mix digest, but their result exceeds 2^256 over the difficulty.
    #
    #     first:  result 0xdd47... > 2^256 / 0x020000
    #     second: result 0xab9b... > 2^256 / 0x020040
    case = _POW[name]
    assert int(case["result"], 16) > 2**256 // _difficulty(bytes.fromhex(case["header"]))
    with pytest.raises(BlockError) as error:
        check_proof_of_work(FORK, bytes.fromhex(case["header"]))
    assert error.value.code == 223


@slow
def test_sealed_header_passes(cache_epoch_0: bytes) -> None:
    # Difficulty 1 accepts every result, so the first header sealed with its own mix digest
    # passes.
    fields = rlp.decode(bytes.fromhex(_POW["first"]["header"]))
    fields[7] = b"\x01"
    unsealed = rlp.encode(fields)
    mix, _ = ethash.hashimoto_light(
        _POW["first"]["full_size"], cache_epoch_0, seal_hash(FORK, unsealed), fields[14]
    )
    fields[13] = mix
    assert check_proof_of_work(FORK, rlp.encode(fields))


@slow
def test_wrong_mix_digest_is_rejected() -> None:
    # The mix digest of the first case sits just before its nonce: change its last byte.
    case = _POW["first"]
    header = bytearray(bytes.fromhex(case["header"]))
    at = header.rindex(bytes.fromhex(case["mixHash"])) + 31
    header[at] ^= 1
    with pytest.raises(BlockError) as error:
        check_proof_of_work(FORK, bytes(header))
    assert error.value.code == 222


def test_paris_has_no_proof_of_work() -> None:
    # From Paris on, the check refuses the header before any Ethash work.
    with pytest.raises(BlockError):
        check_proof_of_work("paris", bytes.fromhex(_POW["first"]["header"]))


def _reference_hashimoto(
    dataset_size: int, cache: list[list[int]], header_hash: bytes, nonce: bytes
) -> tuple[bytes, bytes]:
    """`hashimoto_light` of the Ethash specification, over `keccak` of the bindings."""
    s = _words(keccak512(header_hash + nonce[::-1]))
    mix = s + s
    pairs = dataset_size // 128
    for i in range(64):
        p = _fnv(i ^ s[0], mix[i % 32]) % pairs * 2
        new = _words(_reference_item(cache, p)) + _words(_reference_item(cache, p + 1))
        mix = [_fnv(a, b) for a, b in zip(mix, new, strict=True)]
    cmix = [_fnv(_fnv(_fnv(mix[i], mix[i + 1]), mix[i + 2]), mix[i + 3]) for i in range(0, 32, 4)]
    return _bytes(cmix), keccak256(_bytes(s) + _bytes(cmix))


@pytest.mark.parametrize("items, pairs", [(3, 5), (11, 7)])
def test_hashimoto_light_against_the_specification(items: int, pairs: int) -> None:
    # A small random cache and dataset, fixed by their sizes, and a fixed header hash and nonce.
    rng = random.Random(items * 100 + pairs)
    raw = bytes(rng.getrandbits(8) for _ in range(64 * items))
    cache = [_words(raw[64 * k : 64 * k + 64]) for k in range(items)]
    header_hash, nonce = bytes(range(32)), bytes.fromhex("0102030405060708")
    expected = _reference_hashimoto(128 * pairs, cache, header_hash, nonce)
    assert ethash.hashimoto_light(128 * pairs, raw, header_hash, nonce) == expected
