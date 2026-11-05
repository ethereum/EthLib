"""CRC-32 against the fork hashes of EIP-2124, the CRC catalogue and zlib."""

import random
import zlib

import pytest

from ethlib.cryptography import crc32
from raising import raises

# The genesis hash of mainnet.
MAINNET_GENESIS = bytes.fromhex("d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3")

# The mainnet fork hashes of EIP-2124.
#
# Section: Test Cases
# File: EIPS/eip-2124.md
# Repository: ethereum/EIPs
# Commit: 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445
#
# Each hash is CRC-32 of the genesis hash and the fork blocks passed so far.
# Each block number enters as a big-endian uint64.
# Constantinople and Petersburg share block 7280000, which enters once.
FORK_HASHES = [
    ([], 0xFC64EC04),
    ([1150000], 0x97C2C34C),
    ([1150000, 1920000], 0x91D1F948),
    ([1150000, 1920000, 2463000], 0x7A64DA13),
    ([1150000, 1920000, 2463000, 2675000], 0x3EDD5B10),
    ([1150000, 1920000, 2463000, 2675000, 4370000], 0xA00BC324),
    ([1150000, 1920000, 2463000, 2675000, 4370000, 7280000], 0x668DB0AF),
]


@pytest.mark.parametrize("blocks, fork_hash", FORK_HASHES)
def test_eip2124_fork_hash(blocks: list[int], fork_hash: int) -> None:
    data = MAINNET_GENESIS + b"".join(n.to_bytes(8, "big") for n in blocks)
    assert crc32.crc32(data) == fork_hash
    # EIP-2124 sends the number as four big-endian bytes, the digest bytes in reverse.
    assert crc32.digest(data) == fork_hash.to_bytes(4, "little")


def test_catalogue() -> None:
    # CRC-32/ISO-HDLC of https://reveng.sourceforge.io/crc-catalogue/17plus.htm#crc.cat.crc-32-iso-hdlc.
    # The empty message leaves the register at 0xffffffff, so the CRC is 0.
    assert crc32.crc32(b"") == 0
    # The check value: the nine ASCII bytes "123456789".
    assert crc32.crc32(b"123456789") == 0xCBF43926


def test_zlib() -> None:
    # Random messages of every length up to 200 bytes, with a fixed seed.
    rng = random.Random(2124)
    for size in range(200):
        data = rng.randbytes(size)
        assert crc32.crc32(data) == zlib.crc32(data)


def test_rejects_non_bytes() -> None:
    with raises(TypeError, "data must be bytes"):
        crc32.digest("abc")  # ty: ignore[invalid-argument-type]
