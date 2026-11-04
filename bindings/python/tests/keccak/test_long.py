"""Keccak-256 against the long-message and Monte Carlo known answers of the Keccak team."""

import os
from pathlib import Path

import pytest

from ethlib.cryptography.keccak import keccak256

KAT = Path(__file__).resolve().parent / "kat"


def _fields(name: str) -> list[tuple[str, str]]:
    """The (key, value) pairs of a file, in order, without comments and blank lines."""
    pairs = []
    for line in (KAT / name).read_text().splitlines():
        key, sep, value = line.partition(" = ")
        if sep:
            pairs.append((key.strip(), value.strip()))
    return pairs


def _long_cases() -> list[tuple[int, bytes, bytes]]:
    """The (length in bits, message, digest) of each case of the long-message excerpt."""
    fields = _fields("LongMsgKAT_256_bytes.txt")
    assert [key for key, _ in fields] == ["Len", "Msg", "MD"] * (len(fields) // 3)
    return [(int(fields[i][1]), bytes.fromhex(fields[i + 1][1]), bytes.fromhex(fields[i + 2][1]))
            for i in range(0, len(fields), 3)]


LONG = _long_cases()


def test_long_excerpt_is_complete() -> None:
    # LongMsgKAT_256.txt holds 513 lengths from 2048 bits, in steps of 63 bits.
    # Every eighth length is whole bytes: 65 cases, in steps of 504 bits.
    assert [bits for bits, _, _ in LONG] == list(range(2048, 34304 + 1, 504))


@pytest.mark.parametrize("bits, message, digest", LONG, ids=[str(c[0]) for c in LONG])
def test_long_message(bits: int, message: bytes, digest: bytes) -> None:
    assert len(message) * 8 == bits
    assert keccak256(message) == digest


def test_monte_carlo() -> None:
    # The Monte Carlo test of the SHA-3 competition: the message is a 128-byte window.
    # Each hash puts its digest in front and drops the last 32 bytes.
    # Every 1000 hashes, the digest is a checkpoint.
    fields = _fields("MonteCarlo_256.txt")
    assert fields[0][0] == "Seed"
    message = bytes.fromhex(fields[0][1])
    assert len(message) == 128
    checkpoints = fields[1:]
    assert [key for key, _ in checkpoints] == ["j", "MD"] * 100
    for j in range(100):
        assert int(checkpoints[2 * j][1]) == j
        for _ in range(1000):
            digest = keccak256(message)
            message = digest + message[:96]
        assert digest == bytes.fromhex(checkpoints[2 * j + 1][1]), f"checkpoint {j}"


# The one case of ExtremelyLongMsgKAT_256.txt: a 64-byte text repeated 2^24 times, 1 GiB.
EXTREMELY_LONG_TEXT = b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno"
EXTREMELY_LONG_REPEAT = 16777216
EXTREMELY_LONG_DIGEST = "5F313C39963DCF792B5470D4ADE9F3A356A3E4021748690A958372E2B06F82A4"


@pytest.mark.skipif(os.environ.get("ETHLIB_SLOW_VECTORS") != "1",
                    reason="a 1 GiB message, run weekly with ETHLIB_SLOW_VECTORS=1")
def test_extremely_long_message() -> None:
    message = EXTREMELY_LONG_TEXT * EXTREMELY_LONG_REPEAT
    assert keccak256(message) == bytes.fromhex(EXTREMELY_LONG_DIGEST)
