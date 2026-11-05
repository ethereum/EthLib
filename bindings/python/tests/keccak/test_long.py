"""Keccak-256 and Keccak-512 against the long-message and Monte Carlo known answers of the Keccak team."""

import os
from pathlib import Path

import pytest

from ethlib.cryptography.keccak import keccak256, keccak512

KAT = Path(__file__).resolve().parent / "kat"


def _fields(name: str) -> list[tuple[str, str]]:
    """The (key, value) pairs of a file, in order, without comments and blank lines."""
    pairs = []
    for line in (KAT / name).read_text().splitlines():
        key, sep, value = line.partition(" = ")
        if sep:
            pairs.append((key.strip(), value.strip()))
    return pairs


# The two widths: the hash, its digest length in bytes, and the suffix of its file names.
WIDTHS = {256: (keccak256, 32), 512: (keccak512, 64)}


def _long_cases(width: int) -> list[tuple[int, bytes, bytes]]:
    """The (length in bits, message, digest) of each case of the long-message excerpt."""
    fields = _fields(f"LongMsgKAT_{width}_bytes.txt")
    assert [key for key, _ in fields] == ["Len", "Msg", "MD"] * (len(fields) // 3)
    return [
        (int(fields[i][1]), bytes.fromhex(fields[i + 1][1]), bytes.fromhex(fields[i + 2][1]))
        for i in range(0, len(fields), 3)
    ]


LONG = {width: _long_cases(width) for width in WIDTHS}


@pytest.mark.parametrize("width", WIDTHS)
def test_long_excerpt_is_complete(width: int) -> None:
    # Each LongMsgKAT file holds 513 lengths from 2048 bits, in steps of 63 bits.
    # Every eighth length is whole bytes: 65 cases, in steps of 504 bits.
    assert [bits for bits, _, _ in LONG[width]] == list(range(2048, 34304 + 1, 504))


@pytest.mark.parametrize(
    "width, bits, message, digest",
    [
        pytest.param(width, *case, id=f"{width}-{case[0]}")
        for width in WIDTHS
        for case in LONG[width]
    ],
)
def test_long_message(width: int, bits: int, message: bytes, digest: bytes) -> None:
    hash_fn, size = WIDTHS[width]
    assert len(message) * 8 == bits and len(digest) == size
    assert hash_fn(message) == digest


@pytest.mark.parametrize("width", WIDTHS)
def test_monte_carlo(width: int) -> None:
    # The Monte Carlo test of the SHA-3 competition: the message is a 128-byte window.
    # Each hash puts its digest in front and drops as many bytes from the end.
    # Every 1000 hashes, the digest is a checkpoint.
    hash_fn, size = WIDTHS[width]
    fields = _fields(f"MonteCarlo_{width}.txt")
    assert fields[0][0] == "Seed"
    message = bytes.fromhex(fields[0][1])
    assert len(message) == 128
    checkpoints = fields[1:]
    assert [key for key, _ in checkpoints] == ["j", "MD"] * 100
    for j in range(100):
        assert int(checkpoints[2 * j][1]) == j
        for _ in range(1000):
            digest = hash_fn(message)
            message = digest + message[: 128 - size]
        assert digest == bytes.fromhex(checkpoints[2 * j + 1][1]), f"checkpoint {j}"


# The one case of ExtremelyLongMsgKAT_256.txt and of ExtremelyLongMsgKAT_512.txt: a 64-byte text
# repeated 2^24 times, 1 GiB.
EXTREMELY_LONG_TEXT = b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno"
EXTREMELY_LONG_REPEAT = 16777216
EXTREMELY_LONG_DIGEST = {
    256: "5F313C39963DCF792B5470D4ADE9F3A356A3E4021748690A958372E2B06F82A4",
    512: "3E122EDAF37398231CFACA4C7C216C9D66D5B899EC1D7AC617C40C7261906A45"
    "FC01617A021E5DA3BD8D4182695B5CB785A28237CBB167590E34718E56D8AAB8",
}


@pytest.mark.skipif(
    os.environ.get("ETHLIB_SLOW_VECTORS") != "1",
    reason="a 1 GiB message, run weekly with ETHLIB_SLOW_VECTORS=1",
)
@pytest.mark.parametrize("width", WIDTHS)
def test_extremely_long_message(width: int) -> None:
    hash_fn, _ = WIDTHS[width]
    message = EXTREMELY_LONG_TEXT * EXTREMELY_LONG_REPEAT
    assert hash_fn(message) == bytes.fromhex(EXTREMELY_LONG_DIGEST[width])
