"""Snappy blocks of the compressor, read by a decoder written here from format_description.txt."""

# The decoder below follows format_description.txt and shares no code with EthLib:
# https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt
# It reads the 50 ssz_snappy files of consensus-spec-tests, whose blocks another compressor wrote.
# It must give the data that consensus_spec_tests.json records for them.
# It then reads the blocks of the compressor of EthLib, which must give back their input.

import hashlib
import json
import random
from pathlib import Path

import pytest

from ethlib.networking import snappy
from raising import raises

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "snappy"
CASES = json.loads((Path(__file__).resolve().parent / "consensus_spec_tests.json").read_text())


def _uint(data: bytes, at: int, n: int) -> int:
    # n little-endian bytes from `at`, all inside the block.
    if at + n > len(data):
        raise ValueError("element past the end")
    return int.from_bytes(data[at : at + n], "little")


def _decode(block: bytes) -> bytes:
    # The preamble: the length as a varint of at most five bytes, below 2^32 (§1).
    declared, shift, at = 0, 0, 0
    while True:
        if at == len(block) or at == 5:
            raise ValueError("bad preamble")
        byte = block[at]
        declared |= (byte & 0x7F) << shift
        shift, at = shift + 7, at + 1
        if byte < 0x80:
            break
    if declared >= 1 << 32:
        raise ValueError("preamble too large")
    out = bytearray()
    while at < len(block):
        tag, kind = block[at], block[at] & 3
        at += 1
        if kind == 0:
            # A literal: its length minus one in the tag, or in one to four bytes after it (§2.1).
            if tag >> 2 < 60:
                length = (tag >> 2) + 1
            else:
                extra = (tag >> 2) - 59
                length = _uint(block, at, extra) + 1
                at += extra
            if at + length > len(block):
                raise ValueError("literal past the end")
            out += block[at : at + length]
            at += length
            continue
        if kind == 1:
            # A copy with a one-byte offset: length 4 to 11, offset of 11 bits (§2.2.1).
            length = (tag >> 2 & 7) + 4
            offset = (tag >> 5) << 8 | _uint(block, at, 1)
            at += 1
        else:
            # A copy with a two-byte or four-byte offset: length 1 to 64 (§2.2.2, §2.2.3).
            width = 2 if kind == 2 else 4
            length = (tag >> 2) + 1
            offset = _uint(block, at, width)
            at += width
        if not 0 < offset <= len(out):
            raise ValueError("bad offset")
        # A copy may overlap the bytes it writes, so it goes one byte at a time (§2.2).
        for _ in range(length):
            out.append(out[-offset])
    if len(out) != declared:
        raise ValueError("length mismatch")
    return bytes(out)


# Hand-built blocks with the element kinds that the other blocks here never hold.
GOOD_BLOCKS = [
    # A literal of one byte whose length is written in four extra bytes (§2.1).
    ("01fc0000000041", b"A"),
    # A copy with a four-byte offset: offset 4, length 4 (§2.2.3).
    ("080c414243440f04000000", b"ABCDABCD"),
]


@pytest.mark.parametrize(("block", "data"), GOOD_BLOCKS)
def test_decoder_reads(block: str, data: bytes) -> None:
    assert _decode(bytes.fromhex(block)) == data


# Each malformed block and the fault the decoder finds, so the decoder can fail.
BAD_BLOCKS = [
    ("", "bad preamble"),
    ("808080808000", "bad preamble"),
    ("8080808010", "preamble too large"),
    ("050841", "literal past the end"),
    ("0500410e", "element past the end"),
    ("0500410100", "bad offset"),
    ("040101", "bad offset"),
    ("020041", "length mismatch"),
]


@pytest.mark.parametrize(("block", "fault"), BAD_BLOCKS)
def test_decoder_rejects(block: str, fault: str) -> None:
    with raises(ValueError, fault):
        _decode(bytes.fromhex(block))


def _payload(case: dict) -> bytes:
    data = _decode((FILES / case["file"]).read_bytes())
    assert len(data) == case["size"]
    assert hashlib.sha256(data).hexdigest() == case["sha256"]
    return data


@pytest.mark.parametrize("case", CASES, ids=[case["file"] for case in CASES])
def test_decoder_reads_consensus_spec_tests(case: dict) -> None:
    _payload(case)


@pytest.mark.parametrize("case", CASES, ids=[case["file"] for case in CASES])
def test_compress_consensus_spec_tests(case: dict) -> None:
    data = _payload(case)
    assert _decode(snappy.compress(data)) == data


def _noise(n: int) -> bytes:
    return random.Random(1378).randbytes(n)


# Random runs whose lengths cross the sizes of a literal length (§2.1).
INPUTS = [
    pytest.param(b"", id="empty"),
    pytest.param(b"\x00", id="1 byte"),
    pytest.param(bytes(4), id="4 equal bytes"),
    pytest.param(bytes(200_000), id="200000 equal bytes"),
    pytest.param(_noise(60), id="60 random bytes"),
    pytest.param(_noise(61), id="61 random bytes"),
    pytest.param(_noise(256), id="256 random bytes"),
    pytest.param(_noise(257), id="257 random bytes"),
    pytest.param(_noise(65_536), id="65536 random bytes"),
    pytest.param(_noise(65_537), id="65537 random bytes"),
    # A repeat at the largest offset of a copy with a two-byte offset (§2.2.2).
    pytest.param(_noise(65_535) * 2, id="repeat at distance 65535"),
    pytest.param(b"abc" * 30_000, id="period 3"),
    pytest.param(b"".join(_noise(37) * 5 + _noise(500) for _ in range(40)), id="mixed"),
]


@pytest.mark.parametrize("data", INPUTS)
def test_compress(data: bytes) -> None:
    assert _decode(snappy.compress(data)) == data
