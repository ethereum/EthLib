"""Snappy blocks of consensus-spec-tests and of EthLib's compressor, read by a reference decoder."""

# The decoder of `snappy_reference.py` follows format_description.txt, sharing no EthLib code.
# It reads the 50 ssz_snappy files of consensus-spec-tests, whose blocks another compressor wrote.
# It must give the data that consensus_spec_tests.json records for them.
# It then reads the blocks of the compressor of EthLib, which must give back their input.

import random

import pytest

from ethlib.networking import snappy
from raising import raises
from snappy_reference import CASES, SpecCase, decode_block, spec_object

# Hand-built blocks with the element kinds that the other blocks here never hold.
GOOD_BLOCKS = [
    # A literal of one byte whose length is written in four extra bytes (§2.1).
    ("01fc0000000041", b"A"),
    # A copy with a four-byte offset: offset 4, length 4 (§2.2.3).
    ("080c414243440f04000000", b"ABCDABCD"),
]


@pytest.mark.parametrize(("block", "data"), GOOD_BLOCKS)
def test_decoder_reads(block: str, data: bytes) -> None:
    assert decode_block(bytes.fromhex(block)) == data


# Each malformed block and the fault the decoder finds, to show that the decoder rejects.
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
        decode_block(bytes.fromhex(block))


@pytest.mark.parametrize("case", CASES, ids=[case["file"] for case in CASES])
def test_decoder_reads_consensus_spec_tests(case: SpecCase) -> None:
    spec_object(case)


@pytest.mark.parametrize("case", CASES, ids=[case["file"] for case in CASES])
def test_compress_consensus_spec_tests(case: SpecCase) -> None:
    data = spec_object(case)
    assert decode_block(snappy.compress(data)) == data


def _noise(n: int) -> bytes:
    return random.Random(1378).randbytes(n)


# Inputs of the compressor: empty and repeated data, and repeats at a distance.
# The random runs sit on each side of the literal length sizes 60, 256 and 65536 (§2.1).
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
    assert decode_block(snappy.compress(data)) == data
