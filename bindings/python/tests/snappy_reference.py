"""A Snappy block decoder written from the format, and the ssz_snappy files of the tests."""

# The decoder follows format_description.txt and shares no code with EthLib:
# https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt
#
# The 50 ssz_snappy files come from consensus-spec-tests.
# `tests/consensus/snappy/README.md` gives their origin and how they were chosen.
# consensus_spec_tests.json records the size and the SHA-256 digest of the data of each.
# The header of `snappy/test_consensus_spec_tests.py` says where those values come from.

import hashlib
import json
from pathlib import Path
from typing import TypedDict


class SpecCase(TypedDict):
    """One ssz_snappy file, and the size and SHA-256 digest of its data."""

    file: str
    size: int
    sha256: str


FILES = Path(__file__).resolve().parents[3] / "tests" / "consensus" / "snappy"
CASES: list[SpecCase] = json.loads(
    (Path(__file__).resolve().parent / "snappy" / "consensus_spec_tests.json").read_text()
)


def _uint(data: bytes, at: int, n: int) -> int:
    # n little-endian bytes from `at`, all inside the block.
    if at + n > len(data):
        raise ValueError("element past the end")
    return int.from_bytes(data[at : at + n], "little")


def decode_block(block: bytes) -> bytes:
    """The data of a Snappy block; raises ValueError if the block is malformed."""
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


def spec_object(case: SpecCase) -> bytes:
    """The data of an ssz_snappy file, checked against its recorded size and digest."""
    data = decode_block((FILES / case["file"]).read_bytes())
    # Not a test module, so pytest does not rewrite these asserts: each names its file.
    assert len(data) == case["size"], case["file"]
    assert hashlib.sha256(data).hexdigest() == case["sha256"], case["file"]
    return data
