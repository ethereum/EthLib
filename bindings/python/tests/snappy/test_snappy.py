"""Snappy blocks and framed streams against hand-built cases and python-snappy output."""

# The two accepted framed streams and the block of 123456789 come from python-snappy 0.7.3 on
# cramjam 2.14.0. Every other case is built by hand from format_description.txt and
# framing_format.txt of google/snappy.

import pytest

from ethlib.networking import snappy
from raising import raises

A = b"\x41"

# ---- Blocks ---------------------------------------------------------------------------------

# Each block and its data.
BLOCKS = [
    # A literal of two bytes, its length in the tag.
    ("02044142", b"AB"),
    # Two literals in a row, which §2 permits.
    ("0200410042", b"AB"),
    # A literal of 61 bytes, the shortest whose length takes one extra byte (tag 60).
    ("3df03c" + "41" * 61, A * 61),
    # A literal of one byte whose length is written in four extra bytes (tag 63).
    ("01fc0000000041", A),
    # A copy with a one-byte offset: offset 1, length 4.
    ("0500410101", A * 5),
    # A copy with a one-byte offset of 256, so its top bits sit in the tag.
    ("8402f0ff" + bytes(range(256)).hex() + "2100", bytes(range(256)) + bytes([0, 1, 2, 3])),
    # A copy with a two-byte offset: offset 4, length 4.
    ("080c414243440e0400", b"ABCDABCD"),
    # A copy with a four-byte offset: offset 4, length 4.
    ("080c414243440f04000000", b"ABCDABCD"),
    # The example of §2.2: "xab" then a copy of offset 2 and length 4 gives "xababab".
    ("07087861620e0200", b"xababab"),
    # An overlapping copy of offset 1 and length 10: a run of one byte.
    ("0b00411901", A * 11),
    # An empty block: a preamble of zero and no elements.
    ("00", b""),
    # A preamble of one that is not minimally encoded, which §1 allows.
    ("81000041", A),
]


@pytest.mark.parametrize(("block", "data"), BLOCKS)
def test_decompress(block: str, data: bytes) -> None:
    assert snappy.decompress(bytes.fromhex(block)) == data


# Each data and the block of one literal that holds it.
LITERALS = [
    # The nine bytes 123456789: length 9, then a tag holding the length minus one.
    (b"123456789", "0920" + b"123456789".hex()),
    # Empty data: the length zero and no elements.
    (b"", "00"),
    # A literal of 60 bytes, the longest whose length fits in the tag.
    (A * 60, "3cec" + "41" * 60),
    # A literal of 61 bytes, the shortest whose length takes one extra byte (tag 60).
    (A * 61, "3df03c" + "41" * 61),
    # A literal of 257 bytes, whose length minus one, 256, takes two extra bytes (tag 61).
    (A * 257, "8102f40001" + "41" * 257),
]


@pytest.mark.parametrize(("data", "block"), LITERALS)
def test_compress_literal(data: bytes, block: str) -> None:
    assert snappy.compress_literal(data) == bytes.fromhex(block)


# Each rejected block and the fault that rejects it, one per fault.
BAD_BLOCKS = [
    # No bytes at all.
    ("", "preambleTruncated"),
    # A preamble whose last byte still carries the continuation bit.
    ("80", "preambleTruncated"),
    # A preamble that does not end within five bytes.
    ("808080808000", "preambleTooLong"),
    # A preamble declaring 2^32 bytes, one more than allowed.
    ("8080808010", "preambleTooLarge 4294967296"),
    # A literal of three bytes with one byte left in the input.
    ("050841", "literalPastEnd"),
    # A literal whose two length bytes are cut off after one.
    ("05f400", "literalPastEnd"),
    # A copy with a two-byte offset and no offset bytes.
    ("0500410e", "copyPastEnd"),
    # A copy with offset zero.
    ("0500410100", "copyOffsetZero"),
    # A copy of offset 5 after one byte of output.
    ("0500410105", "copyOffsetTooLarge 5"),
    # A block that starts with a copy.
    ("040101", "copyOffsetTooLarge 1"),
    # An output of one byte where the preamble declared two.
    ("020041", "lengthMismatch 2 1"),
    # An output of two bytes where the preamble declared one.
    ("01044142", "lengthMismatch 1 2"),
    # The same literal, then a copy with offset zero: the literal already passes the length.
    ("010441420100", "lengthMismatch 1 2"),
    # A copy of four bytes that would take one byte of output past the four declared.
    ("0400410101", "lengthMismatch 4 5"),
]


@pytest.mark.parametrize(("block", "fault"), BAD_BLOCKS)
def test_decompress_rejected(block: str, fault: str) -> None:
    with raises(ValueError, "block rejected: EthLib.Networking.Snappy.SnappyError." + fault):
        snappy.decompress(bytes.fromhex(block))


# ---- Frames ---------------------------------------------------------------------------------

STREAM_IDENTIFIER = bytes.fromhex("ff060000734e61507059")

# The nine bytes 123456789 in one uncompressed chunk, as python-snappy frames them.
FRAMED_DIGITS = STREAM_IDENTIFIER + bytes.fromhex("010d0000e5b08ac7") + b"123456789"


def test_masked_crc() -> None:
    # The CRC-32C of 123456789 is the check value 0xe3069283 of the CRC catalogue.
    # Rotated right by 15 bits and added to 0xa282ead8, it gives 0xc78ab0e5.
    assert snappy.masked_crc(b"123456789") == 0xC78AB0E5


def test_framed_digits() -> None:
    assert snappy.decode_frames(FRAMED_DIGITS) == b"123456789"
    # The encoder writes the same stream, byte for byte.
    assert snappy.encode_frames_literal(b"123456789") == FRAMED_DIGITS


def test_framed_zeros() -> None:
    # 32 zero bytes in one compressed chunk, as python-snappy frames them.
    # The block is the length 32, a literal of one zero byte, and a copy of 31 bytes from 1 back.
    stream = STREAM_IDENTIFIER + bytes.fromhex("000a0000faffd70f2000007a0100")
    assert snappy.decode_frames(stream) == bytes(32)


def test_framed_empty() -> None:
    # The encoder writes the stream identifier alone, which decodes to nothing.
    assert snappy.encode_frames_literal(b"") == STREAM_IDENTIFIER
    assert snappy.decode_frames(STREAM_IDENTIFIER) == b""


def test_skipped_chunks() -> None:
    # A second stream identifier, then a padding chunk and a reserved skippable chunk, add nothing.
    stream = STREAM_IDENTIFIER * 2 + bytes.fromhex("fe02000000008001000041")
    assert snappy.decode_frames(stream) == b""


# Each rejected stream and the fault that rejects it.
BAD_STREAMS = [
    # No bytes at all.
    (b"", "missingStreamIdentifier"),
    # An uncompressed chunk first, without the stream identifier.
    (FRAMED_DIGITS[10:], "missingStreamIdentifier"),
    # A stream identifier chunk that holds sNaPpX.
    (bytes.fromhex("ff060000734e61507058"), "badStreamIdentifier"),
    # A stream that ends after two bytes of a chunk header.
    (STREAM_IDENTIFIER + bytes.fromhex("010d"), "headerTruncated"),
    # A chunk that declares 13 bytes, with 12 left.
    (FRAMED_DIGITS[:-1], "chunkPastEnd"),
    # An uncompressed chunk of three bytes, too short for its checksum.
    (STREAM_IDENTIFIER + bytes.fromhex("01030000000000"), "checksumTruncated"),
    # The digits chunk with its last checksum byte changed from c7 to c6.
    (
        FRAMED_DIGITS[:17] + b"\xc6" + FRAMED_DIGITS[18:],
        f"checksumMismatch {0xC68AB0E5} {0xC78AB0E5}",
    ),
    # A compressed chunk whose block declares 65537 bytes.
    (STREAM_IDENTIFIER + bytes.fromhex("0007000000000000818004"), "chunkTooLarge 65537"),
    # A compressed chunk whose block starts with a copy.
    (
        STREAM_IDENTIFIER + bytes.fromhex("0007000000000000040101"),
        "block (EthLib.Networking.Snappy.SnappyError.copyOffsetTooLarge 1)",
    ),
    # A chunk of type 0x02, the first reserved unskippable type.
    (STREAM_IDENTIFIER + bytes.fromhex("02000000"), "reservedUnskippable 2"),
]


@pytest.mark.parametrize(("stream", "fault"), BAD_STREAMS)
def test_decode_frames_rejected(stream: bytes, fault: str) -> None:
    with raises(ValueError, "stream rejected: EthLib.Networking.Snappy.FrameError." + fault):
        snappy.decode_frames(stream)
