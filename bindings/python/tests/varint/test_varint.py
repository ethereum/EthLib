"""The unsigned protobuf varint against hand-built cases and the protobuf encoding guide."""

import pytest

from ethlib.networking import varint
from raising import raises

# Each value and its varint.
# 150 is the worked example of the protobuf encoding guide, and 300 is traced in the Lean module.
# 0, 1, 127 = 2^7 - 1 and 128 = 2^7 are the edges of one and two bytes.
# The largest 64-bit value needs all ten bytes.
CASES = [
    (150, "9601"),
    (0, "00"),
    (1, "01"),
    (127, "7f"),
    (128, "8001"),
    (300, "ac02"),
    (2**64 - 1, "ffffffffffffffffff01"),
]


@pytest.mark.parametrize(("value", "encoded"), CASES)
def test_encode(value: int, encoded: str) -> None:
    assert varint.encode(value) == bytes.fromhex(encoded)


@pytest.mark.parametrize(("value", "encoded"), CASES)
def test_decode(value: int, encoded: str) -> None:
    assert varint.decode(bytes.fromhex(encoded)) == value


@pytest.mark.parametrize(
    ("data", "fault"),
    [
        # Eleven bytes exceed the cap.
        (bytes.fromhex("ffffffffffffffffffff01"), "tooLong"),
        # A megabyte of continuation bytes is rejected at byte eleven.
        (b"\x80" * 1048576 + b"\x01", "tooLong"),
        # 2^64 is one past the range, and still fits in ten bytes.
        (bytes.fromhex("80808080808080808002"), "overflow"),
        # 80 00 is zero padded with an extra zero group.
        (bytes.fromhex("8000"), "nonMinimal"),
        # A continuation bit with nothing after it.
        (bytes.fromhex("80"), "unterminated"),
        # No bytes at all.
        (b"", "unterminated"),
        # A last byte followed by more bytes.
        (bytes.fromhex("0000"), "trailingBytes"),
    ],
)
def test_decode_rejected(data: bytes, fault: str) -> None:
    with raises(
        ValueError, "varint rejected: EthLib.Networking.Encoding.Varint.VarintError." + fault
    ):
        varint.decode(data)


def test_encode_out_of_range() -> None:
    with raises(OverflowError, "value must be in [0, 2^64)"):
        varint.encode(2**64)
