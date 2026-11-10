"""The multiformats unsigned varint against the examples of its source and hand-built edges."""

import pytest

from ethlib.networking import uvarint
from raising import raises

# The examples are from "Spec" in the README of multiformats/unsigned-varint.
# The pinned commit is dd184f1ce89c81808503bb719b5fcb13844d08f3.
SOURCE_EXAMPLES = [
    (1, "01"),
    (127, "7f"),
    (128, "8001"),
    (255, "ff01"),
    (300, "ac02"),
    (16384, "808001"),
]

# Zero is one byte, and 2^63 - 1 is the largest value of nine bytes.
EDGES = [
    (0, "00"),
    (2**63 - 1, "ffffffffffffffff7f"),
]


@pytest.mark.parametrize(("value", "encoded"), SOURCE_EXAMPLES + EDGES)
def test_encode(value: int, encoded: str) -> None:
    assert uvarint.encode(value) == bytes.fromhex(encoded)


@pytest.mark.parametrize(("value", "encoded"), SOURCE_EXAMPLES + EDGES)
def test_decode_returns_the_bytes_after_the_varint(value: int, encoded: str) -> None:
    assert uvarint.decode(bytes.fromhex(encoded) + b"\xff\x00") == (value, b"\xff\x00")


def test_encode_refuses_a_value_of_ten_bytes() -> None:
    with raises(uvarint.UvarintError, "value must be below 2^63") as info:
        uvarint.encode(2**63)
    assert info.value.code == 0


PREFIX = "unsigned varint rejected: EthLib.Networking.Encoding."

# A prefix that is no minimal protobuf varint fails with the fault of the varint inside.
VARINT = "Uvarint.UvarintError.varint (EthLib.Networking.Encoding.Varint.VarintError.{})"


@pytest.mark.parametrize(
    ("data", "fault", "code"),
    [
        # 81 00 is the non-minimal encoding of 1, "Incompatibilities with Go varints".
        ("8100", VARINT.format("nonMinimal"), 1),
        # A continuation bit with nothing after it.
        ("80", VARINT.format("unterminated"), 1),
        # Nine bytes that all continue: the value would need a tenth.
        ("808080808080808080", VARINT.format("unterminated"), 1),
        # Eleven bytes, over the ten of a 64-bit varint.
        ("80" * 10 + "01", VARINT.format("tooLong"), 1),
        # 2^64 does not fit 64 bits.
        ("80" * 9 + "02", VARINT.format("overflow"), 1),
        # 2^63 is minimal in ten bytes, over the nine of "Practical maximum of 9 bytes".
        ("80808080808080808001", "Uvarint.UvarintError.tooLarge", 2),
        # 2^64 - 1 is the largest value of ten bytes.
        ("ff" * 9 + "01", "Uvarint.UvarintError.tooLarge", 2),
    ],
)
def test_decode_rejected(data: str, fault: str, code: int) -> None:
    with raises(uvarint.UvarintError, PREFIX + fault) as info:
        uvarint.decode(bytes.fromhex(data))
    assert info.value.code == code


def test_encode_refuses_a_negative_value_before_lean() -> None:
    # The converter refuses a negative int with a plain ValueError, before any codec runs.
    with raises(ValueError, "cannot pass a negative int to Lean"):
        uvarint.encode(-1)
