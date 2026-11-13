"""QUIC integers against RFC 9000 Appendix A.1, the bounds of Table 4 and hand-built edges."""

import pytest

from ethlib.networking import quic
from raising import raises

# The four shortest encodings of RFC 9000 Appendix A.1.
RFC_EXAMPLES = [
    (37, "25"),
    (15293, "7bbd"),
    (494878333, "9d7f3e7d"),
    (151288809941952652, "c2197c5eff14e88c"),
]

# The first and last value of each width of RFC 9000 §16, Table 4.
EDGES = [
    (0, "00"),
    (63, "3f"),
    (64, "4040"),
    (16383, "7fff"),
    (16384, "80004000"),
    (2**30 - 1, "bfffffff"),
    (2**30, "c000000040000000"),
    (2**62 - 1, "ffffffffffffffff"),
]


@pytest.mark.parametrize(("value", "encoded"), RFC_EXAMPLES + EDGES)
def test_encode(value: int, encoded: str) -> None:
    assert quic.encode_varint(value) == bytes.fromhex(encoded)


@pytest.mark.parametrize(("value", "encoded"), RFC_EXAMPLES + EDGES)
def test_decode_returns_the_bytes_after_the_integer(value: int, encoded: str) -> None:
    assert quic.decode_varint(bytes.fromhex(encoded) + b"tail") == (value, b"tail")


# RFC 9000 §16 permits longer forms except for frame types (§12.4).
# 4025 is from Appendix A.1; the four- and eight-byte forms are hand-built.
@pytest.mark.parametrize("encoded", ["4025", "80000025", "c000000000000025"])
def test_decode_accepts_longer_forms(encoded: str) -> None:
    assert quic.decode_varint(bytes.fromhex(encoded)) == (37, b"")


@pytest.mark.parametrize(
    ("encoded", "length"),
    [
        (encoded, length)
        for encoded in ["00", "4000", "80000000", "c000000000000000"]
        for length in range(len(encoded) // 2)
    ],
)
def test_decode_rejects_every_truncation(encoded: str, length: int) -> None:
    message = "QUIC integer rejected: EthLib.Networking.Quic.Varint.VarintError.truncated"
    with raises(quic.QuicVarintError, message) as info:
        quic.decode_varint(bytes.fromhex(encoded)[:length])
    assert info.value.code == 1


def test_encode_refuses_2_to_the_62() -> None:
    with raises(quic.QuicVarintError, "value must be below 2^62") as info:
        quic.encode_varint(2**62)
    assert info.value.code == 0


def test_encode_refuses_a_negative_value_before_lean() -> None:
    with raises(ValueError, "cannot pass a negative int to Lean"):
        quic.encode_varint(-1)
