"""QUIC integer encodings from RFC 9000 §16 and Appendix A.1."""

import pytest

from ethlib.networking import quic
from raising import raises


@pytest.mark.parametrize(
    ("value", "encoded"),
    [
        (37, "25"),
        (15293, "7bbd"),
        (494878333, "9d7f3e7d"),
        (151288809941952652, "c2197c5eff14e88c"),
        # Table 4 gives the bounds of each encoding width.
        (0, "00"),
        (63, "3f"),
        (64, "4040"),
        (16383, "7fff"),
        (16384, "80004000"),
        (2**30 - 1, "bfffffff"),
        (2**30, "c000000040000000"),
        (2**62 - 1, "ffffffffffffffff"),
    ],
)
def test_encodings(value: int, encoded: str) -> None:
    expected = bytes.fromhex(encoded)
    assert quic.encode_varint(value) == expected
    assert quic.decode_varint(expected + b"tail") == (value, b"tail")


@pytest.mark.parametrize("encoded", ["4025", "80000025", "c000000000000025"])
def test_longer_forms(encoded: str) -> None:
    # RFC 9000 §16 permits non-minimal forms except for frame types (§12.4).
    assert quic.decode_varint(bytes.fromhex(encoded)) == (37, b"")


@pytest.mark.parametrize("encoded", ["00", "4000", "80000000", "c000000000000000"])
def test_every_truncation(encoded: str) -> None:
    data = bytes.fromhex(encoded)
    for length in range(len(data)):
        with raises(
            quic.QuicVarIntError,
            "QUIC integer rejected: EthLib.Networking.Quic.VarInt.Error.truncated",
        ):
            quic.decode_varint(data[:length])


def test_reject_overflow() -> None:
    with raises(quic.QuicVarIntError, "QUIC integer too large"):
        quic.encode_varint(2**62)
