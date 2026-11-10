"""multistream-select messages against the hex examples of their source and hand-built faults."""

import pytest

from ethlib.networking.libp2p import multistream
from raising import raises

# The examples are from the README of multiformats/multistream-select.
# The pinned commit is 9a1fbe8edadebea223f47102f1913b8026c23a1c.
# `na` is in "Protocol", and `ls` in "Listing".
# The protocol ID is built by hand: 19 bytes in all, 0x13, with the newline.
CASES = [
    (b"na", "036e610a"),
    # The empty message is the newline alone.
    (b"", "010a"),
    # A message of 127 bytes has length 128, the first of two bytes.
    (b"a" * 127, "8001" + "61" * 127 + "0a"),
    (b"ls", "036c730a"),
    (b"/multistream/1.0.0", "132f6d756c746973747265616d2f312e302e300a"),
]


@pytest.mark.parametrize(("message", "encoded"), CASES)
def test_encode(message: bytes, encoded: str) -> None:
    assert multistream.encode(message) == bytes.fromhex(encoded)


@pytest.mark.parametrize(("message", "encoded"), CASES)
def test_decode_returns_the_bytes_after_the_message(message: bytes, encoded: str) -> None:
    assert multistream.decode(bytes.fromhex(encoded) + b"next") == (message, b"next")


def test_a_message_need_not_be_text() -> None:
    # The framing reads any bytes, such as an invalid UTF-8 byte or a newline inside.
    message = b"\xff\n\x00"
    assert multistream.encode(message) == bytes.fromhex("04ff0a000a")
    assert multistream.decode(bytes.fromhex("04ff0a000a")) == (message, b"")


PREFIX = "multistream message rejected: EthLib.Networking.Libp2p.Multistream.MultistreamError."


@pytest.mark.parametrize(
    ("data", "fault", "code"),
    [
        # No length at all.
        (
            "",
            "length\n  (EthLib.Networking.Encoding.Uvarint.UvarintError.varint "
            "(EthLib.Networking.Encoding.Varint.VarintError.unterminated))",
            1,
        ),
        # A length of zero leaves no room for the newline.
        ("00", "empty", 2),
        # The length counts three bytes, and two follow.
        ("036e61", "truncated 3 2", 3),
        # The last counted byte is not a newline.
        ("036e6161", "missingNewline", 4),
    ],
)
def test_decode_rejected(data: str, fault: str, code: int) -> None:
    with raises(multistream.MultistreamError, PREFIX + fault) as info:
        multistream.decode(bytes.fromhex(data))
    assert info.value.code == code
