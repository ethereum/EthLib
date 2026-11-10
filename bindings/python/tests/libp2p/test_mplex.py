"""mplex frames built by hand from the message format of their source."""

import pytest

from ethlib.networking.libp2p import mplex
from raising import raises

# The format is mplex/README.md of libp2p/specs at commit c750236de43cd8b246a824b377dfdb26bae686db.
# Its sections are "Message format", "Flag Values" and "Writing to a stream".
# The rules for an end of stream are in "Closing a stream" and "Resetting a stream".
# The header is the unsigned varint of 8 * stream ID + flag; the length and the data follow.
CASES = [
    # Stream 17 opens with the name "a": header 136 = 88 01, length 01.
    (mplex.Frame(stream_id=17, flag=mplex.Flag.NEW_STREAM, data=b"a"), "88010161"),
    # Stream 1 carries "hi" from the peer that opened it: header 10 = 0a.
    (mplex.Frame(stream_id=1, flag=mplex.Flag.MESSAGE_INITIATOR, data=b"hi"), "0a026869"),
    # The receiver of stream 1 answers: header 9 = 09.
    (mplex.Frame(stream_id=1, flag=mplex.Flag.MESSAGE_RECEIVER, data=b"hi"), "09026869"),
    # Closes and resets of stream 0 carry no data: headers 3 to 6.
    (mplex.Frame(stream_id=0, flag=mplex.Flag.CLOSE_RECEIVER), "0300"),
    (mplex.Frame(stream_id=0, flag=mplex.Flag.CLOSE_INITIATOR), "0400"),
    (mplex.Frame(stream_id=0, flag=mplex.Flag.RESET_RECEIVER), "0500"),
    (mplex.Frame(stream_id=0, flag=mplex.Flag.RESET_INITIATOR), "0600"),
    # The largest stream ID, 2^60 - 1, fills the nine bytes of a header with flag 0.
    (mplex.Frame(stream_id=2**60 - 1, flag=mplex.Flag.NEW_STREAM), "f8ffffffffffffff7f00"),
]


@pytest.mark.parametrize(("frame", "encoded"), CASES)
def test_encode(frame: mplex.Frame, encoded: str) -> None:
    assert mplex.encode(frame) == bytes.fromhex(encoded)


@pytest.mark.parametrize(("frame", "encoded"), CASES)
def test_decode_returns_the_bytes_after_the_frame(frame: mplex.Frame, encoded: str) -> None:
    assert mplex.decode(bytes.fromhex(encoded) + b"\x00") == (frame, b"\x00")


def test_data_of_one_mebibyte() -> None:
    # EthLib applies the 1 MiB write limit of "Writing to a stream" to every frame.
    # A frame of exactly 1 MiB has length 2^20 = 80 80 40.
    frame = mplex.Frame(stream_id=2, flag=mplex.Flag.MESSAGE_RECEIVER, data=b"\x01" * 2**20)
    encoded = mplex.encode(frame)
    assert len(encoded) == 4 + 2**20
    assert encoded[:4] == bytes.fromhex("11808040")
    assert mplex.decode(encoded) == (frame, b"")


ENCODE_REFUSAL = (
    "frame must have a stream ID below 2^60, at most 1 MiB of data, "
    "and no data on a close or a reset"
)


@pytest.mark.parametrize(
    "frame",
    [
        mplex.Frame(stream_id=2**60, flag=mplex.Flag.NEW_STREAM),
        mplex.Frame(stream_id=1, flag=mplex.Flag.MESSAGE_INITIATOR, data=bytes(2**20 + 1)),
        mplex.Frame(stream_id=1, flag=mplex.Flag.CLOSE_INITIATOR, data=b"x"),
        mplex.Frame(stream_id=1, flag=mplex.Flag.RESET_RECEIVER, data=b"x"),
        mplex.Frame(stream_id=1, flag=mplex.Flag.CLOSE_RECEIVER, data=b"x"),
        mplex.Frame(stream_id=1, flag=mplex.Flag.RESET_INITIATOR, data=b"x"),
    ],
)
def test_encode_refuses_a_frame_outside_the_format(frame: mplex.Frame) -> None:
    with raises(mplex.MplexError, ENCODE_REFUSAL) as info:
        mplex.encode(frame)
    assert info.value.code == 0


PREFIX = "mplex frame rejected: EthLib.Networking.Libp2p.Mplex.MplexError."


@pytest.mark.parametrize(
    ("data", "fault", "code"),
    [
        # No header at all.
        (
            "",
            "header\n  (EthLib.Networking.Encoding.Uvarint.UvarintError.varint "
            "(EthLib.Networking.Encoding.Varint.VarintError.unterminated))",
            1,
        ),
        # Flag 7 names no frame.
        ("0700", "unknownFlag", 2),
        # A header and no length.
        (
            "0a",
            "length\n  (EthLib.Networking.Encoding.Uvarint.UvarintError.varint "
            "(EthLib.Networking.Encoding.Varint.VarintError.unterminated))",
            3,
        ),
        # A length of 2^20 + 1 = 81 80 40, one byte over 1 MiB, before any data.
        ("0a818040", "tooLong 1048577", 4),
        # A close or a reset of stream 0 that declares one byte.
        ("030161", "dataOnEnd 1", 5),
        ("040161", "dataOnEnd 1", 5),
        ("050161", "dataOnEnd 1", 5),
        ("060161", "dataOnEnd 1", 5),
        # The length is checked before the data is read.
        ("0301", "dataOnEnd 1", 5),
        # A length of exactly 1 MiB is accepted, and then the data is missing.
        ("0a808040", "truncated 1048576 0", 6),
        # Two bytes declared, one present.
        ("0a0268", "truncated 2 1", 6),
    ],
)
def test_decode_rejected(data: str, fault: str, code: int) -> None:
    with raises(mplex.MplexError, PREFIX + fault) as info:
        mplex.decode(bytes.fromhex(data))
    assert info.value.code == code


def test_encode_refuses_a_negative_stream_id_before_lean() -> None:
    # The converter refuses a negative int with a plain ValueError, before any codec runs.
    with raises(ValueError, "cannot pass a negative int to Lean"):
        mplex.encode(mplex.Frame(stream_id=-1, flag=mplex.Flag.NEW_STREAM))
