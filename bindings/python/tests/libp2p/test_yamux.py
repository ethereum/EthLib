"""yamux frames built by hand from the framing of their source."""

import pytest

from ethlib.networking.libp2p import yamux
from raising import raises

# The format is yamux/README.md of libp2p/specs at commit c750236de43cd8b246a824b377dfdb26bae686db.
# Its sections are "Framing" with its field sections, "Flow Control" and "Session termination".
# A header is version 0, the type, two bytes of flags, then the stream ID and the length in four.
# The flags are SYN 1, ACK 2, FIN 4 and RST 8.
CASES = [
    # Stream 1 opens with SYN and carries "hi".
    (
        yamux.Frame(kind=yamux.Kind.DATA, flags=1, stream_id=1, length=2, data=b"hi"),
        "0000000100000001000000026869",
    ),
    # The receiver acknowledges stream 1 with an empty data frame.
    (yamux.Frame(kind=yamux.Kind.DATA, flags=2, stream_id=1, length=0), "000000020000000100000000"),
    # A window update whose delta is 256 KiB = 0x40000, the initial window of "Flow Control".
    (
        yamux.Frame(kind=yamux.Kind.WINDOW_UPDATE, flags=0, stream_id=1, length=262144),
        "000100000000000100040000",
    ),
    # A ping on the session, stream 0, with an opaque value 7.
    (yamux.Frame(kind=yamux.Kind.PING, flags=1, stream_id=0, length=7), "000200010000000000000007"),
    # A go-away for a protocol error, code 1.
    (
        yamux.Frame(kind=yamux.Kind.GO_AWAY, flags=0, stream_id=0, length=1),
        "000300000000000000000001",
    ),
    # Every field at its largest, with all sixteen flag bits, of which the source defines four.
    (
        yamux.Frame(
            kind=yamux.Kind.WINDOW_UPDATE, flags=0xFFFF, stream_id=2**32 - 1, length=2**32 - 1
        ),
        "0001ffffffffffffffffffff",
    ),
]


@pytest.mark.parametrize(("frame", "encoded"), CASES)
def test_encode(frame: yamux.Frame, encoded: str) -> None:
    assert yamux.encode(frame) == bytes.fromhex(encoded)


@pytest.mark.parametrize(("frame", "encoded"), CASES)
def test_decode_returns_the_bytes_after_the_frame(frame: yamux.Frame, encoded: str) -> None:
    assert yamux.decode(bytes.fromhex(encoded) + b"\x00") == (frame, b"\x00")


@pytest.mark.parametrize(
    "frame",
    [
        # A data frame whose data is shorter than its length.
        yamux.Frame(kind=yamux.Kind.DATA, flags=0, stream_id=1, length=2, data=b"h"),
        # A data frame whose data is longer than its length.
        yamux.Frame(kind=yamux.Kind.DATA, flags=0, stream_id=1, length=1, data=b"hi"),
        # A ping or a window update that carries data.
        yamux.Frame(kind=yamux.Kind.PING, flags=0, stream_id=0, length=1, data=b"x"),
        yamux.Frame(kind=yamux.Kind.WINDOW_UPDATE, flags=0, stream_id=1, length=1, data=b"x"),
    ],
)
def test_encode_refuses_a_frame_outside_the_format(frame: yamux.Frame) -> None:
    with raises(
        yamux.YamuxError, "frame must carry as many bytes as its length for data, else none"
    ) as info:
        yamux.encode(frame)
    assert info.value.code == 0


@pytest.mark.parametrize(
    ("frame", "message"),
    [
        (
            yamux.Frame(kind=yamux.Kind.DATA, flags=2**16, stream_id=0, length=0),
            "flags: expected an int below 65536, got 65536",
        ),
        (
            yamux.Frame(kind=yamux.Kind.DATA, flags=0, stream_id=2**32, length=0),
            "stream_id: expected an int below 4294967296, got 4294967296",
        ),
        (
            yamux.Frame(kind=yamux.Kind.PING, flags=0, stream_id=0, length=2**32),
            "length: expected an int below 4294967296, got 4294967296",
        ),
    ],
)
def test_encode_refuses_a_field_out_of_range(frame: yamux.Frame, message: str) -> None:
    with raises(yamux.YamuxError, message) as info:
        yamux.encode(frame)
    assert info.value.code == 0


PREFIX = "yamux frame rejected: EthLib.Networking.Libp2p.Yamux.YamuxError."


@pytest.mark.parametrize(
    ("data", "fault", "code"),
    [
        # No header, and eleven bytes of a twelve-byte header.
        ("", "shortHeader 0", 1),
        ("0000000000000000000000", "shortHeader 11", 1),
        # Version 1.
        ("010000000000000000000000", "version 1", 2),
        # Type 4 names no frame.
        ("000400000000000000000000", "unknownKind 4", 3),
        # A data frame of length 2 with one byte.
        ("00000000000000010000000268", "truncated 2 1", 4),
    ],
)
def test_decode_rejected(data: str, fault: str, code: int) -> None:
    with raises(yamux.YamuxError, PREFIX + fault) as info:
        yamux.decode(bytes.fromhex(data))
    assert info.value.code == code


def test_encode_refuses_a_negative_field_before_lean() -> None:
    # The converter refuses a negative int with a plain ValueError, before any codec runs.
    with raises(ValueError, "cannot pass a negative int to Lean"):
        yamux.encode(yamux.Frame(kind=yamux.Kind.PING, flags=0, stream_id=0, length=-1))
