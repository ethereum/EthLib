"""The session of an RLPx connection, with frames built from the rules of rlpx.md."""

import pytest

from ethlib.networking import devp2p, snappy
from ethlib.serialization import rlp
from raising import raises

# No official vector exists for sessions.
# The frames follow these sections of rlpx.md: "p2p" Capability and Hello (0x00).
# They also follow Message Encoding and Message ID-based Multiplexing.
#
# File: rlpx.md
# Repository: ethereum/devp2p
# Commit: 88f1c80800d622cc3a542a2125bbe33cc18c9f9c

NODE_ID = bytes(range(64))

# The data of a Ping or a Pong, the empty RLP list.
EMPTY = b"\xc0"


def _int(n: int) -> bytes:
    """An integer as RLP reads it: big-endian, without leading zero bytes."""
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _id(message_id: int) -> bytes:
    """The RLP encoding of a message ID."""
    return rlp.encode(_int(message_id))


def _hello(capabilities: list[tuple[bytes, int]], version: int = 5) -> bytes:
    """The uncompressed frame data of a Hello: the ID 0x00, then its RLP list."""
    listed = [[name, _int(number)] for name, number in capabilities]
    return _id(0) + rlp.encode([_int(version), b"client", listed, _int(0), NODE_ID])


OURS = _hello([(b"eth", 68), (b"eth", 69), (b"snap", 1)])
THEIRS = _hello([(b"eth", 69), (b"snap", 1)])
SHARED_OURS = [(b"eth", 68), (b"eth", 69), (b"snap", 1)]
SHARED_THEIRS = [(b"eth", 69), (b"snap", 1)]

# A Ping after Hello, compressed: the ID 2, then the Snappy block of c0.
# The block is the length 1, then one literal of one byte with the tag 00.
PING = bytes.fromhex("020100c0")


def _frame(message_id: int, data: bytes) -> bytes:
    """The frame data of a message after Hello, with Snappy on: the ID, then the compressed data."""
    return _id(message_id) + snappy.compress(data)


def _disconnect(reason: int, compressed: bool) -> bytes:
    """The frame data of a Disconnect with a reason, compressed or not."""
    plain = _id(1) + rlp.encode([_int(reason)])
    return devp2p.encode_message(compressed, plain)


def test_ping_frame() -> None:
    assert devp2p.encode_message(True, _id(2) + EMPTY) == PING


@pytest.mark.parametrize(
    ("message_id", "expected"),
    [
        # eth/69 takes 0x12 IDs, from 0x10 to 0x21.
        (0x10, (b"eth", 69, 0x00)),
        (0x21, (b"eth", 69, 0x11)),
        # snap/1 takes 0x08 IDs, from 0x22 to 0x29.
        (0x22, (b"snap", 1, 0x00)),
        (0x23, (b"snap", 1, 0x01)),
        (0x29, (b"snap", 1, 0x07)),
        (0x2A, None),
        (0x0F, None),
        (0x02, None),
    ],
)
def test_route(message_id: int, expected: tuple[bytes, int, int] | None) -> None:
    assert devp2p.route(SHARED_OURS, SHARED_THEIRS, message_id) == expected
    # Both peers read every ID the same way.
    assert devp2p.route(SHARED_THEIRS, SHARED_OURS, message_id) == expected


def test_hello_ping_and_capability() -> None:
    account_range = rlp.encode([_int(7), [], []])
    outcomes = devp2p.session(OURS, [THEIRS, PING, _frame(0x23, account_range)])
    assert outcomes == [
        ("active", "p2p", b"", 0, 0x00, THEIRS[1:], False),
        ("active", "p2p", b"", 0, 0x02, EMPTY, True),
        ("active", "capability", b"snap", 1, 0x01, account_range, False),
    ]


def test_pong_needs_no_answer() -> None:
    pong = devp2p.encode_message(True, _id(3) + EMPTY)
    assert devp2p.session(OURS, [THEIRS, pong])[1] == ("active", "p2p", b"", 0, 0x03, EMPTY, False)


def test_disconnect_closes() -> None:
    outcomes = devp2p.session(OURS, [THEIRS, _disconnect(0x04, True)])
    assert outcomes[1] == ("closed", "p2p", b"", 0, 0x01, rlp.encode([_int(0x04)]), False)


def test_disconnect_before_hello() -> None:
    # A Disconnect before Hello is read uncompressed, as Hello is.
    outcomes = devp2p.session(OURS, [_disconnect(0x10, False)])
    assert outcomes == [("closed", "p2p", b"", 0, 0x01, rlp.encode([_int(0x10)]), False)]


def test_unknown_version_is_accepted() -> None:
    """A Hello of another version opens the session, without Snappy below version 5."""
    old = _hello([(b"eth", 69)], version=4)
    outcomes = devp2p.session(OURS, [old, _id(2) + EMPTY])
    assert outcomes[1] == ("active", "p2p", b"", 0, 0x02, EMPTY, True)


def test_before_hello() -> None:
    with raises(devp2p.Devp2pError, "frame 0: message ID 2 came before the peer's Hello") as error:
        devp2p.session(OURS, [PING])
    assert error.value.code == 1


def test_capability_before_hello() -> None:
    with raises(devp2p.Devp2pError, "frame 0: message ID 35 came before the peer's Hello"):
        devp2p.session(OURS, [_frame(0x23, rlp.encode([_int(7), [], []]))])


def test_second_hello() -> None:
    with raises(devp2p.Devp2pError, "frame 1: a second Hello came in an active session") as error:
        devp2p.session(OURS, [THEIRS, THEIRS])
    assert error.value.code == 2


@pytest.mark.parametrize("message_id", [0x04, 0x0F, 0x2A])
def test_unknown_id(message_id: int) -> None:
    message = f"frame 1: message ID {message_id} belongs to no shared capability"
    with raises(devp2p.Devp2pError, message) as error:
        devp2p.session(OURS, [THEIRS, _frame(message_id, EMPTY)])
    assert error.value.code == 3


def test_too_large_uncompressed() -> None:
    """Without Snappy, capability data above 16 MiB is rejected."""
    old = _hello([(b"eth", 69)], version=4)
    frame = _id(0x10) + bytes(2**24 + 1)
    with raises(
        devp2p.Devp2pError, f"frame 1: message data has {2**24 + 1} bytes, more than {2**24}"
    ) as error:
        devp2p.session(OURS, [old, frame])
    assert error.value.code == 5


def test_too_large_compressed() -> None:
    """With Snappy, capability data whose header declares more than 16 MiB is rejected."""
    # The Snappy header is the varint of 2^24 + 1, with no data after it.
    header = bytes([0x81, 0x80, 0x80, 0x08])
    with raises(
        devp2p.Devp2pError, f"frame 1: message decompresses to {2**24 + 1} bytes, more than {2**24}"
    ) as error:
        devp2p.session(OURS, [THEIRS, _id(0x10) + header])
    assert error.value.code == 13


def test_closed() -> None:
    with raises(devp2p.Devp2pError, "frame 2: a frame came after a Disconnect") as error:
        devp2p.session(OURS, [THEIRS, _disconnect(0x00, True), PING])
    assert error.value.code == 4


def test_message_error() -> None:
    """A Ping that is not compressed after Hello does not decode, with the code of its error."""
    with raises(devp2p.Devp2pError, "frame 1: message is not a valid Snappy block") as error:
        devp2p.session(OURS, [THEIRS, _id(2) + EMPTY])
    assert error.value.code == 12


def test_our_hello_must_be_hello() -> None:
    with raises(devp2p.Devp2pError, "our Hello is another message") as error:
        devp2p.session(_id(2) + EMPTY, [])
    assert error.value.code == 0
