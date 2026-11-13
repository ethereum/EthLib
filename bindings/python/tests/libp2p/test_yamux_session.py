"""The yamux streams of one side, with frames built by hand from the rules of their source."""

import pytest

from ethlib.networking.libp2p import yamux
from raising import raises

# The rules come from "Message Flow" and "Flag Field" of yamux/README.md.
# Repository: libp2p/specs.
# Commit: c750236de43cd8b246a824b377dfdb26bae686db.
# The source publishes no vector.
#
# A header is version 0, type, flags, stream ID and length, big-endian on 1, 1, 2, 4 and 4 bytes.
DATA, WINDOW_UPDATE, PING, GO_AWAY = 0, 1, 2, 3
SYN, ACK, FIN, RST = 0x1, 0x2, 0x4, 0x8
WINDOW = 256 * 1024

# Each event says whether this side receives its bytes.
RECEIVED = True
SENT = False

# The first argument of a session says whether this side is the client.
CLIENT = True
SERVER = False


def frame(kind: int, flags: int, stream_id: int, length: int, data: bytes = b"") -> bytes:
    """The bytes of one frame, written field by field from the header layout."""
    return (
        bytes([0, kind])
        + flags.to_bytes(2, "big")
        + stream_id.to_bytes(4, "big")
        + length.to_bytes(4, "big")
        + data
    )


def flip(events: list[tuple[bool, bytes]]) -> list[tuple[bool, bytes]]:
    """The same events as the other side sees them."""
    return [(not received, data) for received, data in events]


OPEN_1 = frame(WINDOW_UPDATE, SYN, 1, 0)
HELLO = frame(DATA, 0, 1, 5, b"hello")
ACK_5 = frame(WINDOW_UPDATE, ACK, 1, 5)
FIN_1 = frame(DATA, FIN, 1, 0)
RST_1 = frame(DATA, RST, 1, 0)


def test_header_layout_matches_the_hand_written_bytes() -> None:
    assert OPEN_1 == bytes.fromhex("000100010000000100000000")
    assert ACK_5 == bytes.fromhex("000100020000000100000005")


# The client opens stream 1 and sends 5 bytes; the server acknowledges them, then both close.
OPENED = [(SENT, OPEN_1), (SENT, HELLO)]
EXCHANGE = [*OPENED, (RECEIVED, ACK_5), (SENT, FIN_1), (RECEIVED, FIN_1)]


def test_data_may_follow_syn_before_the_ack() -> None:
    assert yamux.session(CLIENT, OPENED) == ([(1, "syn_sent", WINDOW - 5, WINDOW)], False, [])
    assert yamux.session(SERVER, flip(OPENED)) == (
        [(1, "syn_received", WINDOW, WINDOW - 5)],
        False,
        [],
    )


def test_ack_with_a_window_update_restores_the_window() -> None:
    events = EXCHANGE[:3]
    assert yamux.session(CLIENT, events) == ([(1, "established", WINDOW, WINDOW)], False, [])
    assert yamux.session(SERVER, flip(events)) == (
        [(1, "established", WINDOW, WINDOW)],
        False,
        [],
    )


def test_fin_half_closes_one_direction() -> None:
    events = EXCHANGE[:4]
    assert yamux.session(CLIENT, events)[0] == [(1, "local_closed", WINDOW, WINDOW)]
    assert yamux.session(SERVER, flip(events))[0] == [(1, "remote_closed", WINDOW, WINDOW)]


def test_stream_is_closed_once_both_sides_sent_fin() -> None:
    assert yamux.session(CLIENT, EXCHANGE)[0] == [(1, "closed", WINDOW, WINDOW)]
    assert yamux.session(SERVER, flip(EXCHANGE))[0] == [(1, "closed", WINDOW, WINDOW)]


def test_window_update_after_this_side_sent_fin_is_accepted() -> None:
    events = [*EXCHANGE[:4], (RECEIVED, frame(WINDOW_UPDATE, 0, 1, 100))]
    assert yamux.session(CLIENT, events)[0] == [(1, "local_closed", WINDOW + 100, WINDOW)]


def test_a_reset_rejects_the_stream() -> None:
    events = [*OPENED, (RECEIVED, RST_1)]
    assert yamux.session(CLIENT, events)[0] == [(1, "reset", WINDOW - 5, WINDOW)]


def test_frames_in_flight_after_this_side_reset_are_dropped() -> None:
    events = [*flip(OPENED), (SENT, RST_1), (RECEIVED, HELLO), (RECEIVED, FIN_1)]
    assert yamux.session(SERVER, events)[0] == [(1, "reset", WINDOW, WINDOW - 5)]


def test_after_this_side_reset_even_the_peer_reset_is_dropped() -> None:
    events = [*flip(OPENED), (SENT, RST_1), (RECEIVED, RST_1), (RECEIVED, HELLO)]
    assert yamux.session(SERVER, events)[0] == [(1, "reset", WINDOW, WINDOW - 5)]


def test_both_sides_open_streams_of_their_own_parity() -> None:
    open_2 = frame(WINDOW_UPDATE, SYN, 2, 0)
    events = [
        (SENT, OPEN_1),
        (RECEIVED, open_2),
        (RECEIVED, frame(DATA, 0, 2, 3, b"abc")),
        (SENT, HELLO),
    ]
    assert yamux.session(CLIENT, events)[0] == [
        (1, "syn_sent", WINDOW - 5, WINDOW),
        (2, "syn_received", WINDOW, WINDOW - 3),
    ]


def test_data_that_fills_the_window_is_accepted() -> None:
    events = [(RECEIVED, OPEN_1), (RECEIVED, frame(DATA, 0, 1, WINDOW, bytes(WINDOW)))]
    assert yamux.session(SERVER, events)[0] == [(1, "syn_received", WINDOW, 0)]


def test_empty_data_after_fin_is_accepted() -> None:
    events = [*OPENED, (SENT, FIN_1), (SENT, frame(DATA, 0, 1, 0))]
    assert yamux.session(CLIENT, events)[0] == [(1, "local_closed", WINDOW - 5, WINDOW)]


def test_replies_follow_the_pings_in_order_on_stream_0() -> None:
    events = [(RECEIVED, frame(PING, SYN | ACK, 0, 1)), (RECEIVED, frame(PING, SYN, 3, 2))]
    assert yamux.session(CLIENT, events) == (
        [],
        False,
        [frame(PING, ACK, 0, 1), frame(PING, ACK, 0, 2)],
    )


def test_a_ping_with_syn_is_echoed_with_ack() -> None:
    events = [(RECEIVED, frame(PING, SYN, 0, 0xDEADBEEF))]
    assert yamux.session(CLIENT, events) == ([], False, [frame(PING, ACK, 0, 0xDEADBEEF)])


def test_a_ping_with_ack_gets_no_reply() -> None:
    assert yamux.session(CLIENT, [(RECEIVED, frame(PING, ACK, 0, 7))]) == ([], False, [])


def test_a_sent_ping_gets_no_reply() -> None:
    assert yamux.session(CLIENT, [(SENT, frame(PING, SYN, 0, 7))]) == ([], False, [])


def test_go_away_marks_the_session() -> None:
    assert yamux.session(SERVER, [(RECEIVED, frame(GO_AWAY, 0, 0, 0))]) == ([], True, [])
    assert yamux.session(SERVER, [(SENT, frame(GO_AWAY, 0, 0, 0))]) == ([], False, [])


def test_several_frames_in_one_event() -> None:
    assert yamux.session(SERVER, [(RECEIVED, OPEN_1 + HELLO + FIN_1)])[0] == [
        (1, "remote_closed", WINDOW, WINDOW - 5)
    ]


def test_no_event_leaves_no_stream() -> None:
    assert yamux.session(CLIENT, ()) == ([], False, [])


@pytest.mark.parametrize(
    ("is_client", "events", "message", "code"),
    [
        (
            CLIENT,
            [(SENT, frame(DATA, 0, 0, 0))],
            "event 0: data or window update on stream 0, which names the session",
            101,
        ),
        # The server opens even IDs, so it refuses an even ID from the client.
        (
            SERVER,
            [(RECEIVED, frame(WINDOW_UPDATE, SYN, 2, 0))],
            "event 0: stream 2 has the parity of the other side",
            102,
        ),
        (
            CLIENT,
            [(SENT, frame(WINDOW_UPDATE, SYN, 2, 0))],
            "event 0: stream 2 has the parity of the other side",
            102,
        ),
        (CLIENT, [(SENT, OPEN_1), (SENT, OPEN_1)], "event 1: stream 1 was opened before", 103),
        # A reset stream keeps its ID, even after this side reset it.
        (
            SERVER,
            [*flip(OPENED), (SENT, RST_1), (RECEIVED, OPEN_1)],
            "event 3: stream 1 was opened before",
            103,
        ),
        (CLIENT, [(SENT, HELLO)], "event 0: stream 1 is unknown", 104),
        # The ACK must come from the side that did not open the stream, and only once.
        (CLIENT, [(SENT, OPEN_1), (SENT, ACK_5)], "event 1: unexpected ACK on stream 1", 105),
        (
            CLIENT,
            [(SENT, OPEN_1), (RECEIVED, ACK_5), (RECEIVED, ACK_5)],
            "event 2: unexpected ACK on stream 1",
            105,
        ),
        (
            CLIENT,
            [*OPENED, (RECEIVED, RST_1), (RECEIVED, ACK_5)],
            "event 3: frame on stream 1 after its reset",
            106,
        ),
        (
            CLIENT,
            [*OPENED, (RECEIVED, RST_1), (SENT, HELLO)],
            "event 3: frame on stream 1 after its reset",
            106,
        ),
        (
            CLIENT,
            [*OPENED, (SENT, RST_1), (SENT, RST_1)],
            "event 3: frame on stream 1 after its reset",
            106,
        ),
        (
            CLIENT,
            [*OPENED, (SENT, FIN_1), (SENT, HELLO)],
            "event 3: data or FIN on stream 1 after its writer's FIN",
            107,
        ),
        (
            SERVER,
            [*flip(OPENED), (RECEIVED, FIN_1), (RECEIVED, FIN_1)],
            "event 3: data or FIN on stream 1 after its writer's FIN",
            107,
        ),
        (
            SERVER,
            [(RECEIVED, OPEN_1), (RECEIVED, frame(DATA, 0, 1, WINDOW + 1, bytes(WINDOW + 1)))],
            f"event 1: data of {WINDOW + 1} bytes on stream 1 exceeds its window of {WINDOW}",
            108,
        ),
        (
            CLIENT,
            [*OPENED, (SENT, frame(DATA, 0, 1, WINDOW, bytes(WINDOW)))],
            f"event 2: data of {WINDOW} bytes on stream 1 exceeds its window of {WINDOW - 5}",
            108,
        ),
        # Until it sends ACK, the side that did not open the stream must carry ACK or RST.
        (
            CLIENT,
            [*OPENED, (RECEIVED, FIN_1)],
            "event 2: frame on stream 1 without ACK or RST before its ACK",
            109,
        ),
        (
            SERVER,
            [*flip(OPENED), (SENT, frame(WINDOW_UPDATE, 0, 1, 5))],
            "event 2: frame on stream 1 without ACK or RST before its ACK",
            109,
        ),
    ],
)
def test_a_refused_frame_raises_its_error(
    is_client: bool, events: list[tuple[bool, bytes]], message: str, code: int
) -> None:
    with raises(yamux.YamuxError, message) as info:
        yamux.session(is_client, events)
    assert info.value.code == code


@pytest.mark.parametrize(
    ("data", "message", "code"),
    [
        (bytes([1]) + OPEN_1[1:], "version 1", 2),
        # The second frame of the event ends within its header.
        (OPEN_1 + HELLO[:7], "shortHeader 7", 1),
        # The second frame of the event ends within its data.
        (OPEN_1 + HELLO[:14], "truncated 5 2", 4),
    ],
)
def test_a_frame_that_does_not_decode_is_refused(data: bytes, message: str, code: int) -> None:
    prefix = "event 1: yamux frame rejected: EthLib.Networking.Libp2p.Yamux.YamuxError."
    with raises(yamux.YamuxError, prefix + message) as info:
        yamux.session(CLIENT, [(SENT, b""), (RECEIVED, data)])
    assert info.value.code == code
