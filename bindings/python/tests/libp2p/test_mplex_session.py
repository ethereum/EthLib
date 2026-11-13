"""The mplex streams of one side, with frames built by hand from the rules of their source."""

import pytest

from ethlib.networking.libp2p import mplex
from raising import raises

# The rules come from "Protocol" of mplex/README.md.
# Repository: libp2p/specs.
# Commit: c750236de43cd8b246a824b377dfdb26bae686db.
#
# A header is the unsigned varint of 8 * stream ID + flag, then a length and the data.
#
# Each event says whether this side receives its bytes.
RECEIVED = True
SENT = False

OPEN_3 = bytes.fromhex("1800")  # NewStream on stream 3, empty name.
HI = bytes.fromhex("1a026869")  # MessageInitiator "hi" on stream 3.
OK = bytes.fromhex("19026f6b")  # MessageReceiver "ok" on stream 3.
CLOSE_INITIATOR = bytes.fromhex("1c00")  # CloseInitiator on stream 3.
CLOSE_RECEIVER = bytes.fromhex("1b00")  # CloseReceiver on stream 3.
RESET_RECEIVER = bytes.fromhex("1d00")  # ResetReceiver on stream 3.
RESET_INITIATOR = bytes.fromhex("1e00")  # ResetInitiator on stream 3.
BANG = bytes.fromhex("1a0121")  # MessageInitiator "!" on stream 3.


def flip(events: list[tuple[bool, bytes]]) -> list[tuple[bool, bytes]]:
    """The same events as the other side sees them."""
    return [(not received, data) for received, data in events]


# The peer opens stream 3, writes "hi", gets "ok", then closes its side.
EXCHANGE = [(RECEIVED, OPEN_3), (RECEIVED, HI), (SENT, OK), (RECEIVED, CLOSE_INITIATOR)]


def test_listener_holds_the_stream_as_closed_by_the_peer() -> None:
    assert mplex.session(EXCHANGE) == [(3, False, "remote_closed")]


def test_dialer_holds_the_stream_as_closed_by_itself() -> None:
    assert mplex.session(flip(EXCHANGE)) == [(3, True, "local_closed")]


def test_listener_may_still_write_after_the_peer_closed() -> None:
    assert mplex.session([*EXCHANGE, (SENT, OK)]) == [(3, False, "remote_closed")]


def test_stream_is_closed_once_both_sides_closed() -> None:
    events = [*EXCHANGE, (SENT, CLOSE_RECEIVER)]
    assert mplex.session(events) == [(3, False, "closed")]


def test_both_sides_may_open_one_id() -> None:
    events = [(RECEIVED, OPEN_3), (SENT, OPEN_3)]
    assert mplex.session(events) == [(3, False, "open"), (3, True, "open")]


def test_a_reset_ends_both_directions() -> None:
    events = [(RECEIVED, OPEN_3), (RECEIVED, RESET_INITIATOR)]
    assert mplex.session(events) == [(3, False, "open+remote_reset")]
    with raises(
        mplex.MplexError,
        "event 2: write on stream 3 (opened locally: false) after its close or reset",
    ):
        mplex.session([*events, (SENT, OK)])


def test_crossing_resets_after_a_close() -> None:
    events = [
        (RECEIVED, OPEN_3),
        (RECEIVED, CLOSE_INITIATOR),
        (SENT, RESET_RECEIVER),
        (RECEIVED, RESET_INITIATOR),
    ]
    assert mplex.session(events) == [(3, False, "remote_closed+local_reset+remote_reset")]


def test_several_frames_in_one_event() -> None:
    assert mplex.session([(RECEIVED, OPEN_3 + HI + CLOSE_INITIATOR)]) == [
        (3, False, "remote_closed")
    ]


def test_data_in_flight_after_a_reset_by_this_side_is_dropped() -> None:
    events = [(RECEIVED, OPEN_3), (SENT, RESET_RECEIVER), (RECEIVED, HI)]
    assert mplex.session(events) == [(3, False, "open+local_reset")]


def test_the_peer_reset_ends_the_frames_in_flight() -> None:
    events = [(RECEIVED, OPEN_3), (SENT, RESET_RECEIVER), (RECEIVED, RESET_INITIATOR)]
    assert mplex.session(events) == [(3, False, "open+local_reset+remote_reset")]
    with raises(
        mplex.MplexError,
        "event 3: write on stream 3 (opened locally: false) after its close or reset",
    ):
        mplex.session([*events, (RECEIVED, HI)])


def test_the_peer_close_ends_the_frames_in_flight() -> None:
    events = [(RECEIVED, OPEN_3), (SENT, RESET_RECEIVER), (RECEIVED, CLOSE_INITIATOR)]
    assert mplex.session(events) == [(3, False, "remote_closed+local_reset")]


def test_a_reset_after_the_peer_closed_drops_nothing() -> None:
    events = [*EXCHANGE, (SENT, RESET_RECEIVER), (RECEIVED, HI)]
    with raises(
        mplex.MplexError,
        "event 5: write on stream 3 (opened locally: false) after its close or reset",
    ):
        mplex.session(events)


def test_no_event_leaves_no_stream() -> None:
    assert mplex.session(()) == []


@pytest.mark.parametrize(
    ("events", "message", "code"),
    [
        # The peer writes after it closed its side.
        ([*EXCHANGE, (RECEIVED, BANG)], "event 4: write on stream 3", 103),
        # Data after a reset.
        (
            [(RECEIVED, OPEN_3), (RECEIVED, RESET_INITIATOR), (RECEIVED, HI)],
            "event 2: write on stream 3",
            103,
        ),
        # A second reset.
        (
            [(RECEIVED, OPEN_3), (RECEIVED, RESET_INITIATOR), (RECEIVED, RESET_INITIATOR)],
            "event 2: write on stream 3",
            103,
        ),
        # A second close by the peer.
        ([*EXCHANGE, (RECEIVED, CLOSE_INITIATOR)], "event 4: write on stream 3", 103),
    ],
)
def test_write_after_close_is_refused(
    events: list[tuple[bool, bytes]], message: str, code: int
) -> None:
    with raises(
        mplex.MplexError, message + " (opened locally: false) after its close or reset"
    ) as info:
        mplex.session(events)
    assert info.value.code == code


def test_this_side_may_not_write_after_its_own_close() -> None:
    events = [*flip(EXCHANGE), (SENT, BANG)]
    with raises(
        mplex.MplexError,
        "event 4: write on stream 3 (opened locally: true) after its close or reset",
    ) as info:
        mplex.session(events)
    assert info.value.code == 103


def test_an_id_opened_twice_is_refused() -> None:
    with raises(
        mplex.MplexError, "event 1: stream 3 (opened locally: false) was opened before"
    ) as info:
        mplex.session([(RECEIVED, OPEN_3), (RECEIVED, OPEN_3)])
    assert info.value.code == 101


def test_a_frame_on_an_unknown_stream_is_refused() -> None:
    with raises(mplex.MplexError, "event 0: stream 3 (opened locally: false) is unknown") as info:
        mplex.session([(RECEIVED, HI)])
    assert info.value.code == 102


def test_a_frame_that_does_not_decode_is_refused() -> None:
    # Flag 7 names no flag.
    message = "event 0: mplex frame rejected: EthLib.Networking.Libp2p.Mplex.MplexError.unknownFlag"
    with raises(mplex.MplexError, message) as info:
        mplex.session([(RECEIVED, bytes.fromhex("0700"))])
    assert info.value.code == 2
