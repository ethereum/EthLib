"""QUIC frame layouts (RFC 9000 §19) and packet-type rules (§12.4) derived by hand."""

import pytest

from ethlib.networking import quic
from raising import raises

# Each fixture writes the fields in their RFC 9000 §19 wire order.
# Small integers use one-byte QUIC integers, and opaque data is ab or a fixed byte sequence.
FRAMES = [
    ("padding", "00"),
    ("ping", "01"),
    (
        ("ack", {"largest": 10, "delay": 0, "first_range": 0, "ranges": [], "ecn": None}),
        "020a000000",
    ),
    (
        (
            "ack",
            {"largest": 10, "delay": 0, "first_range": 0, "ranges": [(1, 2)], "ecn": (1, 2, 3)},
        ),
        "030a0001000102010203",
    ),
    (("reset_stream", 1, 2, 3), "04010203"),
    (("stop_sending", 1, 2), "050102"),
    (("crypto", 0, [171]), "060001ab"),
    (("new_token", [171]), "0701ab"),
    (("max_data", 1), "1001"),
    (("max_stream_data", 1, 2), "110102"),
    (("max_streams", False, 1), "1201"),
    (("max_streams", True, 1), "1301"),
    (("data_blocked", 1), "1401"),
    (("stream_data_blocked", 1, 2), "150102"),
    (("streams_blocked", False, 1), "1601"),
    (("streams_blocked", True, 1), "1701"),
    (("new_connection_id", 2, 1, [171], bytes(16)), "18020101ab" + "00" * 16),
    (("retire_connection_id", 1), "1901"),
    (("path_challenge", bytes.fromhex("0001020304050607")), "1a0001020304050607"),
    (("path_response", bytes.fromhex("0001020304050607")), "1b0001020304050607"),
    (("connection_close", 1, 0, [104, 105]), "1c0100026869"),
    (("connection_close", 1, None, [104, 105]), "1d01026869"),
    ("handshake_done", "1e"),
]


@pytest.mark.parametrize(("frame", "encoded"), FRAMES)
def test_frame_round_trip(frame: quic.Frame, encoded: str) -> None:
    data = bytes.fromhex(encoded)
    assert quic.encode_frame(frame) == data
    assert quic.decode_frame("one_rtt", data + b"tail") == (frame, b"tail")


@pytest.mark.parametrize("kind", range(8, 16))
def test_stream_flag_layouts(kind: int) -> None:
    # OFF=4, LEN=2, FIN=1, RFC 9000 §19.8.
    # Without LEN the data ends at the packet boundary.
    offset = 2 if kind & 4 else None
    length_present = bool(kind & 2)
    frame = ("stream", 1, offset, length_present, bool(kind & 1), [171])
    encoded = bytes([kind, 1] + ([2] if kind & 4 else []) + ([1] if length_present else []) + [171])
    assert quic.encode_frame(frame) == encoded
    assert quic.decode_frame("one_rtt", encoded) == (frame, b"")


def test_stream_without_length_consumes_the_packet() -> None:
    frame = ("stream", 1, None, False, False, [171, 205])
    assert quic.decode_frame("one_rtt", bytes.fromhex("0801abcd")) == (frame, b"")


@pytest.mark.parametrize(
    "encoded",
    [
        # A type in a longer form, and an unknown type (§12.4).
        "4001",
        "1f",
        # ACK range underflow (§19.3.1) and an empty token (§19.7).
        "0200000001",
        "0700",
        # Connection ID lengths 0 and 21, and Retire Prior To above Sequence Number (§19.15).
        "18000000" + "00" * 16,
        "18000015" + "00" * 21 + "00" * 16,
        "18010201ab" + "00" * 16,
        # Bodies that end early are badly formatted frames (§20.1).
        "0601",
        "02",
        "18000001",
    ],
)
def test_frame_encoding_error(encoded: str) -> None:
    message = "QUIC frame rejected: EthLib.Networking.Quic.Wire.Error.frameEncoding"
    with raises(quic.QuicError, message) as info:
        quic.decode_frame("one_rtt", bytes.fromhex(encoded))
    assert info.value.code == 8


@pytest.mark.parametrize(
    ("packet", "encoded"),
    [
        ("initial", "1001"),
        ("handshake", "1e"),
        ("zero_rtt", "0200000000"),
        ("zero_rtt", "060000"),
        ("zero_rtt", "1b" + "00" * 8),
        ("initial", "0801ab"),
        ("handshake", "0801ab"),
    ],
)
def test_forbidden_packet_types(packet: quic.PacketType, encoded: str) -> None:
    message = "QUIC frame rejected: EthLib.Networking.Quic.Wire.Error.protocolViolation"
    with raises(quic.QuicError, message) as info:
        quic.decode_frame(packet, bytes.fromhex(encoded))
    assert info.value.code == 9


@pytest.mark.parametrize(("frame", "encoded"), FRAMES)
@pytest.mark.parametrize("packet", ["initial", "handshake", "zero_rtt"])
def test_table_3(frame: quic.Frame, encoded: str, packet: quic.PacketType) -> None:
    # RFC 9000 §12.4, Table 3: I/H carry only PADDING, PING, ACK, CRYPTO and transport close.
    # 0-RTT excludes ACK, CRYPTO, NEW_TOKEN, PATH_RESPONSE and HANDSHAKE_DONE.
    kind = int(encoded[:2], 16)
    allowed = (
        kind in {0, 1, 2, 3, 6, 28} if packet != "zero_rtt" else kind not in {2, 3, 6, 7, 27, 30}
    )
    if allowed:
        assert quic.decode_frame(packet, bytes.fromhex(encoded)) == (frame, b"")
    else:
        message = "QUIC frame rejected: EthLib.Networking.Quic.Wire.Error.protocolViolation"
        with raises(quic.QuicError, message):
            quic.decode_frame(packet, bytes.fromhex(encoded))


@pytest.mark.parametrize(
    "frame",
    [
        ("new_token", []),
        ("max_streams", False, 2**60 + 1),
        ("new_connection_id", 1, 2, [171], bytes(16)),
    ],
)
def test_encoder_rejects_malformed_frames(frame: quic.Frame) -> None:
    message = "QUIC frame rejected: EthLib.Networking.Quic.Wire.Error.frameEncoding"
    with raises(quic.QuicError, message) as info:
        quic.encode_frame(frame)
    assert info.value.code == 8
