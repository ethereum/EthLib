"""QUIC packet headers and packet numbers against RFC 9000 and RFC 9001."""

import pytest

from ethlib.networking import quic
from raising import raises

# RFC 9001 Appendix A.2: Initial header through its unprotected packet number.
INITIAL = "c300000001088394c8f03e5157080000449e00000002"

# RFC 9001 Appendix A.4: the Retry packet, including its integrity tag.
RETRY = "ff000000010008f067a5502a4262b5746f6b656e04a265ba2eff4d829058fb3f0f2496ba"


@pytest.mark.parametrize(
    ("header", "encoded", "short_length"),
    [
        (("initial", [131, 148, 200, 240, 62, 81, 87, 8], [], [], 3, 1182, 2), INITIAL, 0),
        (("zero_rtt", [], [], 0, 1, 1), "d00000000100000101", 0),
        (("handshake", [], [], 0, 1, 1), "e00000000100000101", 0),
        # RFC 9001 Appendix A.5: the unprotected short header.
        (("one_rtt", [], False, False, 2, 49140), "4200bff4", 0),
        # Fixed, spin and key-phase bits, an 8-byte connection ID known from the connection.
        (("one_rtt", [1] * 8, True, True, 0, 7), "64" + "01" * 8 + "07", 8),
        (
            (
                "retry",
                [],
                [240, 103, 165, 80, 42, 66, 98, 181],
                [116, 111, 107, 101, 110],
                bytes.fromhex("04a265ba2eff4d829058fb3f0f2496ba"),
                15,
            ),
            RETRY,
            0,
        ),
        (("version_negotiation", [], [], 0, [1]), "8000000000000000000001", 0),
        # Figure 14 repeats Supported Version zero or more times.
        (("version_negotiation", [], [], 0, []), "80000000000000", 0),
    ],
)
def test_headers(header: quic.Header, encoded: str, short_length: int) -> None:
    data = bytes.fromhex(encoded)
    assert quic.encode_header(header) == data
    assert quic.decode_header(short_length, data) == (header, b"")


def test_header_preserves_payload() -> None:
    header, rest = quic.decode_header(0, bytes.fromhex(INITIAL) + b"payload")
    assert rest == b"payload"
    assert quic.encode_header(header) == bytes.fromhex(INITIAL)


def test_version_negotiation_connection_ids_are_version_independent() -> None:
    # RFC 9000 §17.2.1 permits up to 255 bytes, independently of version 1's 20-byte bound.
    header = ("version_negotiation", [0] * 255, [1] * 21, 127, [1])
    assert quic.decode_header(0, quic.encode_header(header)) == (header, b"")


@pytest.mark.parametrize("prefix", range(len(bytes.fromhex(INITIAL))))
def test_initial_truncation(prefix: int) -> None:
    # Every proper prefix ends inside a required field (§17.2.2).
    with raises(
        quic.QuicError, "QUIC header rejected: EthLib.Networking.Quic.Wire.Error.truncated"
    ):
        quic.decode_header(0, bytes.fromhex(INITIAL)[:prefix])


def test_packet_number_appendix_a3() -> None:
    assert quic.decode_packet_number(1, 0x9B32, 0xA82F30EA + 1) == 0xA82F9B32
    assert quic.encode_packet_number(1, 0xA82F9B32) == bytes.fromhex("9b32")


@pytest.mark.parametrize(
    ("expected", "truncated", "number"), [(128, 0, 256), (127, 0, 0), (1, 255, 255)]
)
def test_packet_number_window_edges(expected: int, truncated: int, number: int) -> None:
    # Appendix A.3 chooses the higher candidate at a half-window tie and avoids underflow.
    assert quic.decode_packet_number(0, truncated, expected) == number


@pytest.mark.parametrize(
    ("encoded", "error", "code"),
    [
        ("800000000100000100", "fixedBit", 3),
        ("c4000000010000000100", "reservedBits", 5),
        ("4800", "reservedBits", 5),
        ("c00000000200000100", "version", 4),
        # Only version 1 limits connection IDs to 20 bytes (§17.2).
        ("c00000000215" + "00" * 21 + "00", "version", 4),
        ("c00000000115", "connectionIdLength", 2),
        # A Length shorter than the packet-number field.
        ("c3000000010000000300000000", "packetLength", 6),
    ],
)
def test_malformed_headers(encoded: str, error: str, code: int) -> None:
    # RFC 9000 §17.2 and §17.3.1: fixed and reserved bits, version and connection IDs.
    message = f"QUIC header rejected: EthLib.Networking.Quic.Wire.Error.{error}"
    with raises(quic.QuicError, message) as info:
        quic.decode_header(0, bytes.fromhex(encoded))
    assert info.value.code == code


@pytest.mark.parametrize(
    "header",
    [
        ("one_rtt", [0] * 21, False, False, 0, 0),
        ("one_rtt", [], False, False, 0, 256),
        ("handshake", [], [], 1, 1, 0),
        ("retry", [], [], [], bytes(16), 0),
    ],
)
def test_encoder_rejects_invalid_headers(header: quic.Header) -> None:
    # A long connection ID, a number wider than its field, a short Length and an empty token.
    message = "QUIC header rejected: EthLib.Networking.Quic.Wire.Error.packetLength"
    with raises(quic.QuicError, message) as info:
        quic.encode_header(header)
    assert info.value.code == 6


def test_short_connection_id_length_bound() -> None:
    message = "QUIC header rejected: EthLib.Networking.Quic.Wire.Error.connectionIdLength"
    with raises(quic.QuicError, message) as info:
        quic.decode_header(21, bytes.fromhex("40" + "00" * 22))
    assert info.value.code == 2


@pytest.mark.parametrize(
    ("width", "truncated", "expected"), [(0, 256, 0), (0, 0, 2**62 + 1), (0, 0, 2**62)]
)
def test_packet_number_rejections(width: int, truncated: int, expected: int) -> None:
    # A truncated value wider than its field, an expectation past 2^62, and a result of 2^62.
    message = "QUIC packet number rejected: EthLib.Networking.Quic.Wire.Error.packetNumber"
    with raises(quic.QuicError, message) as info:
        quic.decode_packet_number(width, truncated, expected)
    assert info.value.code == 7
