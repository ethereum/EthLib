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
    ],
)
def test_headers(header, encoded: str, short_length: int) -> None:
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
    ("encoded", "error"),
    [
        ("800000000100000100", "fixedBit"),
        ("c4000000010000000100", "reservedBits"),
        ("4800", "reservedBits"),
        ("c00000000200000100", "version"),
        ("c00000000115", "connectionIdLength"),
        ("c3000000010000000300000000", "packetLength"),
    ],
)
def test_malformed_headers(encoded: str, error: str) -> None:
    # RFC 9000 §§17.2–17.3: fixed/reserved bits, supported version, CID bound and PN length.
    message = f"QUIC header rejected: EthLib.Networking.Quic.Wire.Error.{error}"
    with raises(quic.QuicError, message):
        quic.decode_header(0, bytes.fromhex(encoded))
