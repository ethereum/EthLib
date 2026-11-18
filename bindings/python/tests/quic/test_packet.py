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
        (("initial", bytes([131, 148, 200, 240, 62, 81, 87, 8]), b"", b"", 3, 1182, 2), INITIAL, 0),
        (("zero_rtt", b"", b"", 0, 1, 1), "d00000000100000101", 0),
        (("handshake", b"", b"", 0, 1, 1), "e00000000100000101", 0),
        # RFC 9001 Appendix A.5: the unprotected short header.
        (("one_rtt", b"", False, False, 2, 49140), "4200bff4", 0),
        # Fixed, spin and key-phase bits, an 8-byte connection ID known from the connection.
        (("one_rtt", bytes([1] * 8), True, True, 0, 7), "64" + "01" * 8 + "07", 8),
        (
            (
                "retry",
                b"",
                bytes([240, 103, 165, 80, 42, 66, 98, 181]),
                bytes([116, 111, 107, 101, 110]),
                bytes.fromhex("04a265ba2eff4d829058fb3f0f2496ba"),
                15,
            ),
            RETRY,
            0,
        ),
        (("version_negotiation", b"", b"", 0, [1]), "8000000000000000000001", 0),
        # Figure 14 repeats Supported Version zero or more times.
        (("version_negotiation", b"", b"", 0, []), "80000000000000", 0),
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
    header = ("version_negotiation", bytes(255), bytes([1] * 21), 127, [1])
    assert quic.decode_header(0, quic.encode_header(header)) == (header, b"")


# The byte sizes of the fields of INITIAL in order (§17.2.2), without its empty source ID.
# The fields are the first byte, the version, the destination ID length and the ID itself.
# Then come the source ID length, the token length, the Length and the packet number.
INITIAL_FIELDS = [1, 4, 1, 8, 1, 1, 2, 4]

# The start of the Length, a two-byte integer whose first byte selects its size (§16).
LENGTH_START = 16


def _truncation(prefix: int) -> tuple[int, int]:
    # The size of the field that the prefix ends inside, and the bytes of it that the prefix holds.
    start = 0
    for size in INITIAL_FIELDS:
        if prefix < start + size:
            # Before its first byte, an integer needs only that byte.
            return (1 if prefix == LENGTH_START else size), prefix - start
        start += size
    raise AssertionError(prefix)


@pytest.mark.parametrize("prefix", range(len(bytes.fromhex(INITIAL))))
def test_initial_truncation(prefix: int) -> None:
    # Every proper prefix ends inside a required field (§17.2.2).
    needed, available = _truncation(prefix)
    message = (
        f"QUIC header rejected: EthLib.Networking.Quic.Wire.Error.truncated {needed} {available}"
    )
    with raises(quic.QuicError, message):
        quic.decode_header(0, bytes.fromhex(INITIAL)[:prefix])


def test_packet_number_appendix_a3() -> None:
    assert quic.decode_packet_number(1, 0x9B32, 0xA82F30EA + 1) == 0xA82F9B32
    assert quic.encode_packet_number(1, 0xA82F9B32) == bytes.fromhex("9b32")


@pytest.mark.parametrize(
    ("number", "width", "encoded"),
    [(0xAC5C02, 1, "5c02"), (0xACE8FE, 2, "ace8fe")],
)
def test_packet_number_width_appendix_a2(number: int, width: int, encoded: str) -> None:
    # RFC 9000 Appendix A.2: 0xabe8b3 is the largest acknowledged packet number.
    assert quic.packet_number_width(number, 0xABE8B3) == width
    assert quic.encode_packet_number(width, number) == bytes.fromhex(encoded)
    assert quic.decode_packet_number(width, int(encoded, 16), 0xABE8B3 + 1) == number


@pytest.mark.parametrize(
    ("gap", "width"),
    [
        (1, 0),
        (2**7 - 1, 0),
        (2**7, 1),
        (2**15 - 1, 1),
        (2**15, 2),
        (2**23 - 1, 2),
        (2**23, 3),
        (2**31 - 1, 3),
    ],
)
def test_packet_number_width_acknowledged_gap(gap: int, width: int) -> None:
    # RFC 9000 §17.1 requires a range strictly greater than twice the gap.
    number = 100 + gap
    assert quic.packet_number_width(number, 100) == width
    encoded = quic.encode_packet_number(width, number)
    assert quic.decode_packet_number(width, int.from_bytes(encoded, "big"), 101) == number


@pytest.mark.parametrize(
    ("number", "width", "encoded"),
    [
        (0, 0, "00"),
        (255, 0, "ff"),
        (256, 1, "0100"),
        (65535, 1, "ffff"),
        (65536, 2, "010000"),
        (2**24 - 1, 2, "ffffff"),
        (2**24, 3, "01000000"),
        (2**32 - 1, 3, "ffffffff"),
    ],
)
def test_packet_number_width_without_acknowledgement(number: int, width: int, encoded: str) -> None:
    # RFC 9000 §17.1 requires the full number before any acknowledgement.
    assert quic.packet_number_width(number, None) == width
    assert quic.encode_packet_number(width, number) == bytes.fromhex(encoded)
    assert quic.decode_packet_number(width, int(encoded, 16), 0) == number


def test_packet_number_width_near_protocol_limit() -> None:
    # RFC 9000 §17.1 includes 2^62 - 1 in the packet-number range.
    number = 2**62 - 1
    assert quic.packet_number_width(number, number - 1) == 0
    assert quic.encode_packet_number(0, number) == bytes.fromhex("ff")
    assert quic.decode_packet_number(0, 255, number) == number


@pytest.mark.parametrize(
    ("number", "largest_acked"), [(0, 0), (1, 2), (100 + 2**31, 100), (2**32, None)]
)
def test_packet_number_width_rejections(number: int, largest_acked: int | None) -> None:
    # RFC 9000 §§12.3 and 17.1: increasing packet numbers and a field of at most four bytes.
    # The error retains both inputs, including whether an acknowledgement was available.
    acknowledged = "none" if largest_acked is None else f"(some {largest_acked})"
    message = (
        "QUIC packet number rejected: EthLib.Networking.Quic.Packet.WidthError.invalid "
        f"{number} {acknowledged}"
    )
    with raises(quic.QuicError, message) as info:
        quic.packet_number_width(number, largest_acked)
    assert info.value.code == 10


@pytest.mark.parametrize(("number", "largest_acked"), [(2**62, None), (1, 2**62)])
def test_packet_number_width_rejects_values_outside_protocol(
    number: int, largest_acked: int | None
) -> None:
    # RFC 9000 §17.1 bounds packet numbers below 2^62, checked by the typed converter.
    message = f"expected an int below {2**62}, got {2**62}"
    with raises(quic.QuicError, message) as info:
        quic.packet_number_width(number, largest_acked)
    assert info.value.code == 0


@pytest.mark.parametrize(("number", "largest_acked"), [(-1, None), (1, -1)])
def test_packet_number_width_rejects_negative_values(
    number: int, largest_acked: int | None
) -> None:
    with raises(ValueError, "cannot pass a negative int to Lean"):
        quic.packet_number_width(number, largest_acked)


@pytest.mark.parametrize(
    ("expected", "truncated", "number"), [(128, 0, 256), (127, 0, 0), (1, 255, 255)]
)
def test_packet_number_window_edges(expected: int, truncated: int, number: int) -> None:
    # Appendix A.3 chooses the higher candidate at a half-window tie and avoids underflow.
    assert quic.decode_packet_number(0, truncated, expected) == number


@pytest.mark.parametrize(
    ("encoded", "error", "code"),
    [
        # The first byte, in decimal, follows the name of a bit error.
        ("800000000100000100", "fixedBit 128", 3),
        ("c4000000010000000100", "reservedBits 196", 5),
        ("4800", "reservedBits 72", 5),
        ("c00000000200000100", "version 2", 4),
        # Only version 1 limits connection IDs to 20 bytes (§17.2).
        ("c00000000215" + "00" * 21 + "00", "version 2", 4),
        ("c00000000115", "connectionIdLength 21 20", 2),
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
        ("one_rtt", bytes(21), False, False, 0, 0),
        ("one_rtt", b"", False, False, 0, 256),
        ("handshake", b"", b"", 1, 1, 0),
        ("retry", b"", b"", b"", bytes(16), 0),
    ],
)
def test_encoder_rejects_invalid_headers(header: quic.Header) -> None:
    # A long connection ID, a number wider than its field, a short Length and an empty token.
    message = "QUIC header rejected: EthLib.Networking.Quic.Wire.Error.packetLength"
    with raises(quic.QuicError, message) as info:
        quic.encode_header(header)
    assert info.value.code == 6


def test_short_connection_id_length_bound() -> None:
    message = "QUIC header rejected: EthLib.Networking.Quic.Wire.Error.connectionIdLength 21 20"
    with raises(quic.QuicError, message) as info:
        quic.decode_header(21, bytes.fromhex("40" + "00" * 22))
    assert info.value.code == 2


@pytest.mark.parametrize(
    ("width", "truncated", "expected"), [(0, 256, 0), (0, 0, 2**62 + 1), (0, 0, 2**62)]
)
def test_packet_number_rejections(width: int, truncated: int, expected: int) -> None:
    # A truncated value wider than its field, an expectation past 2^62, and a result of 2^62.
    # The error holds the truncated number, its width in bytes and the expected number.
    message = (
        "QUIC packet number rejected: EthLib.Networking.Quic.Wire.Error.packetNumber "
        f"{truncated} {width + 1} {expected}"
    )
    with raises(quic.QuicError, message) as info:
        quic.decode_packet_number(width, truncated, expected)
    assert info.value.code == 7
