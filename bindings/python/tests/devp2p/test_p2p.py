"""The messages of the "p2p" capability against EIP-8 and hand-built Snappy frames."""

import pytest

from ethlib.networking import devp2p

# The Hello of "Test Vectors", "devp2p Base Protocol", in EIP-8.
# It holds version 55, two capabilities and three list elements after the five fields of Hello.
#
# File: EIPS/eip-8.md
# Repository: ethereum/EIPs
# Commit: 0ce679f4654ba4d120c97113626f320475e22fa9
# Licence: CC0-1.0
HELLO = bytes.fromhex(
    "f87137916b6e6574682f76302e39312f706c616e39cdc5836574683dc6846d6f726b1682270fb840"
    "fda1cff674c90c9a197539fe3dfb53086ace64f83ed7c6eabec741f7f381cc803e52ab2cd55d5569"
    "bce4347107a310dfd5f88a010cd2ffd1005ca406f1842877c883666f6f836261720304"
)


def _raw_items(data: bytes) -> list[bytes]:
    """The encodings of the items of the RLP list `data`, which is under 256 bytes long."""
    assert data[0] == 0xF8 and data[1] == len(data) - 2
    payload, items = data[2:], []
    while payload:
        first = payload[0]
        if first < 0x80:
            size = 1
        elif first < 0xB8:
            size = 1 + first - 0x80
        elif first < 0xC0:
            size = 2 + payload[1]
        elif first < 0xF8:
            size = 1 + first - 0xC0
        else:
            size = 2 + payload[1]
        items.append(payload[:size])
        payload = payload[size:]
    return items


def test_eip8_hello() -> None:
    # The reader keeps the five fields of Hello and drops the three elements after them.
    items = _raw_items(HELLO)
    assert len(items) == 8
    body = b"".join(items[:5])
    expected = b"\x80" + bytes([0xF8, len(body)]) + body
    assert devp2p.decode_message(False, b"\x80" + HELLO) == expected
    # Hello is never compressed.
    assert devp2p.decode_message(True, b"\x80" + HELLO) == expected
    assert devp2p.encode_message(True, expected) == expected


def test_ping_compressed() -> None:
    # Ping is ID 0x02 and the empty list c0.
    # Its Snappy block is the length 1, then one literal of one byte with the tag 00.
    assert devp2p.encode_message(True, b"\x02\xc0") == b"\x02\x01\x00\xc0"
    assert devp2p.decode_message(True, b"\x02\x01\x00\xc0") == b"\x02\xc0"
    assert devp2p.encode_message(False, b"\x02\xc0") == b"\x02\xc0"


def test_disconnect_compressed() -> None:
    # Disconnect with the reason 4 is ID 0x01 and the list c1 04.
    # A literal of two bytes has the tag (2 - 1) * 4 = 04.
    frame = b"\x01\x02\x04\xc1\x04"
    assert devp2p.decode_message(True, frame) == b"\x01\xc1\x04"
    assert devp2p.encode_message(True, b"\x01\xc1\x04") == frame


def test_disconnect_without_reason() -> None:
    assert devp2p.decode_message(False, b"\x01\xc0") == b"\x01\xc0"


def test_pong() -> None:
    assert devp2p.decode_message(False, b"\x03\xc0") == b"\x03\xc0"


def test_oversized_message_rejected() -> None:
    # The preamble declares 2^24 + 1 bytes, more than 16 MiB, so no decompression starts.
    size = 2**24 + 1
    preamble = bytes([(size & 0x7F) | 0x80, ((size >> 7) & 0x7F) | 0x80, ((size >> 14) & 0x7F) | 0x80,
                      size >> 21])
    with pytest.raises(devp2p.Devp2pError) as info:
        devp2p.decode_message(True, b"\x02" + preamble + b"\x00\xc0")
    assert info.value.code == 3


def test_unknown_id_rejected() -> None:
    # Code 4 names a message ID outside the "p2p" capability.
    with pytest.raises(devp2p.Devp2pError) as info:
        devp2p.decode_message(False, b"\x04\xc0")
    assert info.value.code == 4


def test_ping_with_items_rejected() -> None:
    # Code 1 names RLP of the wrong shape.
    with pytest.raises(devp2p.Devp2pError) as info:
        devp2p.decode_message(False, b"\x02\xc1\x80")
    assert info.value.code == 1


def test_bad_snappy_block_rejected() -> None:
    # Code 2 names a Snappy block that is not valid: the literal claims 2 bytes, and 1 follows.
    with pytest.raises(devp2p.Devp2pError) as info:
        devp2p.decode_message(True, b"\x02\x05\x04\xc0")
    assert info.value.code == 2
