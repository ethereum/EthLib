"""The size limits on the data of a gossip message."""

import pytest

from ethlib.errors import GossipError
from ethlib.networking import gossip

MAX_PAYLOAD_SIZE = 10 * 1024 * 1024
MAX_COMPRESSED = 32 + MAX_PAYLOAD_SIZE + MAX_PAYLOAD_SIZE // 6

# 32 zero bytes as one Snappy block: the length 32, a literal of one zero byte, and a copy of
# 31 bytes from 1 byte back (python-snappy 0.7.3 on cramjam 2.14.0).
PAYLOAD = bytes(32)
COMPRESSED = bytes.fromhex("2000007a0100")


def _literal_block(payload: bytes) -> bytes:
    """A Snappy block that holds the payload as one literal, for payloads of at least 61 bytes."""
    n = len(payload)
    length = bytearray()
    m = n
    while True:
        low = m & 0x7F
        m >>= 7
        length.append(low | (0x80 if m else 0))
        if not m:
            break
    size = (n - 1).to_bytes(4, "little")
    return bytes(length) + bytes([63 << 2]) + size + payload


def _code(error: GossipError) -> int:
    return error.code


def test_accepts_within_bounds() -> None:
    assert gossip.decode_payload(32, COMPRESSED) == PAYLOAD


def test_type_bound() -> None:
    with pytest.raises(GossipError) as caught:
        gossip.decode_payload(31, COMPRESSED)
    assert _code(caught.value) == 4


def test_not_snappy() -> None:
    with pytest.raises(GossipError) as caught:
        gossip.decode_payload(32, bytes(32))
    assert _code(caught.value) == 3


def test_payload_cap() -> None:
    # One byte over the cap is rejected even when the type allows it.
    data = _literal_block(bytes(MAX_PAYLOAD_SIZE + 1))
    assert len(data) <= MAX_COMPRESSED
    with pytest.raises(GossipError) as caught:
        gossip.decode_payload(2**64 - 1, data)
    assert _code(caught.value) == 4
    assert gossip.decode_payload(2**64 - 1, _literal_block(bytes(MAX_PAYLOAD_SIZE))) == bytes(
        MAX_PAYLOAD_SIZE
    )


def test_compressed_length() -> None:
    with pytest.raises(GossipError) as caught:
        gossip.decode_payload(2**64 - 1, bytes(MAX_COMPRESSED + 1))
    assert _code(caught.value) == 2
