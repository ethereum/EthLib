"""The gossip message ID against IDs computed with hashlib."""

import hashlib

from ethlib.networking import gossip

# The payload is 32 zero bytes.
# python-snappy 0.7.3 (on cramjam 2.14.0) compresses it to 20 00 00 7a 01 00: the length 32,
# a literal of one zero byte, and a copy of 31 bytes from 1 byte back.
# The raw payload is not a Snappy block: its first byte declares an empty block, and 31 more
# bytes follow.
PAYLOAD = bytes(32)
COMPRESSED = bytes.fromhex("2000007a0100")
RAW = PAYLOAD

# The beacon block topic; the ID reads it only as bytes, so any fork digest would do.
TOPIC = b"/eth2/afcaaba0/beacon_block/ssz_snappy"

VALID = bytes.fromhex("01000000")
INVALID = bytes.fromhex("00000000")


def _id(*parts: bytes) -> bytes:
    return hashlib.sha256(b"".join(parts)).digest()[:20]


def _length(topic: bytes) -> bytes:
    return len(topic).to_bytes(8, "little")


def test_phase0_valid() -> None:
    expected = bytes.fromhex("11bc115c0226329c9a35a7fee1d29c1f5248e0f7")
    assert expected == _id(VALID, PAYLOAD)
    assert gossip.message_id_phase0(COMPRESSED) == expected


def test_phase0_invalid() -> None:
    expected = bytes.fromhex("6db65fd59fd356f6729140571b5bcd6bb3b83492")
    assert expected == _id(INVALID, RAW)
    assert gossip.message_id_phase0(RAW) == expected


def test_altair_valid() -> None:
    expected = bytes.fromhex("df1bb54c62c1776b5028f44cb879b2b4f3926c09")
    assert expected == _id(VALID, _length(TOPIC), TOPIC, PAYLOAD)
    assert gossip.message_id_altair(TOPIC, COMPRESSED) == expected


def test_altair_invalid() -> None:
    expected = bytes.fromhex("723e3f2785c7227da1fe5cb06a5ed46a3a647ad4")
    assert expected == _id(INVALID, _length(TOPIC), TOPIC, RAW)
    assert gossip.message_id_altair(TOPIC, RAW) == expected


def test_altair_empty() -> None:
    # Empty data is not a Snappy block, since a block starts with its length.
    expected = bytes.fromhex("15ec7bf0b50732b49f8228e07d24365338f9e3ab")
    assert expected == _id(INVALID, bytes(8))
    assert gossip.message_id_altair(b"", b"") == expected


def test_phase0_long_preamble() -> None:
    # The length 0 written in six preamble bytes, one more than a 32-bit length ever needs.
    # The decoder reads at most five preamble bytes, so the data is hashed as it is.
    # python-snappy decompresses it to the empty payload, which would give _id(VALID) instead.
    data = bytes.fromhex("808080808000")
    expected = bytes.fromhex("f50bf126b68e05a9aa7f6c4f039ab9ad253fd405")
    assert expected == _id(INVALID, data)
    assert expected != _id(VALID)
    assert gossip.message_id_phase0(data) == expected
