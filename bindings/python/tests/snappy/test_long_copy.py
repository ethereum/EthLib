"""Snappy copies that repeat their window and that reach far back (format_description.txt §2.2)."""

from ethlib.networking import snappy


def _varint(n: int) -> bytes:
    out = bytearray()
    while n >= 0x80:
        out.append(n & 0x7F | 0x80)
        n >>= 7
    out.append(n)
    return bytes(out)


def _literal(data: bytes) -> bytes:
    # A literal of at most 60 bytes keeps its length minus one in the tag (§2.1).
    assert 1 <= len(data) <= 60
    return bytes([(len(data) - 1) << 2]) + data


def _copy(length: int, offset: int) -> bytes:
    # A copy with a two-byte offset: tag 10, the length minus one in the upper six bits (§2.2.2).
    assert 1 <= length <= 64 and 1 <= offset < 1 << 16
    return bytes([(length - 1) << 2 | 2]) + offset.to_bytes(2, "little")


def test_copy_longer_than_its_offset() -> None:
    # 1000 copies of 64 bytes at offset 3 repeat "abc" across 64 003 bytes.
    count = 1000
    expected = (b"abc" * (64 * count // 3 + 2))[: 3 + 64 * count]
    block = _varint(len(expected)) + _literal(b"abc") + _copy(64, 3) * count
    assert snappy.decompress(block) == expected


def test_copy_far_back() -> None:
    # 60 distinct bytes, then 50 000 bytes of filler, then a copy of the first 60 bytes.
    head = bytes(range(60))
    filler = b"\x00" * 50_000
    block = (
        _varint(60 + len(filler) + 60)
        + _literal(head)
        + _literal(b"\x00")
        + _copy(64, 1) * (len(filler) // 64)
        + _copy(len(filler) % 64 - 1, 1)
        + _copy(60, 60 + len(filler))
    )
    assert snappy.decompress(block) == head + filler + head
