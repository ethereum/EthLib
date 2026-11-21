"""RLP of 200000 nested lists, past the depth that a recursive decoder or conversion reaches."""

from ethlib.serialization import rlp

DEPTH = 200000


def nested(depth: int) -> bytes:
    """The encoding of `depth` nested lists around nothing, built from the inside out."""
    prefixes = []
    size = 0
    for _ in range(depth):
        if size <= 55:
            prefix = bytes([0xC0 + size])
        else:
            length = size.to_bytes((size.bit_length() + 7) // 8, "big")
            prefix = bytes([0xF7 + len(length)]) + length
        prefixes.append(prefix)
        size += len(prefix)
    return b"".join(reversed(prefixes))


def test_nested_lists_decode() -> None:
    encoded = nested(DEPTH)
    assert nested(3) == bytes.fromhex("c2c1c0")
    # One byte each for payloads up to 55 bytes, two up to 255, three up to 65535, then four.
    assert len(encoded) == 56 + 2 * 100 + 3 * 21760 + 4 * (DEPTH - 156 - 21760)
    item = rlp.decode(encoded)
    # Walk down without recursion: each level holds exactly the next one.
    for _ in range(DEPTH - 1):
        assert isinstance(item, list)
        assert len(item) == 1
        item = item[0]
    assert item == []
