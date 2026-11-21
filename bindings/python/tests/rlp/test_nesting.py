"""RLP of 5000 nested lists, well inside the depth that the bindings return."""

from ethlib.serialization import rlp

DEPTH = 5000


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
    # 56 one-byte prefixes, 100 two-byte prefixes up to a payload of 255, then three bytes each.
    assert len(encoded) == 56 + 2 * 100 + 3 * (DEPTH - 156)
    item = rlp.decode(encoded)
    # Walk down without recursion: each level holds exactly the next one.
    for _ in range(DEPTH - 1):
        assert isinstance(item, list)
        assert len(item) == 1
        item = item[0]
    assert item == []
