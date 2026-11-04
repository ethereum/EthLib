"""RLP of a list of a million items, which once overflowed the stack."""

from ethlib.serialization import rlp

COUNT = 1_000_000


def test_long_list_round_trip() -> None:
    items = [b"\x01\x02"] * COUNT
    encoded = rlp.encode(items)
    # Each item is `82 01 02`, and the payload length takes 3 bytes after `fa`.
    assert encoded[:4] == bytes([0xFA]) + (3 * COUNT).to_bytes(3, "big")
    assert len(encoded) == 4 + 3 * COUNT
    assert rlp.decode(encoded) == items
