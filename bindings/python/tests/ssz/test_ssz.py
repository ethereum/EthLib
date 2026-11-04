"""SSZ against values whose bytes and roots are worked out by hand from the SSZ rules."""

import hashlib

import pytest

from ethlib.errors import SszError
from ethlib.serialization import ssz

UINT16 = {"uint": 2}

# A container of two fixed fields, a: uint16 and b: uint16.
FIXED_PAIR = {"container": [["a", UINT16], ["b", UINT16]]}

# A container of a fixed field a: uint16 and a variable field b: List[uint16, 4].
MIXED_PAIR = {"container": [["a", UINT16], ["b", {"list": [UINT16, 4]}]]}

# Each type, value and the bytes of the value.
CASES = [
    # A uint16 puts its low byte first.
    (UINT16, {"uint": 0x0102}, "0201"),
    # A boolean is one byte, 01 for true.
    ("bool", {"bool": True}, "01"),
    # The bits 1, 0, 1 of a Bitvector[3] fill one byte from its lowest bit: 0b101.
    ({"bitvector": 3}, {"bits": [True, False, True]}, "05"),
    # The bits 1, 0, 1 of a Bitlist[8] take a closing bit above them: 0b1101.
    ({"bitlist": 8}, {"bits": [True, False, True]}, "0d"),
    # Two fixed fields are written one after the other.
    (FIXED_PAIR, {"seq": [{"uint": 0x4567}, {"uint": 0x0123}]}, "67452301"),
    # A variable field leaves a four-byte offset among the fixed fields, and its body follows.
    # The fixed part holds two bytes for a and four for the offset, so the body starts at byte 6.
    (MIXED_PAIR, {"seq": [{"uint": 1}, {"seq": [{"uint": 2}, {"uint": 3}]}]},
     "0100060000000200" "0300"),
    # Opaque bytes of a fixed length are written as they are.
    ({"byte_vector": 2}, {"bytes": "0x0102"}, "0102"),
    # A variable field of opaque bytes takes an offset, like any variable field: the body
    # starts at byte 5, after the one byte of a and the four of the offset.
    ({"container": [["a", {"uint": 1}], ["b", {"byte_list": 4}]]},
     {"seq": [{"uint": 7}, {"bytes": "0xaabb"}]}, "0705000000aabb"),
]


@pytest.mark.parametrize(("ssz_type", "value", "encoded"), CASES)
def test_serialize(ssz_type, value, encoded: str) -> None:
    assert ssz.serialize(ssz_type, value) == bytes.fromhex(encoded)


@pytest.mark.parametrize(("ssz_type", "value", "encoded"), CASES)
def test_deserialize(ssz_type, value, encoded: str) -> None:
    assert ssz.deserialize(ssz_type, bytes.fromhex(encoded)) == value


def test_bool_two_rejected() -> None:
    # A byte other than 00 and 01 is no boolean.
    with pytest.raises(ValueError, match="notABit 2$"):
        ssz.deserialize("bool", b"\x02")


def test_bad_hex_rejected() -> None:
    with pytest.raises(ValueError, match="hex"):
        ssz.serialize({"byte_vector": 2}, {"bytes": "0xzz"})


@pytest.mark.parametrize(
    ("ssz_type", "fault"),
    [
        # SSZ defines unsigned integers of 1, 2, 4, 8, 16 and 32 bytes only.
        ({"uint": 3}, "uintWidth 3"),
        # SSZ allows no empty vector and no container without fields.
        ({"vector": [{"uint": 1}, 0]}, "vectorEmpty"),
        ({"container": []}, "containerEmpty"),
    ],
)
def test_illegal_type_rejected(ssz_type, fault: str) -> None:
    with pytest.raises(ValueError, match="type rejected.*" + fault):
        ssz.deserialize(ssz_type, b"")


def test_unknown_type_rejected() -> None:
    # A type that the JSON names no SSZ type for has code 0, which no SSZ error has.
    with pytest.raises(SszError) as caught:
        ssz.serialize({"float": 4}, {"uint": 1})
    assert caught.value.code == 0


def _chunk(hex_bytes: str) -> bytes:
    """A 32-byte chunk: the given bytes, then zero bytes."""
    return bytes.fromhex(hex_bytes).ljust(32, b"\x00")


def _node(left: bytes, right: bytes) -> bytes:
    """The parent of two Merkle nodes, by the SHA-256 of hashlib."""
    return hashlib.sha256(left + right).digest()


ZERO = _chunk("")

# Each type, value and its root, built by hand from the Merkleization rules of SSZ.
ROOTS = [
    # A basic value is its bytes, padded to one chunk, with no hashing.
    (UINT16, {"uint": 0x0102}, _chunk("0201")),
    ("bool", {"bool": True}, _chunk("01")),
    # A container of two fields roots the two field roots as leaves.
    (FIXED_PAIR, {"seq": [{"uint": 0x4567}, {"uint": 0x0123}]},
     _node(_chunk("6745"), _chunk("2301"))),
    # A List[uint16, 4] packs into one chunk, and mixes in its length 2.
    ({"list": [UINT16, 4]}, {"seq": [{"uint": 2}, {"uint": 3}]},
     _node(_chunk("02000300"), _chunk("02"))),
    # A Bitlist[8] packs its bits without the closing bit, and mixes in the bit count 3.
    ({"bitlist": 8}, {"bits": [True, False, True]}, _node(_chunk("05"), _chunk("03"))),
    # A ByteList[33] has room for two chunks, so even an empty one roots a tree of depth 1.
    ({"byte_list": 33}, {"bytes": "0x"}, _node(_node(ZERO, ZERO), ZERO)),
    # A Vector[uint16, 17] fills two chunks: sixteen elements, then one.
    ({"vector": [UINT16, 17]}, {"seq": [{"uint": 1}] * 17},
     _node(_chunk("0100" * 16), _chunk("0100"))),
    # The variable field of a container is rooted by its own rule, length included.
    (MIXED_PAIR, {"seq": [{"uint": 1}, {"seq": [{"uint": 2}, {"uint": 3}]}]},
     _node(_chunk("0100"), _node(_chunk("02000300"), _chunk("02")))),
]


@pytest.mark.parametrize(("ssz_type", "value", "root"), ROOTS)
def test_hash_tree_root(ssz_type, value, root: bytes) -> None:
    assert ssz.hash_tree_root(ssz_type, value) == root


@pytest.mark.parametrize(
    ("ssz_type", "value", "fault"),
    [
        # A ByteList[1] holds at most one byte.
        ({"byte_list": 1}, {"bytes": "0xaabb"}, "overLimit 1 2"),
        # A List[uint16, 4] holds at most four elements.
        ({"list": [UINT16, 4]}, {"seq": [{"uint": 1}] * 5}, "overLimit 4 5"),
        # A Bitvector[3] holds exactly three bits.
        ({"bitvector": 3}, {"bits": [True]}, "scope 3 1"),
        # Bytes are no unsigned integer.
        (UINT16, {"bytes": "0x0000"}, "typeMismatch"),
    ],
)
def test_hash_tree_root_rejects_value(ssz_type, value, fault: str) -> None:
    with pytest.raises(SszError, match="value rejected.*" + fault + "$"):
        ssz.hash_tree_root(ssz_type, value)


def test_hash_tree_root_rejects_type() -> None:
    # The root checks the type before it reads the value.
    with pytest.raises(SszError, match="type rejected.*uintWidth 3$"):
        ssz.hash_tree_root({"uint": 3}, {"uint": 0})
