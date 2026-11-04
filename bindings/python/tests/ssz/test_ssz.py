"""SSZ against values whose bytes are worked out by hand from the SSZ rules."""

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
