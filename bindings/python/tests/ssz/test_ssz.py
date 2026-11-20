"""SSZ against values whose bytes and roots are worked out by hand from the SSZ rules."""

import hashlib

import pytest

from ethlib.errors import SszError
from ethlib.serialization import ssz
from raising import raises

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
    (
        MIXED_PAIR,
        {"seq": [{"uint": 1}, {"seq": [{"uint": 2}, {"uint": 3}]}]},
        "01000600000002000300",
    ),
    # Opaque bytes of a fixed length are written as they are.
    ({"byte_vector": 2}, {"bytes": "0x0102"}, "0102"),
    # A variable field of opaque bytes takes an offset, like any variable field.
    # The body starts at byte 5, after the one byte of a and the four of the offset.
    (
        {"container": [["a", {"uint": 1}], ["b", {"byte_list": 4}]]},
        {"seq": [{"uint": 7}, {"bytes": "0xaabb"}]},
        "0705000000aabb",
    ),
]


@pytest.mark.parametrize(("ssz_type", "value", "encoded"), CASES)
def test_serialize(ssz_type, value, encoded: str) -> None:
    assert ssz.serialize(ssz_type, value) == bytes.fromhex(encoded)


@pytest.mark.parametrize(("ssz_type", "value", "encoded"), CASES)
def test_deserialize(ssz_type, value, encoded: str) -> None:
    assert ssz.deserialize(ssz_type, bytes.fromhex(encoded)) == value


def test_bool_two_rejected() -> None:
    # A byte other than 00 and 01 is no boolean.
    with raises(ValueError, "input rejected: EthLib.Serialization.Ssz.Err.notABit 2"):
        ssz.deserialize("bool", b"\x02")


def test_bad_hex_rejected() -> None:
    with raises(ValueError, "value: bytes must be 0x and hex digits"):
        ssz.serialize({"byte_vector": 2}, {"bytes": "0xzz"})


@pytest.mark.parametrize("sequence", [list, tuple])
def test_equal_width_native_bytes(sequence) -> None:
    rows = [bytes((i, i + 1, i + 2)) for i in range(64)]
    value = {"seq": sequence({"bytes": row} for row in rows)}
    concatenated = b"".join(rows)
    assert ssz.serialize({"vector": [{"byte_vector": 3}, len(rows)]}, value) == concatenated

    offsets = b"".join((4 * len(rows) + 3 * i).to_bytes(4, "little") for i in range(len(rows)))
    assert ssz.serialize({"vector": [{"byte_list": 3}, len(rows)]}, value) == offsets + concatenated


@pytest.mark.parametrize(
    ("width", "count", "fault"), [(2, 64, "scope 2 3"), (3, 63, "scope 63 64")]
)
def test_equal_width_native_bytes_reject_wrong_shape(width: int, count: int, fault: str) -> None:
    value = {"seq": [{"bytes": b"abc"} for _ in range(64)]}
    with raises(SszError, "value rejected: EthLib.Serialization.Ssz.Err." + fault):
        ssz.serialize({"vector": [{"byte_vector": width}, count]}, value)


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
    with raises(ValueError, "type rejected: EthLib.Serialization.Ssz.Err." + fault):
        ssz.deserialize(ssz_type, b"")


def test_unknown_type_rejected() -> None:
    # A type that names no SSZ type has code 0, which no SSZ error has.
    with raises(SszError, "type: unknown SSZ type float") as caught:
        ssz.serialize({"float": 4}, {"uint": 1})
    assert caught.value.code == 0


def _chunk(hex_bytes: str) -> bytes:
    """A 32-byte chunk: the given bytes, then zero bytes."""
    return bytes.fromhex(hex_bytes).ljust(32, b"\x00")


def _node(left: bytes, right: bytes) -> bytes:
    """The parent of two Merkle nodes, by the SHA-256 of hashlib."""
    return hashlib.sha256(left + right).digest()


def test_native_uint_sequence_root() -> None:
    count = 63
    values = {"seq": [{"uint": i} for i in range(count)]}
    encoded = b"".join(i.to_bytes(2, "little") for i in range(count))
    chunks = [encoded[i : i + 32].ljust(32, b"\x00") for i in range(0, len(encoded), 32)]
    contents = _node(_node(chunks[0], chunks[1]), _node(chunks[2], chunks[3]))
    expected = _node(contents, count.to_bytes(32, "little"))
    assert ssz.hash_tree_root({"list": [UINT16, 64]}, values) == expected


@pytest.mark.parametrize("operation", [ssz.serialize, ssz.hash_tree_root])
def test_native_uint_sequence_rejects_invalid_element(operation) -> None:
    kind = {"list": [UINT16, 64]}
    value = {"seq": [{"uint": 1}] * 63 + [{"uint": 2**16}]}
    with raises(SszError, "value rejected: EthLib.Serialization.Ssz.Err.typeMismatch"):
        operation(kind, value)
    with raises(SszError, "value rejected: EthLib.Serialization.Ssz.Err.overLimit 63 64"):
        operation({"list": [UINT16, 63]}, value)

    value["seq"][-1] = {"uint": -1}
    with raises(ValueError, "cannot pass a negative int to Lean"):
        operation(kind, value)


ZERO = _chunk("")


def test_native_byte_vector_root_pads_to_tree_width() -> None:
    nodes = [bytes((i,)) * 32 for i in range(33)]
    level = nodes + [ZERO] * 31
    while len(level) > 1:
        level = [_node(left, right) for left, right in zip(level[::2], level[1::2], strict=True)]
    value = {"seq": [{"bytes": node} for node in nodes]}
    assert ssz.hash_tree_root({"vector": [{"byte_vector": 32}, 33]}, value) == level[0]

    with raises(SszError, "value rejected: EthLib.Serialization.Ssz.Err.scope 32 33"):
        ssz.hash_tree_root({"vector": [{"byte_vector": 32}, 32]}, value)


@pytest.mark.parametrize("operation", [ssz.serialize, ssz.hash_tree_root])
def test_record_mutations_keep_conversion_error_order(operation) -> None:
    integer = {"uint": 2}
    kind = {"container": [("a", integer), ("b", {"byte_vector": 2}), ("c", UINT16)]}
    fields = [{"uint": 0x0102}, {"bytes": b"ab"}, {"uint": 3}]
    value = {"seq": fields}
    if operation is ssz.serialize:
        expected = bytes.fromhex("020161620300")
    else:
        expected = _node(_node(_chunk("0201"), _chunk("6162")), _node(_chunk("0300"), ZERO))
    assert operation(kind, value) == expected

    # Hex text uses the general converter and represents the same bytes.
    fields[1] = {"bytes": "0x6162"}
    assert operation(kind, value) == expected

    # The type error precedes a semantic error in the value.
    integer["uint"] = 3
    for wrong_bytes in (b"a", "0xzz"):
        fields[1] = {"bytes": wrong_bytes}
        with raises(SszError, "type rejected: EthLib.Serialization.Ssz.Err.uintWidth 3"):
            operation(kind, value)

    # Conversion of both arguments precedes decoding the type.
    fields[-1] = {"uint": -1}
    with raises(ValueError, "cannot pass a negative int to Lean"):
        operation(kind, value)


# Each type, value and its root, built by hand from the Merkleization rules of SSZ.
ROOTS = [
    # A basic value is its bytes, padded to one chunk, with no hashing.
    (UINT16, {"uint": 0x0102}, _chunk("0201")),
    ("bool", {"bool": True}, _chunk("01")),
    # A container of two fields roots the two field roots as leaves.
    (
        FIXED_PAIR,
        {"seq": [{"uint": 0x4567}, {"uint": 0x0123}]},
        _node(_chunk("6745"), _chunk("2301")),
    ),
    # A List[uint16, 4] packs into one chunk, and mixes in its length 2.
    (
        {"list": [UINT16, 4]},
        {"seq": [{"uint": 2}, {"uint": 3}]},
        _node(_chunk("02000300"), _chunk("02")),
    ),
    # A Bitlist[8] packs its bits without the closing bit, and mixes in the bit count 3.
    ({"bitlist": 8}, {"bits": [True, False, True]}, _node(_chunk("05"), _chunk("03"))),
    # A ByteList[33] has room for two chunks, so even an empty one roots a tree of depth 1.
    ({"byte_list": 33}, {"bytes": "0x"}, _node(_node(ZERO, ZERO), ZERO)),
    # A Vector[uint16, 17] fills two chunks: sixteen elements, then one.
    (
        {"vector": [UINT16, 17]},
        {"seq": [{"uint": 1}] * 17},
        _node(_chunk("0100" * 16), _chunk("0100")),
    ),
    # The variable field of a container is rooted by its own rule, length included.
    (
        MIXED_PAIR,
        {"seq": [{"uint": 1}, {"seq": [{"uint": 2}, {"uint": 3}]}]},
        _node(_chunk("0100"), _node(_chunk("02000300"), _chunk("02"))),
    ),
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
    with raises(SszError, "value rejected: EthLib.Serialization.Ssz.Err." + fault):
        ssz.hash_tree_root(ssz_type, value)


# A List[List[uint16, 4], 4], whose encoding starts with a table of four-byte offsets.
NESTED_LIST = {"list": [{"list": [UINT16, 4]}, 4]}


@pytest.mark.parametrize(
    ("ssz_type", "encoded", "fault"),
    [
        # A first offset of 2 points inside its own four-byte entry.
        (NESTED_LIST, "02000000", "offsetBelowTable 2"),
        # A first offset of 6 is no whole number of four-byte entries.
        (NESTED_LIST, "0600000000000000", "offsetUnaligned 6"),
        # A first offset of 12 lies past the 8 bytes of the encoding.
        (NESTED_LIST, "0c00000000000000", "offsetPastScope 12 8"),
        # The second body would start at 4, before the first one at 8.
        (NESTED_LIST, "0800000004000000", "offsetUnordered 8 4"),
        # The byte 0x09 of a Bitvector[3] sets bit 3, above the three declared bits.
        ({"bitvector": 3}, "09", "paddingBits 9"),
    ],
)
def test_deserialize_rejects_input(ssz_type, encoded: str, fault: str) -> None:
    with raises(SszError, "input rejected: EthLib.Serialization.Ssz.Err." + fault):
        ssz.deserialize(ssz_type, bytes.fromhex(encoded))


def test_hash_tree_root_rejects_type() -> None:
    # The root checks the type before it reads the value.
    with raises(SszError, "type rejected: EthLib.Serialization.Ssz.Err.uintWidth 3"):
        ssz.hash_tree_root({"uint": 3}, {"uint": 0})


def test_bytes_cross_as_hex() -> None:
    # A bytes value crosses as 0x and hex, the form that a str in the value gives.
    assert ssz.serialize({"byte_list": 4}, {"bytes": b"ab"}) == b"ab"
    assert ssz.serialize({"byte_list": 4}, {"bytes": "0x6162"}) == b"ab"


def test_deserialize_returns_a_dict() -> None:
    assert ssz.deserialize({"uint": 2}, b"\x02\x01") == {"uint": 258}


def test_type_of_another_form() -> None:
    with raises(SszError, "type: expected an object with one key") as info:
        ssz.serialize(5, {"uint": 1})  # ty: ignore[invalid-argument-type]
    assert info.value.code == 0


def test_data_of_another_form() -> None:
    with raises(SszError, "expected bytes") as info:
        ssz.deserialize("bool", "01")  # ty: ignore[invalid-argument-type]
    assert info.value.code == 0


def test_nesting_bound_of_the_converter() -> None:
    # The converter reads at most 64 levels below an argument.
    # A vector type takes two levels for each of its own, and a value one more than its type.
    def vector(depth: int) -> str | dict:
        return "bool" if depth == 0 else {"vector": [vector(depth - 1), 1]}

    def value(depth: int) -> dict:
        return {"bool": True} if depth == 0 else {"seq": [value(depth - 1)]}

    def container(depth: int) -> str | dict:
        return "bool" if depth == 0 else {"container": [["a", container(depth - 1)]]}

    message = "cannot pass a value nested deeper than 64 to Lean"
    assert ssz.serialize(vector(31), value(31)) == b"\x01"
    with raises(ValueError, message):
        ssz.serialize(vector(31), value(32))
    assert ssz.deserialize(vector(32), b"\x01") == value(32)
    with raises(ValueError, message):
        ssz.deserialize(vector(33), b"\x01")
    assert ssz.deserialize(container(21), b"\x01") == value(21)
    with raises(ValueError, message):
        ssz.deserialize(container(22), b"\x01")
