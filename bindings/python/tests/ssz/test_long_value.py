"""SSZ of long values, which once overflowed the stack or took quadratic time."""

from ethlib.serialization import ssz

BYTE_LIST = {"byte_list": 2**40}
UINT64_LIST = {"list": [{"uint": 8}, 2**40]}


def test_long_byte_list() -> None:
    data = bytes(range(256)) * (4 * 4096)
    assert ssz.serialize(BYTE_LIST, {"bytes": "0x" + data.hex()}) == data


def test_long_uint64_list() -> None:
    count = 50_000
    value = {"seq": [{"uint": i} for i in range(count)]}
    expected = b"".join(i.to_bytes(8, "little") for i in range(count))
    assert ssz.serialize(UINT64_LIST, value) == expected


def test_many_variable_elements() -> None:
    # A list of 200 000 empty byte lists: an offset table and no bodies, on the main thread.
    count = 200_000
    kind = {"list": [{"byte_list": 2**30}, 2**20]}
    data = (4 * count).to_bytes(4, "little") * count
    value = ssz.deserialize(kind, data)
    assert value == {"seq": [{"bytes": "0x"}] * count}
    assert ssz.serialize(kind, value) == data
    assert len(ssz.hash_tree_root(kind, value)) == 32


def test_many_fixed_elements() -> None:
    count = 200_000
    value = {"seq": [{"uint": i} for i in range(count)]}
    data = b"".join(i.to_bytes(8, "little") for i in range(count))
    assert ssz.serialize(UINT64_LIST, value) == data
    assert ssz.deserialize(UINT64_LIST, data) == value
