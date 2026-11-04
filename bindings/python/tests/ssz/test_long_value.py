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
