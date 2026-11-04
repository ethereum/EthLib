"""Recursive Length Prefix, the strict encoding of byte strings and nested lists."""

from typing import Union

from ...errors import RlpError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native

Item = Union[bytes, list["Item"]]


def encode(item: Item) -> bytes:
    """The RLP encoding of an item."""
    return _native.rlp_encode(item)


def decode(data: bytes) -> Item:
    """The item that the bytes encode, if they encode exactly one item."""
    return _native.rlp_decode(data)


def _scalar(item: Item) -> int:
    # A scalar is its bytes in base 256, most significant first.
    assert isinstance(item, bytes)
    return int.from_bytes(item, "big")


def decode_as(kind: str, data: bytes):
    """The value of one type that the bytes encode.

    The kinds, and the Python value of each:

    - "nat": an int, without bound;
    - "u256" and "uint64": an int below 2^256 or 2^64;
    - "bool": a bool;
    - "address": 20 bytes;
    - "recipient": 20 bytes, or None for a contract creation;
    - "list_nat": a list of int.
    """
    item = _native.rlp_decode_as(kind, data)
    if kind in ("nat", "u256", "uint64"):
        return _scalar(item)
    if kind == "bool":
        return _scalar(item) == 1
    if kind == "recipient":
        return item or None
    if kind == "list_nat":
        assert isinstance(item, list)
        return [_scalar(x) for x in item]
    return item
