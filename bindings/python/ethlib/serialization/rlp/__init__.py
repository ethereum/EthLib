"""Recursive Length Prefix, the strict encoding of byte strings and nested lists."""

from typing import Any

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import RlpError as RlpError

Item = bytes | list["Item"]


def encode(item: bytes | list[Any]) -> bytes:
    """The RLP encoding of an item."""
    # The elements are Any, not Item: a list is invariant, so a list[bytes] is not a list[Item].
    return _native.rlp_encode(item)


def decode(data: bytes) -> Any:
    """The item that the bytes encode, if they encode exactly one item."""
    # The result is Any, not Item: the caller reads it in the shape that its schema gives.
    return _native.rlp_decode(data)


def _scalar(item: Item) -> int:
    # A scalar is its bytes in base 256, most significant first.
    assert isinstance(item, bytes)
    return int.from_bytes(item, "big")


def decode_as(kind: str, data: bytes):
    """
    The value of one type that the bytes encode.

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
