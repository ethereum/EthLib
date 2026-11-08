"""Simple Serialize, on types and values in their tagged form."""

from typing import Any

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native


def serialize(ssz_type: str | dict[str, Any], value: dict[str, Any]) -> bytes:
    """The SSZ bytes of a value of a type, for example {"uint": 258} of type {"uint": 2}."""
    return _native.ssz_serialize(ssz_type, value)


def deserialize(ssz_type: str | dict[str, Any], data: bytes) -> dict[str, Any]:
    """The value that SSZ bytes hold for a type, in the form that serialize takes."""
    return _native.ssz_deserialize(ssz_type, data)


def hash_tree_root(ssz_type: str | dict[str, Any], value: dict[str, Any]) -> bytes:
    """The 32-byte hash tree root of a value of a type, in the form that serialize takes."""
    return _native.ssz_hash_tree_root(ssz_type, value)
