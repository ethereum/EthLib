"""Simple Serialize, on types and values in their tagged form."""

from collections.abc import Sequence
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


def get_generalized_index(ssz_type: str | dict[str, Any], *path: int | str) -> int:
    """The generalized index that a path of positions, field names or "__len__" selects."""
    return _native.ssz_generalized_index(ssz_type, list(path))


def compute_merkle_proof(
    ssz_type: str | dict[str, Any], value: dict[str, Any], index: int
) -> list[bytes]:
    """The siblings on the path from a generalized index of a value up to its root, bottom first."""
    return _native.ssz_merkle_proof(ssz_type, value, index)


def merkleize_chunks(chunks: Sequence[bytes], limit: int | None = None) -> bytes:
    """The root of 32-byte chunks, padded to a power of two at least the limit or else the count."""
    return _native.ssz_merkleize_chunks(list(chunks), limit)
