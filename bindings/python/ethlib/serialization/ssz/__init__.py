"""Simple Serialize, on types and values written as tagged JSON objects."""

import json

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native


def _dump(document) -> bytes:
    return json.dumps(document, separators=(",", ":")).encode()


def serialize(ssz_type, value) -> bytes:
    """The SSZ bytes of a value of a type, such as serialize({"uint": 2}, {"uint": 258})."""
    return _native.ssz_serialize(_dump(ssz_type), _dump(value))


def deserialize(ssz_type, data: bytes):
    """The value that SSZ bytes hold for a type, in the form that serialize takes."""
    return json.loads(_native.ssz_deserialize(_dump(ssz_type), data))


def hash_tree_root(ssz_type, value) -> bytes:
    """The 32-byte hash tree root of a value of a type, in the form that serialize takes."""
    return _native.ssz_hash_tree_root(_dump(ssz_type), _dump(value))
