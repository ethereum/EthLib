"""The consensus layer: presets, configurations, containers, the shuffle and custody."""

import json
from typing import Any

from ..errors import ConsensusError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ..cryptography import _native


def _value(value: Any) -> Any:
    # The export writes every integer as a string of decimal digits.
    if isinstance(value, str) and not value.startswith("0x") and value.isdigit():
        return int(value)
    if isinstance(value, list):
        return [_value(item) for item in value]
    if isinstance(value, dict):
        return {key: _value(item) for key, item in value.items()}
    return value


def preset(name: str) -> dict:
    """The values of a preset, with the values that it derives from them."""
    return _value(json.loads(_native.consensus_preset(name)))


def config(name: str) -> dict:
    """The values of a configuration."""
    return _value(json.loads(_native.consensus_config(name)))


def parameters(name: str, fork: str) -> dict:
    """The values of a preset that a fork replaces, as they stand at the fork."""
    return _value(json.loads(_native.consensus_parameters(name, fork)))


def get_custody_groups(node_id: int, custody_group_count: int, name: str = "mainnet") -> list:
    """The sorted custody groups of a node, or ConsensusError when they cannot be selected."""
    if not 0 <= node_id < 2**256 or not 0 <= custody_group_count < 2**64:
        raise ValueError("node_id or custody_group_count is out of range")
    groups = _native.consensus_get_custody_groups(
        name, node_id.to_bytes(32, "big"), custody_group_count
    )
    return _value(json.loads(groups))


def compute_columns_for_custody_group(custody_group: int, name: str = "mainnet") -> list:
    """The columns of a custody group, or ConsensusError for a group out of range."""
    if not 0 <= custody_group < 2**64:
        raise ValueError("custody_group is out of range")
    columns = _native.consensus_compute_columns_for_custody_group(name, custody_group)
    return _value(json.loads(columns))


def ssz_static(name: str, fork: str, type_name: str, data: bytes) -> tuple[bytes, bytes]:
    """The root of the beacon container that SSZ bytes encode, and its bytes encoded again."""
    out = _native.consensus_ssz_static(name, fork, type_name, data)
    return out[:32], out[32:]


def compute_shuffled_permutation(count: int, seed: bytes, name: str = "mainnet") -> list:
    """The shuffled position of every index below the count."""
    return _value(json.loads(_native.consensus_compute_shuffled_permutation(name, count, seed)))


def compute_shuffled_index(index: int, count: int, seed: bytes, name: str = "mainnet") -> int:
    """The shuffled position of one index, or ConsensusError when it is not below the count."""
    return _native.consensus_compute_shuffled_index(name, index, count, seed)


__all__ = [
    "preset",
    "config",
    "parameters",
    "ConsensusError",
    "get_custody_groups",
    "compute_columns_for_custody_group",
    "ssz_static",
    "compute_shuffled_permutation",
    "compute_shuffled_index",
]
