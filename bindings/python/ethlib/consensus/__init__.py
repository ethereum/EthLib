"""The consensus layer: the presets, the configurations and the parameters at a fork.

A preset or a configuration is named "mainnet" or "minimal".
A fork is named as in the Lean type of forks, such as "phase0", "altair" or "pectra".

Each function returns a dict from the names of the source to their values.
An integer is an int, and a byte string is "0x" and lowercase hex.
An unknown name raises ConsensusError, a ValueError with code 0.
"""

import json

from ..errors import ConsensusError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ..cryptography import _native


def _value(value):
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


__all__ = ["preset", "config", "parameters", "ConsensusError"]
