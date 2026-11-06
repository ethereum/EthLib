"""The activation of each fork on the execution chains of mainnet, Hoodi and a configured chain."""

import json

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import ChainError


def mainnet_active_fork(number: int, timestamp: int) -> str | None:
    """The fork active on mainnet at a block with this number and timestamp, if any."""
    name = _native.mainnet_active_fork(number, timestamp)
    return name.decode() if name else None


def hoodi_active_fork(number: int, timestamp: int) -> str | None:
    """The fork active on Hoodi at a block with this number and timestamp, if any."""
    name = _native.hoodi_active_fork(number, timestamp)
    return name.decode() if name else None


def active_fork(config: dict, number: int, timestamp: int) -> str | None:
    """The fork active on a configured chain at a block with this number and timestamp, if any."""
    name = _native.active_fork(json.dumps(config).encode(), number, timestamp)
    return name.decode() if name else None


__all__ = ["ChainError", "active_fork", "hoodi_active_fork", "mainnet_active_fork"]
