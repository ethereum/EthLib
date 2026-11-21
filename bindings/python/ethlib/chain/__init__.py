"""The forks and blob schedules of the execution chains of mainnet, Hoodi and a configured chain."""

from typing import Any

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import ChainError


def mainnet_active_fork(number: int, timestamp: int) -> str | None:
    """The fork active on mainnet at a block with this number and timestamp, if any."""
    return _native.mainnet_active_fork(number, timestamp)


def hoodi_active_fork(number: int, timestamp: int) -> str | None:
    """The fork active on Hoodi at a block with this number and timestamp, if any."""
    return _native.hoodi_active_fork(number, timestamp)


def active_fork(config: dict[str, Any], number: int, timestamp: int) -> str | None:
    """The fork active on a configured chain at a block with this number and timestamp, if any."""
    return _native.active_fork(config, number, timestamp)


def execution_blob_schedule(
    base: dict[str, Any], config: dict[str, Any], number: int, timestamp: int
) -> tuple[int, int, int] | None:
    """The blob schedule at a block, from a configuration and a client configuration file."""
    return _native.execution_blob_schedule(base, config, number, timestamp)


def write_execution_config(config: dict[str, Any]) -> dict[str, Any]:
    """The fork times and blob schedules of a configuration, as a client configuration file."""
    return _native.write_execution_config(config)


__all__ = [
    "ChainError",
    "active_fork",
    "execution_blob_schedule",
    "hoodi_active_fork",
    "mainnet_active_fork",
    "write_execution_config",
]
