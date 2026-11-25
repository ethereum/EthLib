"""The forks and blob schedules of mainnet, Hoodi, Sepolia and a configured chain."""

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


def sepolia_active_fork(number: int, timestamp: int) -> str | None:
    """The fork active on Sepolia at a block with this number and timestamp, if any."""
    return _native.sepolia_active_fork(number, timestamp)


def chain_config(name: str) -> dict[str, Any]:
    """The configuration of mainnet, Hoodi or Sepolia, as `active_fork` takes it."""
    return _native.chain_config(name)


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
    "chain_config",
    "execution_blob_schedule",
    "hoodi_active_fork",
    "mainnet_active_fork",
    "sepolia_active_fork",
    "write_execution_config",
]
