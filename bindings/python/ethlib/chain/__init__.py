"""The activation of each fork on the execution chains of mainnet and Hoodi."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ..cryptography import _native


def mainnet_active_fork(number: int, timestamp: int) -> str | None:
    """The fork active on mainnet at a block with this number and timestamp, if any."""
    name = _native.mainnet_active_fork(number, timestamp)
    return name.decode() if name else None


def hoodi_active_fork(number: int, timestamp: int) -> str | None:
    """The fork active on Hoodi at a block with this number and timestamp, if any."""
    name = _native.hoodi_active_fork(number, timestamp)
    return name.decode() if name else None


__all__ = ["hoodi_active_fork", "mainnet_active_fork"]
