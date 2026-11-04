"""The activation of each fork on the execution chain of mainnet."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ..cryptography import _native


def mainnet_active_fork(number: int, timestamp: int) -> str | None:
    """The fork active on mainnet at a block with this number and timestamp, if any."""
    name = _native.mainnet_active_fork(number, timestamp)
    return name.decode() if name else None


__all__ = ["mainnet_active_fork"]
