"""The EVM precompiled contracts of every fork, by address."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import PrecompileError

ADDRESSES = (
    0x01,
    0x02,
    0x03,
    0x04,
    0x05,
    0x06,
    0x07,
    0x08,
    0x09,
    0x0A,
    0x0B,
    0x0C,
    0x0D,
    0x0E,
    0x0F,
    0x10,
    0x11,
    0x100,
)


def run(fork: str, address: int, data: bytes, gas: int) -> bytes:
    """The output of the precompile at the address, on the call data with the gas, at the fork."""
    return _native.precompile_run(fork, address, data, gas)


def price(fork: str, address: int, data: bytes) -> int:
    """The gas that the precompile at the address charges for the call data, at the fork."""
    return int.from_bytes(_native.precompile_price(fork, address, data), "big")


__all__ = ["ADDRESSES", "run", "price", "PrecompileError"]
