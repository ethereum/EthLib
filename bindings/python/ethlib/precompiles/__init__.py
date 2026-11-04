"""The EVM precompiled contracts.

`run` calls any of the 18 precompiles of Bogota by its address.

The subpackages expose some precompiles with their sizes and prices.
"""

from ..errors import PrecompileError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ..cryptography import _native

ADDRESSES = (
    0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09,
    0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11, 0x100,
)


def run(address: int, data: bytes, gas: int) -> bytes:
    """The output of the precompile at the address on the call data, with the gas given.

    Raises PrecompileError, a ValueError, when the call fails or when no precompile has the address.

    Its code names the precompile that failed, and code 0 means no precompile has the address.
    """
    return _native.precompile_run(address, data, gas)


__all__ = ["ADDRESSES", "run", "ecrecover", "modexp", "ripemd160", "sha256", "PrecompileError"]
