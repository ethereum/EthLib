"""The IDENTITY precompile at address `0x04`, as of Amsterdam, the execution fork of Glamsterdam.

- The output is the call data, byte for byte.
- The price is `15 + 3 * ceil(len(data) / 32)`.
- A call with too little gas raises ValueError.
- The gas crosses into Lean as a 64-bit integer, an interface limit of the bindings.
  Execution-specs counts gas without a bound.
"""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


def identity(data: bytes, gas: int) -> bytes:
    """The output of the precompile on the call data, with the gas given.

    It is the call data itself.

    Raises ValueError when the gas is below the price.
    Raises OverflowError when the gas is negative or not below 2^64.
    Raises TypeError when the data is not bytes or the gas is not an int.
    """
    return _native.identity(data, gas)


def gas_cost(data: bytes) -> int:
    """The gas that the precompile charges for the call data.

    Raises TypeError when the data is not bytes.
    """
    return _native.identity_gas_cost(data)


__all__ = ["identity", "gas_cost"]
