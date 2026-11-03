"""The SHA-256 precompile at address `0x02`.

- The price is `60 + 12 * ceil(len(data) / 32)`.
- A call with too little gas raises ValueError.
"""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native

SHA256_PRECOMPILE_OUTPUT_BYTES = _native.SHA256_PRECOMPILE_OUTPUT_BYTES


def sha256(data: bytes, gas: int) -> bytes:
    """The output of the precompile on the call data, with the gas given.

    It is the 32-byte SHA-256 digest of the whole call data.

    Raises ValueError when the gas is below the price.
    """
    return _native.sha256_precompile(data, gas)


def gas_cost(data: bytes) -> int:
    """The gas the precompile charges for the call data."""
    return _native.sha256_precompile_gas_cost(data)


__all__ = ["sha256", "gas_cost", "SHA256_PRECOMPILE_OUTPUT_BYTES"]
