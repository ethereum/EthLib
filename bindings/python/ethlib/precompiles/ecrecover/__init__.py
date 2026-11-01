"""The ECRECOVER precompile at address `0x01`, as of the BPO2 fork.

- The output is the signer's address, left-padded to 32 bytes, or empty for a rejected signature.
- A call with too little gas raises ValueError.
"""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native

ECRECOVER_GAS = _native.ECRECOVER_GAS


def ecrecover(data: bytes, gas: int) -> bytes:
    """The output of the precompile on the call data, with the gas given.

    Raises ValueError when the gas is below the price.
    """
    return _native.ecrecover(data, gas)


__all__ = ["ecrecover", "ECRECOVER_GAS"]
