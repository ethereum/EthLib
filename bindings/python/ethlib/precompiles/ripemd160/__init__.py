"""The RIPEMD-160 precompile at address `0x03`."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native

RIPEMD160_OUTPUT_BYTES = _native.RIPEMD160_OUTPUT_BYTES


def ripemd160(data: bytes) -> bytes:
    """The output of the precompile on the call data.

    It is the RIPEMD-160 digest of the data, left-padded with zero bytes to 32 bytes.
    """
    return _native.ripemd160(data)


__all__ = ["ripemd160", "RIPEMD160_OUTPUT_BYTES"]
