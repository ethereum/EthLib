"""Block headers and blocks of the execution layer, at each fork.

A fork is the name of its case in the Lean fork type, such as "london" or "shapella".
A header or a block is its RLP bytes.

Each function decodes at the fork first.
An input that the decoder rejects raises ValueError, and so does an unknown fork.
"""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


def header_hash(fork: str, header: bytes) -> bytes:
    """The Keccak-256 hash of a header, which must hold exactly the fields of the fork."""
    return _native.block_header_hash(fork, header)


def reencode(fork: str, block: bytes) -> bytes:
    """The RLP bytes of a block, decoded at the fork and encoded again.

    Each transaction stays an RLP item, so the result equals the input for every block that
    the decoder accepts.
    """
    return _native.block_reencode(fork, block)


__all__ = ["header_hash", "reencode"]
