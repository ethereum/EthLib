"""Ethereum Node Records, from EIP-778, with the "v4" identity scheme.

- A record is its RLP bytes, at most MAX_RECORD_SIZE bytes long.
- Its text form is "enr:", then the unpadded URL-safe base64 of those bytes.

Each function decodes the record first.
A record that the decoder rejects raises ValueError, and so does a malformed text.
"""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native

MAX_RECORD_SIZE = _native.ENR_MAX_RECORD_SIZE


def from_text(text: str) -> bytes:
    """The RLP bytes of a record in text form."""
    return _native.enr_from_text(text)


def seq(record: bytes) -> int:
    """The sequence number of a record."""
    return _native.enr_seq(record)


def verify_v4(record: bytes) -> bool:
    """Whether the record names the "v4" scheme and its signature verifies under its public key.

    A high s is accepted, since EIP-778 adds no low-s rule.
    """
    return _native.enr_verify_v4(record)


def node_id(record: bytes) -> bytes:
    """The 32-byte node ID of a "v4" record: the Keccak-256 hash of the x and y of its key.

    It does not check the signature.
    """
    return _native.enr_node_id(record)


__all__ = ["MAX_RECORD_SIZE", "from_text", "seq", "verify_v4", "node_id"]
