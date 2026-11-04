"""The packets of the Node Discovery Protocol v4."""

from ...errors import Discv4Error

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


def decode(packet: bytes) -> bytes:
    """The hash, the sender's 64-byte key and the content of the packet `packet`."""
    return _native.discv4_decode(packet)


def encode(key: bytes, content: bytes) -> bytes:
    """The packet with the content `content`, packet type then data, signed with `key`."""
    return _native.discv4_encode(key, content)


def record_signed_by(sender: bytes, record: bytes) -> bool:
    """Whether the RLP node record `record` is a valid "v4" record of the key `sender`."""
    return _native.discv4_record_signed_by(sender, record)


__all__ = ["Discv4Error", "decode", "encode", "record_signed_by"]
