"""Gossip on the consensus layer: the message ID and the payload of a message."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


def message_id(fork: str, topic: bytes, data: bytes) -> bytes:
    """The 20-byte message ID of a message on a topic of a fork."""
    return _native.gossip_message_id(fork.encode(), topic, data)


def decode_payload(type_bound: int, data: bytes) -> bytes:
    """The SSZ bytes of the data of a message, given the size bound of its SSZ type."""
    return _native.gossip_decode_payload(type_bound, data)
