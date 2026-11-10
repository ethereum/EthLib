"""Gossip on the consensus layer: the message ID, the payload of a message and the RPC."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native


def message_id(fork: str, topic: bytes, data: bytes) -> bytes:
    """The 20-byte message ID of a message on a topic of a fork."""
    return _native.gossip_message_id(fork, topic, data)


def decode_payload(type_bound: int, data: bytes) -> bytes:
    """The SSZ bytes of the data of a message, given the size bound of its SSZ type."""
    return _native.gossip_decode_payload(type_bound, data)
