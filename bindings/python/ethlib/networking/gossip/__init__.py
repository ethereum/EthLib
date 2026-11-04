"""The message ID of a gossip message."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


def message_id_phase0(data: bytes) -> bytes:
    """The 20-byte message ID of Phase 0, from the data of the message."""
    return _native.gossip_message_id_phase0(data)


def message_id_altair(topic: bytes, data: bytes) -> bytes:
    """The 20-byte message ID from Altair on, from the topic and the data of the message."""
    return _native.gossip_message_id_altair(topic, data)
