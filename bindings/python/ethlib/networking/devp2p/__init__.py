"""The messages of the devp2p "p2p" capability: Hello, Disconnect, Ping and Pong."""

from ...errors import Devp2pError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native


def decode_message(snappy: bool, frame_data: bytes) -> bytes:
    """The uncompressed frame data, message ID then RLP list, of the message in `frame_data`."""
    return _native.devp2p_decode_message(snappy, frame_data)


def encode_message(snappy: bool, plain: bytes) -> bytes:
    """The frame data of the message in the uncompressed frame data `plain`."""
    return _native.devp2p_encode_message(snappy, plain)


__all__ = ["Devp2pError", "decode_message", "encode_message"]
