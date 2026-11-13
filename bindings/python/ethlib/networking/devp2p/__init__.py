"""The messages of the devp2p "p2p" capability: Hello, Disconnect, Ping and Pong."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from collections.abc import Sequence

from ethlib.cryptography import _native
from ethlib.errors import Devp2pError


def decode_message(snappy: bool, frame_data: bytes) -> bytes:
    """The uncompressed frame data, message ID then RLP list, of the message in `frame_data`."""
    return _native.devp2p_decode_message(snappy, frame_data)


def encode_message(snappy: bool, plain: bytes) -> bytes:
    """The frame data of the message in the uncompressed frame data `plain`."""
    return _native.devp2p_encode_message(snappy, plain)


def route(
    ours: Sequence[tuple[bytes, int]], theirs: Sequence[tuple[bytes, int]], message_id: int
) -> tuple[bytes, int, int] | None:
    """The shared eth or snap capability that holds a message ID, with the ID relative to it."""
    return _native.devp2p_route(list(ours), list(theirs), message_id)


def session(
    hello: bytes, frames: Sequence[bytes]
) -> list[tuple[str, str, bytes, int, int, bytes, bool]]:
    """The outcomes of the frames a session receives in turn, from before the peer's Hello."""
    return _native.devp2p_session(hello, list(frames))


__all__ = ["Devp2pError", "decode_message", "encode_message", "route", "session"]
