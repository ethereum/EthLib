"""mplex frames: a header of stream ID and flag, a length, then the data."""

from dataclasses import dataclass
from enum import Enum

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import MplexError as MplexError


class Flag(Enum):
    """What a frame does to its stream, from "Flag Values" of the mplex source."""

    NEW_STREAM = "new_stream"
    MESSAGE_RECEIVER = "message_receiver"
    MESSAGE_INITIATOR = "message_initiator"
    CLOSE_RECEIVER = "close_receiver"
    CLOSE_INITIATOR = "close_initiator"
    RESET_RECEIVER = "reset_receiver"
    RESET_INITIATOR = "reset_initiator"


@dataclass(frozen=True, slots=True, kw_only=True)
class Frame:
    """One frame: its stream, its flag and its data."""

    stream_id: int
    flag: Flag
    data: bytes = b""


def encode(frame: Frame) -> bytes:
    """The bytes of a frame; a frame outside the mplex rules raises MplexError."""
    return _native.mplex_encode(
        {"stream_id": frame.stream_id, "flag": frame.flag.value, "data": frame.data}
    )


def decode(data: bytes) -> tuple[Frame, bytes]:
    """The frame at the start of the bytes, and the bytes after it."""
    value, rest = _native.mplex_decode(data)
    frame = Frame(stream_id=value["stream_id"], flag=Flag(value["flag"]), data=value["data"])
    return frame, rest


__all__ = ["Flag", "Frame", "MplexError", "decode", "encode"]
