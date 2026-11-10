"""yamux frames: a 12-byte header of version 0, type, flags, stream ID and length, then data."""

from dataclasses import dataclass
from enum import Enum

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import YamuxError as YamuxError


class Kind(Enum):
    """The type of a frame, which says what its length means."""

    DATA = "data"
    WINDOW_UPDATE = "window_update"
    PING = "ping"
    GO_AWAY = "go_away"


@dataclass(frozen=True, slots=True, kw_only=True)
class Frame:
    """One frame: the header fields after the version, and the data that a data frame carries."""

    kind: Kind
    flags: int
    stream_id: int
    # The data size of a data frame; a window delta, a ping value or a go-away code otherwise.
    length: int
    data: bytes = b""


def encode(frame: Frame) -> bytes:
    """The bytes of a frame; data of a size that its kind and length forbid raises YamuxError."""
    return _native.yamux_encode(
        {
            "kind": frame.kind.value,
            "flags": frame.flags,
            "stream_id": frame.stream_id,
            "length": frame.length,
            "data": frame.data,
        }
    )


def decode(data: bytes) -> tuple[Frame, bytes]:
    """The frame at the start of the bytes, and the bytes after it."""
    value, rest = _native.yamux_decode(data)
    frame = Frame(
        kind=Kind(value["kind"]),
        flags=value["flags"],
        stream_id=value["stream_id"],
        length=value["length"],
        data=value["data"],
    )
    return frame, rest


__all__ = ["Frame", "Kind", "YamuxError", "decode", "encode"]
