"""The shared Python shapes of QUIC packet headers and frames."""

from typing import Literal, TypeAlias, TypedDict

# The packet types that carry frames, RFC 9000 §12.4, Table 3.
PacketType: TypeAlias = Literal["initial", "zero_rtt", "handshake", "one_rtt"]

# A header is a tuple: its packet type, then its connection IDs and other fields.
# Width is the two-bit packet-number length, 0 to 3 for 1 to 4 bytes.
# The number is the truncated packet number, and the Length counts it and the payload.
Header: TypeAlias = (
    tuple[Literal["initial"], list[int], list[int], list[int], int, int, int]
    | tuple[Literal["zero_rtt", "handshake"], list[int], list[int], int, int, int]
    | tuple[Literal["one_rtt"], list[int], bool, bool, int, int]
    | tuple[Literal["retry"], list[int], list[int], list[int], bytes, int]
    | tuple[Literal["version_negotiation"], list[int], list[int], int, list[int]]
)


class Ack(TypedDict):
    """The fields of an ACK frame, RFC 9000 §19.3."""

    largest: int
    delay: int
    first_range: int
    ranges: list[tuple[int, int]]
    ecn: tuple[int, int, int] | None


# A frame is its name alone, or a tuple of its name and its fields in wire order.
Frame: TypeAlias = (
    Literal["padding", "ping", "handshake_done"]
    | tuple[Literal["ack"], Ack]
    | tuple[Literal["reset_stream"], int, int, int]
    | tuple[Literal["stop_sending", "max_stream_data", "stream_data_blocked"], int, int]
    | tuple[Literal["crypto"], int, list[int]]
    | tuple[Literal["new_token"], list[int]]
    | tuple[Literal["stream"], int, int | None, bool, bool, list[int]]
    | tuple[Literal["max_data", "data_blocked", "retire_connection_id"], int]
    | tuple[Literal["max_streams", "streams_blocked"], bool, int]
    | tuple[Literal["new_connection_id"], int, int, list[int], bytes]
    | tuple[Literal["path_challenge", "path_response"], bytes]
    | tuple[Literal["connection_close"], int, int | None, list[int]]
)


__all__ = ["Ack", "Frame", "Header", "PacketType"]
