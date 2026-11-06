"""The ssz_snappy encoding of consensus-layer requests and responses."""

from typing import NamedTuple

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import ReqRespError

# A payload is a varint of the SSZ length, then a Snappy framed stream of the SSZ bytes.
# A response chunk is a response code, then context bytes, then a payload.
#
# Each function takes the whole message.
# A message that the decoder rejects raises `ReqRespError`, a `ValueError` with a code.
MAX_PAYLOAD_SIZE = _native.REQRESP_MAX_PAYLOAD_SIZE
MAX_ERROR_MESSAGE_SIZE = _native.REQRESP_MAX_ERROR_MESSAGE_SIZE


class ResponseChunk(NamedTuple):
    """One response chunk: its code, its context bytes and its SSZ bytes."""

    code: int
    context: bytes
    payload: bytes


def max_compressed_len(n: int) -> int:
    """The largest Snappy-compressed size of n bytes: 32 + n + n // 6."""
    return _native.reqresp_max_compressed_len(n)


def decode_payload(type_min: int, type_bound: int, data: bytes) -> bytes:
    """The SSZ bytes of a payload whose SSZ type encodes to type_min through type_bound bytes."""
    return _native.reqresp_decode_payload(type_min, type_bound, data)


def decode_response_chunk(
    context_bytes: int, type_min: int, type_bound: int, data: bytes
) -> ResponseChunk:
    """
    One response chunk, for a method that sends context_bytes context bytes on success.

    An error chunk carries no context bytes, and its payload is the error message.
    """
    raw = _native.reqresp_decode_response_chunk(context_bytes, type_min, type_bound, data)
    code = raw[0]
    n = context_bytes if code == 0 else 0
    return ResponseChunk(code, raw[1 : 1 + n], raw[1 + n :])


__all__ = [
    "ReqRespError",
    "MAX_PAYLOAD_SIZE",
    "MAX_ERROR_MESSAGE_SIZE",
    "ResponseChunk",
    "max_compressed_len",
    "decode_payload",
    "decode_response_chunk",
]
