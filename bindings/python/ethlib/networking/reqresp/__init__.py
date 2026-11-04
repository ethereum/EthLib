"""The ssz_snappy encoding of consensus-layer requests and responses.

- A payload is a varint of the SSZ length, then a Snappy framed stream of the SSZ bytes.
- A response chunk is a response code, then context bytes, then a payload.

Each function takes the whole message.
A fork is named as on the timeline of EthLib, such as "bellatrix".
The payload cap depends on the fork: 1 MiB before Bellatrix and 10 MiB from Bellatrix on.
A message that the decoder rejects raises ReqRespError, a ValueError with a code.
An unknown fork name raises ReqRespError with code 0.
"""

from typing import NamedTuple

from ...errors import ReqRespError

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native

MAX_ERROR_MESSAGE_SIZE = _native.REQRESP_MAX_ERROR_MESSAGE_SIZE


class ResponseChunk(NamedTuple):
    """One response chunk: its code, its context bytes and its SSZ bytes."""

    code: int
    context: bytes
    payload: bytes


def max_compressed_len(n: int) -> int:
    """The largest Snappy-compressed size of n bytes: 32 + n + n // 6."""
    return _native.reqresp_max_compressed_len(n)


def max_payload_size(fork: str) -> int:
    """The largest payload, in SSZ bytes, that a request or a response chunk may hold at a fork."""
    return _native.reqresp_max_payload_size(fork)


def decode_payload(fork: str, type_bound: int, data: bytes) -> bytes:
    """The SSZ bytes of a payload whose SSZ type allows at most type_bound bytes."""
    return _native.reqresp_decode_payload(fork, type_bound, data)


def decode_response_chunk(
    fork: str, context_bytes: int, type_bound: int, data: bytes
) -> ResponseChunk:
    """One response chunk, for a method that sends context_bytes context bytes on success.

    An error chunk carries no context bytes, and its payload is the error message.
    """
    raw = _native.reqresp_decode_response_chunk(fork, context_bytes, type_bound, data)
    code = raw[0]
    n = context_bytes if code == 0 else 0
    return ResponseChunk(code, raw[1 : 1 + n], raw[1 + n :])


__all__ = [
    "ReqRespError",
    "MAX_ERROR_MESSAGE_SIZE",
    "ResponseChunk",
    "max_compressed_len",
    "max_payload_size",
    "decode_payload",
    "decode_response_chunk",
]
