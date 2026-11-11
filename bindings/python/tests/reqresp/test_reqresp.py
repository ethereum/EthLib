"""The ssz_snappy req/resp encoding against hand-built messages and a reference decoder."""

import random

import pytest

from ethlib.networking import reqresp
from raising import raises
from snappy_reference import CASES as SPEC_CASES, SpecCase, decode_block, spec_object

# Each message is built from the framing format of google/snappy and the protobuf varint.
# The framing format is framing_format.txt, so no value comes from the code under test.
# Each test names the rule that its message pins.

STREAM_IDENTIFIER = bytes([0xFF, 0x06, 0x00, 0x00]) + b"sNaPpY"


def _crc32c(data: bytes) -> int:
    # CRC-32C (Castagnoli), reflected polynomial 0x82f63b78, bit by bit.
    crc = 0xFFFFFFFF
    for byte in data:
        crc ^= byte
        for _ in range(8):
            crc = (crc >> 1) ^ (0x82F63B78 if crc & 1 else 0)
    return crc ^ 0xFFFFFFFF


def _masked_crc(data: bytes) -> int:
    crc = _crc32c(data)
    return ((((crc >> 15) | (crc << 17)) & 0xFFFFFFFF) + 0xA282EAD8) & 0xFFFFFFFF


def _chunk(chunk_type: int, body: bytes) -> bytes:
    return bytes([chunk_type]) + len(body).to_bytes(3, "little") + body


def _uncompressed(data: bytes, checksum: int | None = None) -> bytes:
    crc = _masked_crc(data) if checksum is None else checksum
    return _chunk(0x01, crc.to_bytes(4, "little") + data)


def _compressed_literal(data: bytes) -> bytes:
    # A Snappy block of one literal: the length as a varint, then the tag (len - 1) << 2.
    assert 0 < len(data) <= 60
    block = bytes([len(data), (len(data) - 1) << 2]) + data
    return _chunk(0x00, _masked_crc(data).to_bytes(4, "little") + block)


def _varint(n: int) -> bytes:
    out = bytearray()
    while n >= 0x80:
        out.append((n & 0x7F) | 0x80)
        n >>= 7
    out.append(n)
    return bytes(out)


PAYLOAD = bytes.fromhex("deadbeef")


def test_crc32c_check_value():
    # The check value of CRC-32C on the ASCII string "123456789".
    assert _crc32c(b"123456789") == 0xE3069283


def test_max_payload_size():
    # 10 MiB at every fork.
    assert reqresp.MAX_PAYLOAD_SIZE == 10 * 2**20


def test_max_compressed_len():
    # 32 + n + n // 6 at the payload cap of 10 MiB.
    assert reqresp.max_compressed_len(10 * 2**20) == 32 + 10485760 + 1747626
    assert reqresp.max_compressed_len(0) == 32


def test_max_compressed_len_overflow():
    with raises(ValueError, "bound on the compressed size is 2^64 or more"):
        reqresp.max_compressed_len(2**64 - 1)


def test_framed_payload_bytes():
    # deadbeef in one uncompressed chunk, written out in full.
    # The checksum 0x91a0ce90 is CRC-32C 0xf1dc778e, rotated right by 15 bits, plus 0xa282ead8.
    message = bytes.fromhex("04ff060000734e615070590108000090cea091deadbeef")
    assert message == _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    assert reqresp.decode_payload(0, 4, message) == PAYLOAD


def test_uncompressed_chunk():
    message = _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    assert reqresp.decode_payload(0, 100, message) == PAYLOAD


def test_compressed_chunk():
    message = _varint(4) + STREAM_IDENTIFIER + _compressed_literal(PAYLOAD)
    assert reqresp.decode_payload(0, 100, message) == PAYLOAD


def test_two_chunks():
    chunks = _uncompressed(PAYLOAD[:1]) + _uncompressed(PAYLOAD[1:])
    message = _varint(4) + STREAM_IDENTIFIER + chunks
    assert reqresp.decode_payload(0, 4, message) == PAYLOAD


def test_empty_payload():
    assert reqresp.decode_payload(0, 0, _varint(0) + STREAM_IDENTIFIER) == b""


def test_length_above_type_bound():
    message = _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    with raises(ValueError, "declared length 4 is above 3"):
        reqresp.decode_payload(0, 3, message)


def test_length_above_payload_cap():
    # A declared length of 10 MiB + 1 exceeds the cap, before any frame is read.
    message = _varint(10 * 2**20 + 1) + STREAM_IDENTIFIER
    with raises(ValueError, "declared length 10485761 is above 10485760"):
        reqresp.decode_payload(0, 2**30, message)


def test_length_at_payload_cap():
    # A declared length of 10 MiB passes the cap, and fails later: the stream is empty.
    message = _varint(10 * 2**20) + STREAM_IDENTIFIER
    with raises(ValueError, "payload has 0 bytes, not the declared 10485760"):
        reqresp.decode_payload(0, 2**30, message)


def test_length_below_type_minimum():
    # The header rule bounds the declared length below too, by the smallest encoding of the type.
    message = _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    with raises(ValueError, "declared length 4 is below 5"):
        reqresp.decode_payload(5, 100, message)


def test_length_at_type_minimum():
    message = _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    assert reqresp.decode_payload(4, 100, message) == PAYLOAD


def test_length_at_both_bounds():
    # A fixed-size type has one encoding size, so both bounds are equal.
    message = _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    assert reqresp.decode_payload(4, 4, message) == PAYLOAD


def test_empty_payload_below_type_minimum():
    with raises(ValueError, "declared length 0 is below 1"):
        reqresp.decode_payload(1, 100, _varint(0) + STREAM_IDENTIFIER)


def test_stream_shorter_than_declared():
    message = _varint(5) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    with raises(ValueError, "payload has 4 bytes, not the declared 5"):
        reqresp.decode_payload(0, 100, message)


def test_stream_longer_than_declared():
    message = _varint(3) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    with raises(ValueError, "payload has 4 bytes, not the declared 3"):
        reqresp.decode_payload(0, 100, message)


def test_compressed_bytes_at_the_bound():
    # Declared length 4 allows 32 + 4 + 4 // 6 = 36 bytes.
    # The identifier (10), a padding chunk of 4 + 10 and the data chunk (12) make 36.
    message = _varint(4) + STREAM_IDENTIFIER + _chunk(0xFE, bytes(10)) + _uncompressed(PAYLOAD)
    assert reqresp.decode_payload(0, 4, message) == PAYLOAD


def test_compressed_bytes_above_the_bound():
    # One more padding byte makes 37 bytes after the prefix.
    message = _varint(4) + STREAM_IDENTIFIER + _chunk(0xFE, bytes(11)) + _uncompressed(PAYLOAD)
    with raises(ValueError, "37 compressed bytes, more than 36"):
        reqresp.decode_payload(0, 4, message)


# A reader must reject any bytes that remain after it has read the declared n SSZ bytes.
# The reader stops at the chunk that completes n bytes, so any byte after it is rejected.
# That holds for chunks that add no bytes too: padding, skippable chunks and stream identifiers.
# An empty data chunk adds no bytes either.


@pytest.mark.parametrize(
    "after",
    [
        pytest.param(_chunk(0xFE, b""), id="padding"),
        pytest.param(_chunk(0x80, b"x"), id="skippable"),
        pytest.param(STREAM_IDENTIFIER, id="stream_identifier"),
        pytest.param(_uncompressed(b""), id="empty_data_chunk"),
        pytest.param(b"\x00", id="one_byte"),
        pytest.param(_uncompressed(b"\x01"), id="data_chunk"),
    ],
)
def test_bytes_after_the_payload(after: bytes):
    message = _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD) + after
    with raises(ValueError, f"{len(after)} bytes follow the last chunk of the payload"):
        reqresp.decode_payload(0, 100, message)


def test_bytes_after_a_compressed_payload():
    message = _varint(4) + STREAM_IDENTIFIER + _compressed_literal(PAYLOAD) + _chunk(0xFE, b"")
    with raises(ValueError, "4 bytes follow the last chunk of the payload"):
        reqresp.decode_payload(0, 100, message)


def test_last_chunk_past_the_length_with_bytes_after():
    # The length is checked before the bytes after the chunk, so the overshoot is reported.
    message = _varint(3) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD) + _chunk(0xFE, b"")
    with raises(ValueError, "payload has 4 bytes, not the declared 3"):
        reqresp.decode_payload(0, 100, message)


def test_bytes_after_an_empty_payload():
    # With n = 0 the reader reads the stream identifier alone, and a padding chunk after it remains.
    message = _varint(0) + STREAM_IDENTIFIER + _chunk(0xFE, bytes(18))
    with raises(ValueError, "22 bytes follow the last chunk of the payload"):
        reqresp.decode_payload(0, 0, message)


def test_chunks_before_the_last_data_chunk():
    # Chunks that add no bytes are read while bytes are still needed.
    padding = _chunk(0xFE, b"")
    message = _varint(4) + STREAM_IDENTIFIER + padding + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    assert reqresp.decode_payload(0, 100, message) == PAYLOAD


def test_response_chunk_with_bytes_after():
    # A padding chunk after the payload of a response chunk is rejected too.
    chunk = bytes([0]) + _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    with raises(ValueError, "4 bytes follow the last chunk of the payload"):
        reqresp.decode_response_chunk(0, 0, 100, chunk + _chunk(0xFE, b""))


def test_non_minimal_varint():
    message = bytes([0x84, 0x00]) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    with raises(ValueError, "length prefix is not a valid varint"):
        reqresp.decode_payload(0, 100, message)


def test_varint_over_ten_bytes():
    message = bytes([0x80] * 10 + [0x00]) + STREAM_IDENTIFIER
    with raises(ValueError, "length prefix is not a valid varint"):
        reqresp.decode_payload(0, 100, message)


def test_bad_checksum():
    message = _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD, checksum=0)
    with raises(ValueError, "payload is not a valid Snappy framed stream"):
        reqresp.decode_payload(0, 100, message)


def test_missing_stream_identifier():
    message = _varint(4) + _uncompressed(PAYLOAD)
    with raises(ValueError, "payload is not a valid Snappy framed stream"):
        reqresp.decode_payload(0, 100, message)


def test_success_chunk_with_fork_digest():
    digest = bytes.fromhex("6a95a1a9")
    chunk = bytes([0]) + digest + _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    assert reqresp.decode_response_chunk(4, 0, 100, chunk) == (0, digest, PAYLOAD)


def test_success_chunk_without_context():
    chunk = bytes([0]) + _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    assert reqresp.decode_response_chunk(0, 0, 100, chunk) == (0, b"", PAYLOAD)


def test_error_chunk():
    # An error carries no context bytes, even on a method that sends a fork digest.
    message = b"bad request"
    chunk = bytes([1]) + _varint(len(message)) + STREAM_IDENTIFIER + _uncompressed(message)
    assert reqresp.decode_response_chunk(4, 0, 0, chunk) == (1, b"", message)


def test_request_specific_code():
    chunk = bytes([200]) + _varint(1) + STREAM_IDENTIFIER + _uncompressed(b"x")
    assert reqresp.decode_response_chunk(4, 0, 0, chunk) == (200, b"", b"x")


def test_error_message_too_long():
    message = bytes(reqresp.MAX_ERROR_MESSAGE_SIZE + 1)
    chunk = bytes([2]) + _varint(len(message)) + STREAM_IDENTIFIER + _uncompressed(message)
    with raises(ValueError, "declared length 257 is above 256"):
        reqresp.decode_response_chunk(0, 0, 1000, chunk)


def test_context_truncated():
    with raises(ValueError, "response chunk ends inside its context bytes"):
        reqresp.decode_response_chunk(4, 0, 100, bytes([0, 0x6A, 0x95]))


def test_missing_code():
    with raises(ValueError, "response chunk has no response code"):
        reqresp.decode_response_chunk(0, 0, 100, b"")


def test_success_chunk_below_type_minimum():
    digest = bytes.fromhex("6a95a1a9")
    chunk = bytes([0]) + digest + _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    with raises(ValueError, "declared length 4 is below 8"):
        reqresp.decode_response_chunk(4, 8, 100, chunk)


def test_empty_error_message_ignores_type_minimum():
    # An error chunk carries an error message, not the payload type, so it may be empty.
    chunk = bytes([1]) + _varint(0) + STREAM_IDENTIFIER
    assert reqresp.decode_response_chunk(4, 8, 100, chunk) == (1, b"", b"")


# A frame decoder written here checks the encoders that compress.
# It reads blocks with the independent block decoder of the Snappy tests.
# It reads only data chunks, the only chunks that the encoders write.
# A compressor may write other bytes for the same data, so the tests compare the decoded data.
#
# Frames: https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/framing_format.txt


def _read_varint(data: bytes, at: int) -> tuple[int, int]:
    # The value of the varint at `at`, and the position after it.
    value, shift = 0, 0
    while True:
        byte = data[at]
        value |= (byte & 0x7F) << shift
        at += 1
        if byte < 0x80:
            return value, at
        shift += 7


def _decode_frames(stream: bytes) -> tuple[bytes, list[tuple[int, int]]]:
    # The data of a framed stream, and the type and data size of each of its data chunks.
    assert stream.startswith(STREAM_IDENTIFIER)
    data = bytearray()
    chunks: list[tuple[int, int]] = []
    at = len(STREAM_IDENTIFIER)
    while at < len(stream):
        chunk_type = stream[at]
        length = int.from_bytes(stream[at + 1 : at + 4], "little")
        body = stream[at + 4 : at + 4 + length]
        assert len(body) == length
        at += 4 + length
        # Type 0 is a compressed chunk, and type 1 an uncompressed one.
        assert chunk_type in (0x00, 0x01)
        piece = decode_block(body[4:]) if chunk_type == 0x00 else body[4:]
        assert len(piece) <= 65536
        assert body[:4] == _masked_crc(piece).to_bytes(4, "little")
        data += piece
        chunks.append((chunk_type, len(piece)))
    return bytes(data), chunks


def _decode_payload(payload: bytes) -> tuple[bytes, list[tuple[int, int]]]:
    # The data of a payload, checked against its length prefix, and the chunks of its stream.
    length, at = _read_varint(payload, 0)
    assert payload[:at] == _varint(length)
    data, chunks = _decode_frames(payload[at:])
    assert len(data) == length
    return data, chunks


def _noise(n: int) -> bytes:
    # Bytes that do not compress, from a seeded generator.
    return random.Random(2026).randbytes(n)


def test_reference_decoder():
    # The decoder reads the hand-built messages of the tests above.
    uncompressed = _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    assert _decode_payload(uncompressed) == (PAYLOAD, [(1, 4)])
    compressed = _varint(4) + STREAM_IDENTIFIER + _compressed_literal(PAYLOAD)
    assert _decode_payload(compressed) == (PAYLOAD, [(0, 4)])
    # 32 zero bytes: a literal of one zero byte, then a copy of 31 bytes from 1 back.
    assert decode_block(bytes.fromhex("2000007a0100")) == bytes(32)


# Each input of the payload encoder, and the type and data size of each chunk that it writes.
# Each chunk holds at most 65536 bytes of data.
PAYLOADS = [
    pytest.param(b"", [], id="empty"),
    pytest.param(PAYLOAD, [(1, 4)], id="4 bytes"),
    pytest.param(bytes(100), [(0, 100)], id="100 zero bytes"),
    pytest.param(_noise(1000), [(1, 1000)], id="incompressible"),
    pytest.param(bytes(65537), [(0, 65536), (1, 1)], id="cut after 65536 bytes"),
    pytest.param(
        _noise(65536) + bytes(70_000), [(1, 65536), (0, 65536), (0, 4464)], id="three chunks"
    ),
]


@pytest.mark.parametrize(("data", "chunks"), PAYLOADS)
def test_encode_payload(data: bytes, chunks: list[tuple[int, int]]):
    payload = reqresp.encode_payload(data)
    assert _decode_payload(payload) == (data, chunks)
    assert reqresp.decode_payload(len(data), len(data), payload) == data


# The SSZ objects of the 50 ssz_snappy files of consensus-spec-tests that the Snappy tests read.
# `tests/consensus/snappy/README.md` gives their origin.
@pytest.mark.parametrize("case", SPEC_CASES, ids=[case["file"] for case in SPEC_CASES])
def test_encode_payload_of_spec_objects(case: SpecCase):
    data = spec_object(case)
    decoded, _ = _decode_payload(reqresp.encode_payload(data))
    assert decoded == data


def test_encode_payload_wrong_type():
    with raises(TypeError, "data must be bytes"):
        reqresp.encode_payload(bytearray(b"x"))  # ty: ignore[invalid-argument-type]


RESPONSE_CHUNKS = [
    pytest.param(reqresp.ResponseChunk(0, bytes.fromhex("6a95a1a9"), bytes(100)), id="success"),
    pytest.param(reqresp.ResponseChunk(0, b"", PAYLOAD), id="success without context"),
    pytest.param(reqresp.ResponseChunk(1, b"", b"bad request"), id="invalid request"),
    pytest.param(reqresp.ResponseChunk(200, b"", b"x"), id="request specific"),
]


@pytest.mark.parametrize("chunk", RESPONSE_CHUNKS)
def test_encode_response_chunk(chunk: reqresp.ResponseChunk):
    encoded = reqresp.encode_response_chunk(chunk)
    # The code and the context bytes are written as they are, before the payload.
    head = bytes([chunk.code]) + chunk.context
    assert encoded.startswith(head)
    assert _decode_payload(encoded[len(head) :])[0] == chunk.payload
    size = len(chunk.payload)
    assert reqresp.decode_response_chunk(len(chunk.context), size, size, encoded) == chunk


def test_encode_response_chunk_keeps_any_context():
    # The encoder does not check the context bytes against the code.
    chunk = reqresp.ResponseChunk(2, bytes.fromhex("6a95a1a9"), b"oops")
    encoded = reqresp.encode_response_chunk(chunk)
    assert encoded[:5] == bytes.fromhex("026a95a1a9")
    assert _decode_payload(encoded[5:])[0] == b"oops"


@pytest.mark.parametrize("code", [256, -1, 2**64], ids=["256", "negative", "2^64"])
def test_encode_response_chunk_code_out_of_range(code: int):
    with raises(OverflowError, "code must be in [0, 256)"):
        reqresp.encode_response_chunk(reqresp.ResponseChunk(code, b"", b""))


WRONG_TYPES = [
    pytest.param(
        reqresp.ResponseChunk(b"\x00", b"", b""),  # ty: ignore[invalid-argument-type]
        "code must be int",
        id="code",
    ),
    pytest.param(
        reqresp.ResponseChunk(0, "", b""),  # ty: ignore[invalid-argument-type]
        "context and payload must be bytes",
        id="context",
    ),
    pytest.param(
        reqresp.ResponseChunk(0, b"", ""),  # ty: ignore[invalid-argument-type]
        "context and payload must be bytes",
        id="payload",
    ),
]


@pytest.mark.parametrize(("chunk", "message"), WRONG_TYPES)
def test_encode_response_chunk_wrong_type(chunk: reqresp.ResponseChunk, message: str):
    with raises(TypeError, message):
        reqresp.encode_response_chunk(chunk)
