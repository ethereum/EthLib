"""The ssz_snappy req/resp encoding against hand-built messages.

Each message is built here from the framing format of google/snappy (framing_format.txt) and the
protobuf varint, so no value comes from the code under test.
Each test names the rule that its message pins.
"""

from ethlib.networking import reqresp
from raising import raises

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
    assert reqresp.decode_payload(4, message) == PAYLOAD


def test_uncompressed_chunk():
    message = _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    assert reqresp.decode_payload(100, message) == PAYLOAD


def test_compressed_chunk():
    message = _varint(4) + STREAM_IDENTIFIER + _compressed_literal(PAYLOAD)
    assert reqresp.decode_payload(100, message) == PAYLOAD


def test_two_chunks():
    chunks = _uncompressed(PAYLOAD[:1]) + _uncompressed(PAYLOAD[1:])
    message = _varint(4) + STREAM_IDENTIFIER + chunks
    assert reqresp.decode_payload(4, message) == PAYLOAD


def test_empty_payload():
    assert reqresp.decode_payload(0, _varint(0) + STREAM_IDENTIFIER) == b""


def test_length_above_type_bound():
    message = _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    with raises(ValueError, "declared length 4 is above 3"):
        reqresp.decode_payload(3, message)


def test_length_above_payload_cap():
    # A declared length of 10 MiB + 1 exceeds the cap, before any frame is read.
    message = _varint(10 * 2**20 + 1) + STREAM_IDENTIFIER
    with raises(ValueError, "declared length 10485761 is above 10485760"):
        reqresp.decode_payload(2**30, message)


def test_length_at_payload_cap():
    # A declared length of 10 MiB passes the cap, and fails later: the stream is empty.
    message = _varint(10 * 2**20) + STREAM_IDENTIFIER
    with raises(ValueError, "payload has 0 bytes, not the declared 10485760"):
        reqresp.decode_payload(2**30, message)


def test_stream_shorter_than_declared():
    message = _varint(5) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    with raises(ValueError, "payload has 4 bytes, not the declared 5"):
        reqresp.decode_payload(100, message)


def test_stream_longer_than_declared():
    message = _varint(3) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    with raises(ValueError, "payload has 4 bytes, not the declared 3"):
        reqresp.decode_payload(100, message)


def test_compressed_bytes_at_the_bound():
    # Declared length 0 allows 32 bytes: the identifier (10) and a padding chunk of 4 + 18.
    message = _varint(0) + STREAM_IDENTIFIER + _chunk(0xFE, bytes(18))
    assert reqresp.decode_payload(0, message) == b""


def test_compressed_bytes_above_the_bound():
    # One more padding byte makes 33 bytes after the prefix.
    message = _varint(0) + STREAM_IDENTIFIER + _chunk(0xFE, bytes(19))
    with raises(ValueError, "33 compressed bytes, more than 32"):
        reqresp.decode_payload(0, message)


def test_non_minimal_varint():
    message = bytes([0x84, 0x00]) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    with raises(ValueError, "length prefix is not a valid varint"):
        reqresp.decode_payload(100, message)


def test_varint_over_ten_bytes():
    message = bytes([0x80] * 10 + [0x00]) + STREAM_IDENTIFIER
    with raises(ValueError, "length prefix is not a valid varint"):
        reqresp.decode_payload(100, message)


def test_bad_checksum():
    message = _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD, checksum=0)
    with raises(ValueError, "payload is not a valid Snappy framed stream"):
        reqresp.decode_payload(100, message)


def test_missing_stream_identifier():
    message = _varint(4) + _uncompressed(PAYLOAD)
    with raises(ValueError, "payload is not a valid Snappy framed stream"):
        reqresp.decode_payload(100, message)


def test_success_chunk_with_fork_digest():
    digest = bytes.fromhex("6a95a1a9")
    chunk = bytes([0]) + digest + _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    assert reqresp.decode_response_chunk(4, 100, chunk) == (0, digest, PAYLOAD)


def test_success_chunk_without_context():
    chunk = bytes([0]) + _varint(4) + STREAM_IDENTIFIER + _uncompressed(PAYLOAD)
    assert reqresp.decode_response_chunk(0, 100, chunk) == (0, b"", PAYLOAD)


def test_error_chunk():
    # An error carries no context bytes, even on a method that sends a fork digest.
    message = b"bad request"
    chunk = bytes([1]) + _varint(len(message)) + STREAM_IDENTIFIER + _uncompressed(message)
    assert reqresp.decode_response_chunk(4, 0, chunk) == (1, b"", message)


def test_request_specific_code():
    chunk = bytes([200]) + _varint(1) + STREAM_IDENTIFIER + _uncompressed(b"x")
    assert reqresp.decode_response_chunk(4, 0, chunk) == (200, b"", b"x")


def test_error_message_too_long():
    message = bytes(reqresp.MAX_ERROR_MESSAGE_SIZE + 1)
    chunk = bytes([2]) + _varint(len(message)) + STREAM_IDENTIFIER + _uncompressed(message)
    with raises(ValueError, "declared length 257 is above 256"):
        reqresp.decode_response_chunk(0, 1000, chunk)


def test_context_truncated():
    with raises(ValueError, "response chunk ends inside its context bytes"):
        reqresp.decode_response_chunk(4, 100, bytes([0, 0x6A, 0x95]))


def test_missing_code():
    with raises(ValueError, "response chunk has no response code"):
        reqresp.decode_response_chunk(0, 100, b"")
