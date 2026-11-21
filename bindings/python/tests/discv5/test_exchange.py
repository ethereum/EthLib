"""Answers of discv5 against their requests, with records signed by test keys."""

from ethlib.networking import discv5, enr
from ethlib.serialization import rlp
from raising import raises

# The rules come from "Protocol Messages" of discv5/discv5-wire.md in ethereum/devp2p.
# No official vectors exist for them, so the messages are RLP built here.
# Each record is a "v4" record made by the library from a test key, with no other pair.
# A node ID is 32 bytes, and the logarithmic distance counts the bits of the XOR of two IDs.


def _int(n: int) -> bytes:
    # An RLP scalar: big-endian, with no leading zero byte.
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _message(message_type: int, *fields: object) -> bytes:
    return bytes([message_type]) + rlp.encode(list(fields))


def _record(secret: int) -> bytes:
    return enr.make_record_v4(secret.to_bytes(32, "big"), 1, rlp.encode([]))


def _flip(node_id: bytes, bit: int) -> bytes:
    # The ID that differs from this one in one bit, counted from the lowest bit.
    return (int.from_bytes(node_id, "big") ^ (1 << bit)).to_bytes(32, "big")


RECORD = _record(1)
NODE_ID = enr.node_id(RECORD)
OTHER = _record(2)

PING = _message(1, b"\x01", _int(1))
PONG = _message(2, b"\x01", _int(1), bytes([127, 0, 0, 1]), _int(30303))
FINDNODE = _message(3, b"\x01", [_int(256)])
NODES = _message(4, b"\x01", _int(1), [])
TALKREQ = _message(5, b"\x02", b"xyz", b"hello")
TALKRESP = _message(6, b"\x02", b"")


def test_answer_types() -> None:
    assert discv5.answers_request(PING, PONG)
    assert discv5.answers_request(FINDNODE, NODES)
    assert discv5.answers_request(TALKREQ, TALKRESP)


def test_answer_of_another_request() -> None:
    assert not discv5.answers_request(PING, NODES)
    assert not discv5.answers_request(FINDNODE, TALKRESP)
    # A response is no request, so nothing answers it.
    assert not discv5.answers_request(PONG, PONG)


def test_request_id_is_mirrored() -> None:
    # A TALKRESP with request ID 0x02 does not answer a TALKREQ with request ID 0x01.
    assert not discv5.answers_request(_message(5, b"\x01", b"xyz", b""), TALKRESP)
    assert not discv5.answers_request(PING, _message(2, b"\x02", _int(1), bytes(4), _int(1)))


def test_unknown_protocol_gets_an_empty_response() -> None:
    # An unknown protocol "must" get a TALKRESP "containing empty response data".
    assert discv5.talk_response(TALKREQ) == TALKRESP
    assert discv5.answers_request(TALKREQ, discv5.talk_response(TALKREQ))


def test_talk_response_of_another_message() -> None:
    with raises(ValueError, "message is not a TALKREQ"):
        discv5.talk_response(PING)


def test_rejects_a_plaintext_that_is_no_message() -> None:
    with raises(ValueError, "invalid message: empty"):
        discv5.answers_request(b"", PONG)


def test_nodes_at_distance_256() -> None:
    # The recipient differs from the record in its first bit, so the distance is 256.
    recipient = _flip(NODE_ID, 255)
    assert discv5.nodes_match(recipient, [256], [RECORD])
    assert not discv5.nodes_match(recipient, [255], [RECORD])


def test_nodes_at_distance_2() -> None:
    # The recipient differs in the second lowest bit, so the distance is 2.
    recipient = _flip(NODE_ID, 1)
    assert discv5.nodes_match(recipient, [2], [RECORD])
    assert not discv5.nodes_match(recipient, [256], [RECORD])


def test_distance_zero_is_the_recipient_itself() -> None:
    assert discv5.nodes_match(NODE_ID, [0], [RECORD])
    assert not discv5.nodes_match(NODE_ID, [0], [RECORD, OTHER])


def test_every_record_must_match() -> None:
    other_distance = discv5.log_distance(NODE_ID, enr.node_id(OTHER))
    assert discv5.nodes_match(NODE_ID, [0, other_distance], [RECORD, OTHER])
    assert not discv5.nodes_match(NODE_ID, [other_distance], [RECORD, OTHER])
    assert discv5.nodes_match(NODE_ID, [256], [])


def test_a_record_that_does_not_verify() -> None:
    # The same record with a zero signature no longer verifies, so it never matches.
    fields = rlp.decode(RECORD)
    forged = rlp.encode([bytes(64), *fields[1:]])
    assert not discv5.nodes_match(NODE_ID, [0], [forged])


def test_rejects_bytes_that_are_no_rlp_item() -> None:
    with raises(ValueError, "record is not one RLP item"):
        discv5.nodes_match(NODE_ID, [0], [b"\xc1"])
