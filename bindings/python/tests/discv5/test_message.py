"""discv5 messages against discv5-wire-test-vectors.md of ethereum/devp2p, commit
88f1c80800d622cc3a542a2125bbe33cc18c9f9c, and hand-built messages."""

import pytest

from ethlib.networking import discv5

H = bytes.fromhex


def _rlp_bytes(data: bytes) -> bytes:
    # The byte strings here are short, so a one-byte prefix suffices.
    if len(data) == 1 and data[0] < 0x80:
        return data
    assert len(data) < 56
    return bytes([0x80 + len(data)]) + data


def _rlp_list(payload: bytes) -> bytes:
    assert len(payload) < 56
    return bytes([0xC0 + len(payload)]) + payload


def _scalar(n: int) -> bytes:
    return _rlp_bytes(n.to_bytes((n.bit_length() + 7) // 8, "big"))


def _message(message_type: int, *fields: bytes) -> bytes:
    return bytes([message_type]) + _rlp_list(b"".join(fields))


def test_ping_of_the_packet_vector():
    # The ping of the message packet vector: request ID 0x00000001, ENR sequence number 2.
    m = discv5.decode_message(H("01c684000000010" + "2"))
    assert m == {"type": 1, "request_id": H("00000001"), "enr_seq": 2}


def test_ping_of_the_gcm_vector():
    # The plaintext of the AES-GCM vector: a ping with request ID 0x01 and sequence number 1.
    m = discv5.decode_message(H("01c20101"))
    assert m == {"type": 1, "request_id": H("01"), "enr_seq": 1}


PONG = _message(2, _rlp_bytes(H("01")), _scalar(5), _rlp_bytes(H("7f000001")), _scalar(30303))
FINDNODE = _message(3, _rlp_bytes(H("02")), _rlp_list(_scalar(0) + _scalar(255) + _scalar(256)))
NODES = _message(4, _rlp_bytes(H("03")), _scalar(1), _rlp_list(b""))
TALKREQ = _message(5, _rlp_bytes(H("04")), _rlp_bytes(b"eth"), _rlp_bytes(b"hello"))
TALKRESP = _message(6, _rlp_bytes(H("05")), _rlp_bytes(b""))


@pytest.mark.parametrize("plaintext", [PONG, FINDNODE, NODES, TALKREQ, TALKRESP])
def test_reencode(plaintext):
    assert discv5.reencode_message(plaintext) == plaintext


def test_pong_fields():
    m = discv5.decode_message(PONG)
    assert (m["recipient_ip"], m["recipient_port"]) == (H("7f000001"), 30303)


def test_findnode_distances():
    assert discv5.decode_message(FINDNODE)["distances"] == [0, 255, 256]


def test_nodes_with_one_record():
    # A record stays its RLP bytes; this one is the list [sig, seq 1] of a toy record.
    record = _rlp_list(_rlp_bytes(b"sig") + _scalar(1))
    m = discv5.decode_message(_message(4, _rlp_bytes(H("03")), _scalar(1), _rlp_list(record)))
    assert m["records"] == [record]


def test_empty():
    with pytest.raises(discv5.Discv5Error, match="empty") as error:
        discv5.decode_message(b"")
    assert error.value.code == 101


def test_error_code_of_a_range_check():
    with pytest.raises(discv5.Discv5Error) as error:
        discv5.decode_message(_message(1, _rlp_bytes(bytes(9)), _scalar(1)))
    assert error.value.code == 105


def test_unknown_type():
    with pytest.raises(discv5.Discv5Error, match="unknown type") as error:
        discv5.decode_message(_message(11, _rlp_bytes(H("01"))))
    assert error.value.code == 102


def test_field_of_the_wrong_form():
    # A port of 65536 is not below 2^16.
    ip = _rlp_bytes(H("7f000001"))
    plaintext = _message(2, _rlp_bytes(H("01")), _scalar(5), ip, _scalar(65536))
    with pytest.raises(discv5.Discv5Error, match="wrong form") as error:
        discv5.decode_message(plaintext)
    assert error.value.code == 103


def test_wrong_field_count():
    with pytest.raises(discv5.Discv5Error, match="field count") as error:
        discv5.decode_message(_message(1, _rlp_bytes(H("01"))))
    assert error.value.code == 104


def test_request_id_of_nine_bytes():
    with pytest.raises(ValueError, match="out of range"):
        discv5.decode_message(_message(1, _rlp_bytes(bytes(9)), _scalar(1)))


def test_distance_257():
    with pytest.raises(ValueError, match="out of range"):
        discv5.decode_message(_message(3, _rlp_bytes(H("01")), _rlp_list(_scalar(257))))


def test_pong_address_of_five_bytes():
    plaintext = _message(2, _rlp_bytes(H("01")), _scalar(5), _rlp_bytes(bytes(5)), _scalar(1))
    with pytest.raises(ValueError, match="out of range"):
        discv5.decode_message(plaintext)


def test_topic_distance_zero():
    # A distance from a topic is a positive integer.
    plaintext = _message(9, _rlp_bytes(H("01")), _rlp_bytes(bytes(32)), _rlp_list(_scalar(0)))
    with pytest.raises(ValueError, match="out of range"):
        discv5.decode_message(plaintext)
