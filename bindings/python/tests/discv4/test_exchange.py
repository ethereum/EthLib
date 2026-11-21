"""The exchange rules of discv4: the endpoint proof, expired packets and unsolicited Pongs."""

from ethlib.networking import discv4, enr
from ethlib.serialization import rlp
from raising import raises

# The rules come from "Endpoint Proof" and the packet sections of discv4.md in ethereum/devp2p.
# No official vectors exist for them, so the packets are RLP built here and signed by test keys.
# Node A is at 10.0.0.1:30303 and node B at 10.0.0.2:30303; B receives the packets of A.
# A time is a UNIX time in seconds, and a packet expires once its expiration is in the past.

KEY_A = (1).to_bytes(32, "big")
KEY_B = (2).to_bytes(32, "big")
IP_A = bytes([10, 0, 0, 1])
IP_B = bytes([10, 0, 0, 2])
PORT = 30303
# The 12 hours of an endpoint proof, in seconds.
DAY_HALF = 12 * 3600

NO_PEER = discv4.Peer(None, None)
RECORD = enr.make_record_v4(KEY_B, 1, rlp.encode([]))
# One node of the table of B, which B gives for any target.
NODE = [IP_B, PORT.to_bytes(2, "big"), PORT.to_bytes(2, "big"), bytes(64)]


def _int(n: int) -> bytes:
    # An RLP scalar: big-endian, with no leading zero byte.
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _endpoint(ip: bytes, tcp: int) -> list[bytes]:
    return [ip, _int(PORT), _int(tcp)]


def _packet(key: bytes, packet_type: int, *fields: object) -> bytes:
    return discv4.encode(key, bytes([packet_type]) + rlp.encode(list(fields)))


def _receive(now: int, peer: discv4.Peer, packet: bytes) -> tuple[discv4.Peer, list[bytes]]:
    # B receives a packet from the address of A.
    return discv4.receive(now, IP_A, PORT, peer, packet, now + 20, None, RECORD, rlp.encode([NODE]))


def _find_node(expiration: int) -> bytes:
    return _packet(KEY_A, 3, bytes(64), _int(expiration))


def _proof_at_1000() -> discv4.Peer:
    # B pings A, and A's Pong carries the hash of that Ping, the first 32 bytes of the packet.
    ping = _packet(KEY_B, 1, _int(4), _endpoint(IP_B, PORT), _endpoint(IP_A, 0), _int(1020))
    ping_hash = ping[:32]
    pong = _packet(KEY_A, 2, _endpoint(IP_B, PORT), ping_hash, _int(1020))
    peer, replies = _receive(1000, discv4.Peer(ping_hash, None), pong)
    assert replies == []
    return peer


def test_find_node_without_proof_gets_nothing() -> None:
    assert _receive(1000, NO_PEER, _find_node(1020)) == (NO_PEER, [])


def test_pong_with_the_ping_hash_proves_the_endpoint() -> None:
    peer = _proof_at_1000()
    assert peer.last_pong == 1000


def test_find_node_after_the_proof_gets_neighbors() -> None:
    peer = _proof_at_1000()
    _, replies = _receive(2000, peer, _find_node(2020))
    assert replies == [bytes([4]) + rlp.encode([[NODE], _int(2020)])]


def test_proof_lasts_12_hours() -> None:
    peer = _proof_at_1000()
    # 12 hours exactly still counts, and one second more does not.
    assert len(_receive(1000 + DAY_HALF, peer, _find_node(1000 + DAY_HALF))[1]) == 1
    assert _receive(1000 + DAY_HALF + 1, peer, _find_node(1000 + DAY_HALF + 1))[1] == []


def test_expired_pong_changes_nothing() -> None:
    ping_hash = bytes(32)
    pong = _packet(KEY_A, 2, _endpoint(IP_B, PORT), ping_hash, _int(900))
    peer = discv4.Peer(ping_hash, None)
    assert _receive(1000, peer, pong) == (peer, [])


def test_unsolicited_pong_changes_nothing() -> None:
    pong = _packet(KEY_A, 2, _endpoint(IP_B, PORT), bytes(32), _int(1020))
    peer = discv4.Peer(bytes([1]) * 32, None)
    assert _receive(1000, peer, pong) == (peer, [])


def test_ping_gets_a_pong_with_its_hash() -> None:
    ping = _packet(KEY_A, 1, _int(4), _endpoint(IP_A, 30304), _endpoint(IP_B, 0), _int(1020))
    peer, replies = _receive(1000, NO_PEER, ping)
    assert peer == NO_PEER
    # The Pong goes to the address that the Ping came from, with its TCP port.
    assert replies == [bytes([2]) + rlp.encode([_endpoint(IP_A, 30304), ping[:32], _int(1020)])]


def test_expired_ping_gets_nothing() -> None:
    ping = _packet(KEY_A, 1, _int(4), _endpoint(IP_A, 0), _endpoint(IP_B, 0), _int(999))
    assert _receive(1000, NO_PEER, ping) == (NO_PEER, [])


def test_enr_request_after_the_proof() -> None:
    request = _packet(KEY_A, 5, _int(1020))
    assert _receive(1000, NO_PEER, request)[1] == []
    _, replies = _receive(1000, _proof_at_1000(), request)
    # The ENRResponse holds the hash of the whole ENRRequest packet, then the record.
    assert replies == [bytes([6]) + rlp.encode([request[:32], rlp.decode(RECORD)])]


def test_sixteen_nodes_take_two_packets() -> None:
    # At most twelve nodes go into one Neighbors packet, to stay under 1280 bytes.
    peer = _proof_at_1000()
    nodes = [NODE] * 16
    _, replies = discv4.receive(
        2000, IP_A, PORT, peer, _find_node(2020), 2020, None, RECORD, rlp.encode(nodes)
    )
    assert replies == [
        bytes([4]) + rlp.encode([[NODE] * 12, _int(2020)]),
        bytes([4]) + rlp.encode([[NODE] * 4, _int(2020)]),
    ]


def test_twelve_ipv6_nodes_fit_in_a_packet() -> None:
    # Twelve IPv6 nodes with ports of two bytes and an expiration of four make 1201 bytes.
    node6 = [bytes(16), PORT.to_bytes(2, "big"), PORT.to_bytes(2, "big"), bytes(64)]
    content = bytes([4]) + rlp.encode([[node6] * 12, _int(2**31)])
    assert len(discv4.encode(KEY_B, content)) == 1201
    # Thirteen make 1292 bytes, over the limit of 1280, so the encoder refuses them.
    content = bytes([4]) + rlp.encode([[node6] * 13, _int(2**31)])
    with raises(ValueError, "packet has 1292 bytes, more than 1280"):
        discv4.encode(KEY_B, content)


def test_accept_enr_response() -> None:
    request = _packet(KEY_B, 5, _int(1020))
    response = _packet(
        KEY_A, 6, request[:32], rlp.decode(enr.make_record_v4(KEY_A, 1, rlp.encode([])))
    )
    assert discv4.accept_enr_response(request, response)
    # Another hash, or a record of another key, is refused.
    other = _packet(KEY_A, 6, bytes(32), rlp.decode(enr.make_record_v4(KEY_A, 1, rlp.encode([]))))
    assert not discv4.accept_enr_response(request, other)
    foreign = _packet(KEY_A, 6, request[:32], rlp.decode(RECORD))
    assert not discv4.accept_enr_response(request, foreign)
