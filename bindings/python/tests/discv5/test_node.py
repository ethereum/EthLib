"""The session states of two discv5 nodes, through a whole handshake."""

from ethlib.networking import discv5, enr
from ethlib.serialization import rlp

# The steps come from "Sessions" in discv5/discv5-theory.md of ethereum/devp2p.
# No official vectors exist for a run of several packets, so the run is built here.
# Node A has the private key 1 and node B the private key 2.
# Their compressed public keys are those of the points G and 2G of secp256k1, from SEC 2 §2.4.1.

KEY_A = (1).to_bytes(32, "big")
KEY_B = (2).to_bytes(32, "big")
PUB_A = bytes.fromhex("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
PUB_B = bytes.fromhex("02c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5")
RECORD_A = enr.make_record_v4(KEY_A, 1, rlp.encode([]))
RECORD_B = enr.make_record_v4(KEY_B, 1, rlp.encode([]))
ID_A = enr.node_id(RECORD_A)
ID_B = enr.node_id(RECORD_B)

IP_A = bytes([10, 0, 0, 1])
IP_A_MOVED = bytes([10, 0, 0, 3])
IP_B = bytes([10, 0, 0, 2])
PORT = 9000

# Node B answers every message with NODES, written here as an opaque plaintext.
NODES = bytes([4]) + rlp.encode([b"\x01", b"\x01", []])
FINDNODE = bytes([3]) + rlp.encode([b"\x01", [b"\x01\x00"]])
PING = bytes([1]) + rlp.encode([b"\x02", b"\x01"])

NODE_A = (KEY_A, ID_A, RECORD_A, 1, [(ID_B, PUB_B, 1)], None)
NODE_B = (KEY_B, ID_B, RECORD_B, 1, [(ID_A, PUB_A, 0)], NODES)
EMPTY = ([], [], [])


def _randoms(n: int) -> tuple[bytes, bytes, bytes, bytes]:
    # Random values of one step, made distinct by n.
    return (bytes([n]) * 16, bytes([n]) * 8, bytes([n + 100]) * 16, (n + 7).to_bytes(32, "big"))


def _send(state: tuple, plaintext: bytes, n: int) -> tuple[tuple, bytes]:
    state, sent = discv5.node_send(
        NODE_A, _randoms(n), state, ID_B, IP_B, PORT, bytes([0xAA]) * 16, plaintext
    )
    assert len(sent) == 1
    return state, sent[0]


def test_handshake_and_roaming() -> None:
    # 1. A sends FINDNODE in a packet that B cannot open: B sends WHOAREYOU and stores it.
    state_a, findnode = _send(EMPTY, FINDNODE, 1)
    state_b, (whoareyou,) = discv5.node_step(NODE_B, _randoms(2), EMPTY, IP_A, PORT, findnode)
    assert len(state_b[1]) == 1

    # 2. A sends PING before it sees the challenge: B sends the same WHOAREYOU, not a new one.
    _, ping = _send(state_a, PING, 3)
    again, (whoareyou_again,) = discv5.node_step(NODE_B, _randoms(4), state_b, IP_A, PORT, ping)
    assert whoareyou_again == whoareyou
    assert again == state_b

    # 3. A answers with a handshake packet, and B derives the keys and answers.
    state_a, (handshake,) = discv5.node_step(NODE_A, _randoms(5), state_a, IP_B, PORT, whoareyou)
    state_b, (answer,) = discv5.node_step(NODE_B, _randoms(6), state_b, IP_A, PORT, handshake)
    # Both nodes hold one session with the same two keys, and B's challenge is gone.
    ((_, _, _, a_init, a_recip, a_initiator, _),) = state_a[0]
    ((_, _, _, b_init, b_recip, b_initiator, _),) = state_b[0]
    assert (a_init, a_recip, a_initiator) == (b_init, b_recip, True)
    assert not b_initiator
    assert state_b[1] == []
    # A opens B's answer in the session, and settles its request.
    state_a, replies = discv5.node_step(NODE_A, _randoms(7), state_a, IP_B, PORT, answer)
    assert replies == []
    assert state_a[2] == []

    # 4. A moves to another address and sends PING: B has no keys there, so it sends WHOAREYOU.
    _, ping = discv5.node_send(
        NODE_A, _randoms(8), state_a, ID_B, IP_B, PORT, bytes([0xAA]) * 16, PING
    )
    moved_b, (challenge,) = discv5.node_step(
        NODE_B, _randoms(9), state_b, IP_A_MOVED, PORT, ping[0]
    )
    # The new challenge is kept at the new endpoint, and the session at the old one is unchanged.
    assert moved_b[1] == [(ID_A, IP_A_MOVED, PORT, challenge, moved_b[1][0][4])]
    assert moved_b[0] == state_b[0]


def test_unsolicited_whoareyou_is_ignored() -> None:
    # A WHOAREYOU that no request of A caused changes nothing and gets nothing.
    _, findnode = _send(EMPTY, FINDNODE, 1)
    _, (whoareyou,) = discv5.node_step(NODE_B, _randoms(2), EMPTY, IP_A, PORT, findnode)
    assert discv5.node_step(NODE_A, _randoms(3), EMPTY, IP_B, PORT, whoareyou) == (EMPTY, [])


def test_session_messages_use_counter_nonces() -> None:
    # Each message sealed in the session carries the counter in the first 4 bytes of its nonce.
    state_a, findnode = _send(EMPTY, FINDNODE, 1)
    _, (whoareyou,) = discv5.node_step(NODE_B, _randoms(2), EMPTY, IP_A, PORT, findnode)
    state_a, _ = discv5.node_step(NODE_A, _randoms(3), state_a, IP_B, PORT, whoareyou)
    counter = state_a[0][0][6]
    state_a, first = _send(state_a, PING, 4)
    state_a, second = _send(state_a, PING, 5)
    assert state_a[0][0][6] == counter + 2
    nonces = [discv5.decode_packet(ID_B, packet)["nonce"] for packet in (first, second)]
    assert [nonce[:4] for nonce in nonces] == [
        counter.to_bytes(4, "big"),
        (counter + 1).to_bytes(4, "big"),
    ]


def test_handshake_with_the_record_in_the_packet() -> None:
    # B has no record of A, so its WHOAREYOU holds 0 and A puts its record in the handshake.
    node_b = (KEY_B, ID_B, RECORD_B, 1, [], NODES)
    state_a, findnode = _send(EMPTY, FINDNODE, 1)
    state_b, (whoareyou,) = discv5.node_step(node_b, _randoms(2), EMPTY, IP_A, PORT, findnode)
    state_a, (handshake,) = discv5.node_step(NODE_A, _randoms(3), state_a, IP_B, PORT, whoareyou)
    state_b, (answer,) = discv5.node_step(node_b, _randoms(4), state_b, IP_A, PORT, handshake)
    assert state_b[0][0][3:5] == state_a[0][0][3:5]
