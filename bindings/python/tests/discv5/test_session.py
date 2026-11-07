"""discv5 session packets, written and read, against the discv5 wire test vectors."""

from ethlib.networking import discv5
from raising import raises

# The test vectors of the discv5 wire protocol, "Packet Encodings".
#
# File: discv5/discv5-wire-test-vectors.md
# Repository: ethereum/devp2p
# Commit: 88f1c80800d622cc3a542a2125bbe33cc18c9f9c
#
# The vectors do not list the masking IV as an input.
# Every packet of the vectors starts with 16 zero bytes.
# The masking IV is the first 16 bytes of a packet, sent in the clear.
# So the tests take it to be 16 zero bytes.

H = bytes.fromhex

NODE_A_KEY = H("eef77acb6c6a6eebc5b363a475ac583ec7eccdb42b6481424c60f59aa326547f")
NODE_B_KEY = H("66fb62bfbd66b9177a138c1e5cddbe4f7c30c343e94e68df8769459cb1cde628")
SRC_ID = H("aaaa8419e9f49d0083561b48287df592939a8d19947d8c0ef88f2a4856a69fbb")
DEST_ID = H("bbbb9d047f0488c0b5a93c1c3f2d8bafc7c8ff337024a55434a0d0555de64db9")
NONCE = H("ffffffffffffffffffffffff")
MASKING_IV = bytes(16)

# The ping message: type 0x01, then the RLP list [req-id 0x00000001, enr-seq].
PING_ENR_SEQ_2 = H("01c684000000010" + "2")
PING_ENR_SEQ_1 = H("01c684000000010" + "1")

PING_PACKET = H(
    "00000000000000000000000000000000088b3d4342774649325f313964a39e55"
    "ea96c005ad52be8c7560413a7008f16c9e6d2f43bbea8814a546b7409ce783d3"
    "4c4f53245d08dab84102ed931f66d1492acb308fa1c6715b9d139b81acbdcc"
)

WHOAREYOU_PACKET = H(
    "00000000000000000000000000000000088b3d434277464933a1ccc59f5967ad"
    "1d6035f15e528627dde75cd68292f9e6c27d6b66c8100a873fcbaed4e16b8d"
)
WHOAREYOU_NONCE = H("0102030405060708090a0b0c")
ID_NONCE = H("0102030405060708090a0b0c0d0e0f10")
WHOAREYOU_CHALLENGE_DATA = H(
    "000000000000000000000000000000006469736376350001010102030405060708090a0b0c"
    "00180102030405060708090a0b0c0d0e0f100000000000000000"
)

HANDSHAKE_PACKET = H(
    "00000000000000000000000000000000088b3d4342774649305f313964a39e55"
    "ea96c005ad521d8c7560413a7008f16c9e6d2f43bbea8814a546b7409ce783d3"
    "4c4f53245d08da4bb252012b2cba3f4f374a90a75cff91f142fa9be3e0a5f3ef"
    "268ccb9065aeecfd67a999e7fdc137e062b2ec4a0eb92947f0d9a74bfbf44dfb"
    "a776b21301f8b65efd5796706adff216ab862a9186875f9494150c4ae06fa4d1"
    "f0396c93f215fa4ef524f1eadf5f0f4126b79336671cbcf7a885b1f8bd2a5d83"
    "9cf8"
)
# The handshake inputs of "Ping handshake packet (flag 2)": a WHOAREYOU with enr-seq 1.
HANDSHAKE_CHALLENGE_DATA = H(
    "000000000000000000000000000000006469736376350001010102030405060708090a0b0c"
    "00180102030405060708090a0b0c0d0e0f100000000000000001"
)
EPHEMERAL_KEY = H("0288ef00023598499cb6c940146d050d2b1fb914198c327f76aad590bead68b6")
EPHEMERAL_PUBKEY = H("039a003ba6517b473fa0cd74aefe99dadfdb34627f90fec6362df85803908f53a5")
HANDSHAKE_READ_KEY = H("4f9fac6de7567d1e3b1241dffe90f662")

HANDSHAKE_ENR_PACKET = H(
    "00000000000000000000000000000000088b3d4342774649305f313964a39e55"
    "ea96c005ad539c8c7560413a7008f16c9e6d2f43bbea8814a546b7409ce783d3"
    "4c4f53245d08da4bb23698868350aaad22e3ab8dd034f548a1c43cd246be9856"
    "2fafa0a1fa86d8e7a3b95ae78cc2b988ded6a5b59eb83ad58097252188b902b2"
    "1481e30e5e285f19735796706adff216ab862a9186875f9494150c4ae06fa4d1"
    "f0396c93f215fa4ef524e0ed04c3c21e39b1868e1ca8105e585ec17315e755e6"
    "cfc4dd6cb7fd8e1a1f55e49b4b5eb024221482105346f3c82b15fdaae36a3bb1"
    "2a494683b4a3c7f2ae41306252fed84785e2bbff3b022812d0882f06978df84a"
    "80d443972213342d04b9048fc3b1d5fcb1df0f822152eced6da4d3f6df27e70e"
    "4539717307a0208cd208d65093ccab5aa596a34d7511401987662d8cf62b1394"
    "71"
)
HANDSHAKE_ENR_READ_KEY = H("53b1c075f41876423154e157470c2f48")

# The generator of secp256k1, compressed, from SEC 2 section 2.4.1.
GENERATOR = H("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")


def _public_key(secret_key: bytes) -> bytes:
    # The vectors give no public keys for the node keys, so each is computed as k G.
    return discv5.ecdh(secret_key, GENERATOR)


# ---- Ordinary message packets ----


def test_seal_ping_packet():
    packet = discv5.seal_message(bytes(16), SRC_ID, DEST_ID, MASKING_IV, NONCE, PING_ENR_SEQ_2)
    assert packet == PING_PACKET


def test_seal_message_up_to_the_size_limit():
    # The packet has 16 + 23 + 32 bytes before the message, and the message adds a 16-byte tag.
    packet = discv5.seal_message(bytes(16), SRC_ID, DEST_ID, MASKING_IV, NONCE, bytes(1193))
    assert len(packet) == 1280
    assert discv5.open_message(bytes(16), SRC_ID, DEST_ID, packet) == bytes(1193)


def test_seal_message_over_the_size_limit():
    message = "invalid packet: EthLib.Networking.Discv5.PacketError.size 1281"
    with raises(discv5.Discv5Error, message) as info:
        discv5.seal_message(bytes(16), SRC_ID, DEST_ID, MASKING_IV, NONCE, bytes(1194))
    assert info.value.code == 1


def test_open_ping_packet():
    assert discv5.open_message(bytes(16), SRC_ID, DEST_ID, PING_PACKET) == PING_ENR_SEQ_2


def test_open_message_of_another_source():
    with raises(discv5.Discv5Error, "no session key for the source node ID") as info:
        discv5.open_message(bytes(16), DEST_ID, DEST_ID, PING_PACKET)
    assert info.value.code == 205


def test_open_message_of_a_whoareyou():
    with raises(discv5.Discv5Error, "packet has flag 1, not 0") as info:
        discv5.open_message(bytes(16), SRC_ID, DEST_ID, WHOAREYOU_PACKET)
    assert info.value.code == 204


# ---- WHOAREYOU ----


def test_make_whoareyou_packet():
    packet, challenge_data = discv5.make_whoareyou(
        DEST_ID, MASKING_IV, WHOAREYOU_NONCE, ID_NONCE, 0
    )
    assert packet == WHOAREYOU_PACKET
    assert challenge_data == WHOAREYOU_CHALLENGE_DATA


def test_read_whoareyou_packet():
    c = discv5.read_whoareyou(DEST_ID, WHOAREYOU_PACKET)
    assert c["nonce"] == WHOAREYOU_NONCE
    assert c["id_nonce"] == ID_NONCE
    assert c["enr_seq"] == 0
    assert c["challenge_data"] == WHOAREYOU_CHALLENGE_DATA


def test_read_whoareyou_of_a_message():
    with raises(discv5.Discv5Error, "packet has flag 0, not 1") as info:
        discv5.read_whoareyou(DEST_ID, PING_PACKET)
    assert info.value.code == 204


# ---- Handshake message packets ----


def test_seal_handshake_packet():
    packet, keys = discv5.seal_handshake(
        EPHEMERAL_KEY,
        NODE_A_KEY,
        HANDSHAKE_CHALLENGE_DATA,
        SRC_ID,
        DEST_ID,
        _public_key(NODE_B_KEY),
        MASKING_IV,
        NONCE,
        b"",
        PING_ENR_SEQ_1,
    )
    assert packet == HANDSHAKE_PACKET
    assert keys.initiator_key == HANDSHAKE_READ_KEY


def test_open_handshake_packet():
    r = discv5.open_handshake(
        NODE_B_KEY, HANDSHAKE_CHALLENGE_DATA, DEST_ID, _public_key(NODE_A_KEY), HANDSHAKE_PACKET
    )
    assert r["src_id"] == SRC_ID
    assert r["record"] == b""
    assert r["plaintext"] == PING_ENR_SEQ_1
    assert r["keys"].initiator_key == HANDSHAKE_READ_KEY


def test_open_handshake_packet_with_enr():
    r = discv5.open_handshake(
        NODE_B_KEY,
        WHOAREYOU_CHALLENGE_DATA,
        DEST_ID,
        _public_key(NODE_A_KEY),
        HANDSHAKE_ENR_PACKET,
    )
    assert r["src_id"] == SRC_ID
    # The record is an RLP list, so it starts with a list prefix.
    assert r["record"][0] >= 0xC0
    assert r["plaintext"] == PING_ENR_SEQ_1
    assert r["keys"].initiator_key == HANDSHAKE_ENR_READ_KEY


def test_open_handshake_under_another_challenge():
    # The ID signature covers the challenge data, so another challenge fails to verify.
    with raises(discv5.Discv5Error, "ID signature does not verify") as info:
        discv5.open_handshake(
            NODE_B_KEY,
            WHOAREYOU_CHALLENGE_DATA,
            DEST_ID,
            _public_key(NODE_A_KEY),
            HANDSHAKE_PACKET,
        )
    assert info.value.code == 305


def test_open_handshake_of_a_message():
    with raises(discv5.Discv5Error, "packet has flag 0, not 2") as info:
        discv5.open_handshake(
            NODE_B_KEY, HANDSHAKE_CHALLENGE_DATA, DEST_ID, _public_key(NODE_A_KEY), PING_PACKET
        )
    assert info.value.code == 310
