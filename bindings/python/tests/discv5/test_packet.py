"""discv5 packets against the test vectors of the discv5 wire protocol."""

import pytest

from ethlib.networking import discv5
from raising import raises

# The test vectors of the discv5 wire protocol.
#
# File: discv5/discv5-wire-test-vectors.md
# Repository: ethereum/devp2p
# Commit: 88f1c80800d622cc3a542a2125bbe33cc18c9f9c

H = bytes.fromhex

SRC_ID = H("aaaa8419e9f49d0083561b48287df592939a8d19947d8c0ef88f2a4856a69fbb")
DEST_ID = H("bbbb9d047f0488c0b5a93c1c3f2d8bafc7c8ff337024a55434a0d0555de64db9")
NONCE = H("ffffffffffffffffffffffff")

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

HANDSHAKE_PACKET = H(
    "00000000000000000000000000000000088b3d4342774649305f313964a39e55"
    "ea96c005ad521d8c7560413a7008f16c9e6d2f43bbea8814a546b7409ce783d3"
    "4c4f53245d08da4bb252012b2cba3f4f374a90a75cff91f142fa9be3e0a5f3ef"
    "268ccb9065aeecfd67a999e7fdc137e062b2ec4a0eb92947f0d9a74bfbf44dfb"
    "a776b21301f8b65efd5796706adff216ab862a9186875f9494150c4ae06fa4d1"
    "f0396c93f215fa4ef524f1eadf5f0f4126b79336671cbcf7a885b1f8bd2a5d83"
    "9cf8"
)

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

EPHEMERAL_PUBKEY = H("039a003ba6517b473fa0cd74aefe99dadfdb34627f90fec6362df85803908f53a5")

ALL_PACKETS = [PING_PACKET, WHOAREYOU_PACKET, HANDSHAKE_PACKET, HANDSHAKE_ENR_PACKET]


def test_ping_packet():
    p = discv5.decode_packet(DEST_ID, PING_PACKET)
    assert (p["flag"], p["src_id"], p["nonce"]) == (0, SRC_ID, NONCE)
    assert p["masking_iv"] == bytes(16)
    plaintext = discv5.decrypt_message(bytes(16), NONCE, p["message"], p["message_ad"])
    assert plaintext == PING_ENR_SEQ_2


def test_whoareyou_packet():
    p = discv5.decode_packet(DEST_ID, WHOAREYOU_PACKET)
    assert p["flag"] == 1
    assert p["nonce"] == H("0102030405060708090a0b0c")
    assert p["id_nonce"] == H("0102030405060708090a0b0c0d0e0f10")
    assert p["enr_seq"] == 0
    assert p["message"] == b""
    # The challenge data of the vector is the masking IV, then the unmasked header.
    challenge_data = H(
        "000000000000000000000000000000006469736376350001010102030405060708090a0b0c"
        "00180102030405060708090a0b0c0d0e0f100000000000000000"
    )
    assert p["message_ad"] == challenge_data


def test_handshake_packet():
    p = discv5.decode_packet(DEST_ID, HANDSHAKE_PACKET)
    assert (p["flag"], p["src_id"], p["nonce"]) == (2, SRC_ID, NONCE)
    assert len(p["id_signature"]) == 64
    assert p["ephemeral_pubkey"] == EPHEMERAL_PUBKEY
    assert p["record"] == b""
    read_key = H("4f9fac6de7567d1e3b1241dffe90f662")
    plaintext = discv5.decrypt_message(read_key, NONCE, p["message"], p["message_ad"])
    assert plaintext == PING_ENR_SEQ_1


def test_handshake_packet_with_enr():
    p = discv5.decode_packet(DEST_ID, HANDSHAKE_ENR_PACKET)
    assert (p["flag"], p["src_id"]) == (2, SRC_ID)
    assert p["ephemeral_pubkey"] == EPHEMERAL_PUBKEY
    # The record is an RLP list, so it starts with a list prefix.
    assert p["record"][0] >= 0xC0
    read_key = H("53b1c075f41876423154e157470c2f48")
    plaintext = discv5.decrypt_message(read_key, NONCE, p["message"], p["message_ad"])
    assert plaintext == PING_ENR_SEQ_1


@pytest.mark.parametrize("packet", ALL_PACKETS)
def test_reencode(packet):
    assert discv5.reencode_packet(DEST_ID, packet) == packet


def test_aes_gcm_vector():
    key = H("9f2d77db7004bf8a1a85107ac686990b")
    nonce = H("27b5af763c446acd2749fe8e")
    plaintext = H("01c20101")
    ad = H("93a7400fa0d6a694ebc24d5cf570f65d04215b6ac00757875e3f3a5f42107903")
    message = H("a5d12a2d94b8ccb3ba55558229867dc13bfa3648")
    assert discv5.encrypt_message(key, nonce, plaintext, ad) == message
    assert discv5.decrypt_message(key, nonce, message, ad) == plaintext


def test_changed_tag_fails():
    p = discv5.decode_packet(DEST_ID, PING_PACKET)
    message = p["message"][:-1] + bytes([p["message"][-1] ^ 1])
    with raises(ValueError, "message does not authenticate"):
        discv5.decrypt_message(bytes(16), NONCE, message, p["message_ad"])


def test_wrong_destination():
    # Under another destination ID, the header unmasks to bytes without "discv5".
    with raises(ValueError, "invalid packet: EthLib.Networking.Discv5.PacketError.protocolId"):
        discv5.decode_packet(SRC_ID, PING_PACKET)


def test_packet_too_short():
    with raises(ValueError, "invalid packet: EthLib.Networking.Discv5.PacketError.size 62"):
        discv5.decode_packet(DEST_ID, PING_PACKET[:62])


def test_packet_too_long():
    with raises(ValueError, "invalid packet: EthLib.Networking.Discv5.PacketError.size 1281"):
        discv5.decode_packet(DEST_ID, PING_PACKET + bytes(1281 - len(PING_PACKET)))


def test_whoareyou_with_a_message():
    # A WHOAREYOU packet carries no message, so one more byte is rejected.
    with raises(
        ValueError, "invalid packet: EthLib.Networking.Discv5.PacketError.whoareyouMessage"
    ):
        discv5.decode_packet(DEST_ID, WHOAREYOU_PACKET + b"\x00")
