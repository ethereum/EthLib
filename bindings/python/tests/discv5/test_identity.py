"""discv5 handshake cryptography against the test vectors of the discv5 wire protocol."""

from ethlib.networking import discv5
from raising import raises

# The test vectors of the discv5 wire protocol.
#
# File: discv5/discv5-wire-test-vectors.md
# Repository: ethereum/devp2p
# Commit: 88f1c80800d622cc3a542a2125bbe33cc18c9f9c

H = bytes.fromhex

NODE_ID_A = H("aaaa8419e9f49d0083561b48287df592939a8d19947d8c0ef88f2a4856a69fbb")
NODE_ID_B = H("bbbb9d047f0488c0b5a93c1c3f2d8bafc7c8ff337024a55434a0d0555de64db9")
CHALLENGE_DATA = H(
    "000000000000000000000000000000006469736376350001010102030405060708090a0b0c"
    "00180102030405060708090a0b0c0d0e0f100000000000000000"
)
KEY = H("fb757dc581730490a1d7a00deea65e9b1936924caaea8f44d476014856b68736")


def test_ecdh():
    public_key = H("039961e4c2356d61bedb83052c115d311acb3a96f5777296dcf297351130266231")
    expected = H("033b11a2a1f214567e1537ce5e509ffd9b21373247f2a3ff6841f4976f53165e7e")
    assert discv5.ecdh(KEY, public_key) == expected


def test_key_derivation():
    dest_pubkey = H("0317931e6e0840220642f230037d285d122bc59063221ef3226b1f403ddc69ca91")
    keys = discv5.derive_keys(KEY, dest_pubkey, NODE_ID_A, NODE_ID_B, CHALLENGE_DATA)
    assert keys.initiator_key == H("dccc82d81bd610f4f76d3ebe97a40571")
    assert keys.recipient_key == H("ac74bb8773749920b0d3a8881c173ec5")


EPHEMERAL_PUBKEY = H("039961e4c2356d61bedb83052c115d311acb3a96f5777296dcf297351130266231")
ID_SIGNATURE = H(
    "94852a1e2318c4e5e9d422c98eaf19d1d90d876b29cd06ca7cb7546d0fff7b48"
    "4fe86c09a064fe72bdbef73ba8e9c34df0cd2b53e9d65528c2c7f336d5dfc6e6"
)


def test_id_sign():
    assert discv5.id_sign(KEY, CHALLENGE_DATA, EPHEMERAL_PUBKEY, NODE_ID_B) == ID_SIGNATURE


# The generator of secp256k1, compressed, from SEC 2 section 2.4.1.
GENERATOR = H("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")


def _public_key(secret_key: bytes) -> bytes:
    # The vectors give no public key for the static key, so it is computed as k G.
    return discv5.ecdh(secret_key, GENERATOR)


def test_id_verify():
    # The vectors say that the signature can be checked in reverse, under the signer's key.
    public_key = _public_key(KEY)
    assert discv5.id_verify(public_key, CHALLENGE_DATA, EPHEMERAL_PUBKEY, NODE_ID_B, ID_SIGNATURE)


def test_id_verify_rejects_another_node():
    public_key = _public_key(KEY)
    assert not discv5.id_verify(
        public_key, CHALLENGE_DATA, EPHEMERAL_PUBKEY, NODE_ID_A, ID_SIGNATURE
    )


def test_ecdh_of_the_generator_is_the_public_key():
    # The public key of the private key 1 is the generator itself.
    assert _public_key((1).to_bytes(32, "big")) == GENERATOR


def test_log_distance_equal_ids():
    assert discv5.log_distance(NODE_ID_A, NODE_ID_A) == 0


def test_log_distance_last_bit():
    # IDs that differ only in their last bit have distance 1, one bit long.
    other = NODE_ID_A[:-1] + bytes([NODE_ID_A[-1] ^ 1])
    assert discv5.log_distance(NODE_ID_A, other) == 1


def test_log_distance_first_bit():
    # aa = 1010_1010 and bb = 1011_1011 first differ in bit 4 of the first byte, from the top.
    # So the XOR has 256 - 3 = 253 bits.
    assert discv5.log_distance(NODE_ID_A, NODE_ID_B) == 253
    assert discv5.log_distance(NODE_ID_B, NODE_ID_A) == 253


def test_log_distance_rejects_short_id():
    with raises(ValueError, "node ID has 31 bytes, not 32"):
        discv5.log_distance(NODE_ID_A[:31], NODE_ID_B)
