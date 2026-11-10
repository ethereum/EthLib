"""secp256k1 libp2p identities against the key vector of the peer ID specification."""

import pytest

from ethlib.networking.libp2p import identity
from raising import raises

# The keys are the secp256k1 rows of "Test vectors" in peer-ids/peer-ids.md of libp2p/specs.
# The pinned commit is c750236de43cd8b246a824b377dfdb26bae686db.
# The private key row is the protobuf 08 02 12 20 of key type 2, then the 32-byte secret.
SECRET = bytes.fromhex("53DADF1D5A164D6B4ACDB15E24AA4C5B1D3461BDBD42ABEDB0A4404D56CED8FB")
PUBLIC_KEY = bytes.fromhex(
    "08021221037777e994e452c21604f91de093ce415f5432f701dd8cd1a7a6fea0e630bfca99"
)

# The key protobuf has 37 bytes, at most 42, so the peer ID is its identity multihash ("Peer Ids").
# That multihash is the code 0, the length 37 = 0x25, then the protobuf.
PEER_ID = bytes.fromhex("0025") + PUBLIC_KEY

# The order n of the group, the prime p of the field and the x of the generator G are from SEC 2.
# They are in its section 2.4.1.
ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
PRIME = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
GX = "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"

# The ends of the range of secrets: 1 gives G, whose y is even, and n - 1 gives -G, whose y is odd.
ENDS = [
    (1, bytes.fromhex("0802122102" + GX)),
    (ORDER - 1, bytes.fromhex("0802122103" + GX)),
]


def test_public_key_of_the_vector_secret() -> None:
    assert identity.public_key(SECRET) == PUBLIC_KEY


def test_peer_id_of_the_vector_key() -> None:
    assert identity.peer_id(PUBLIC_KEY) == PEER_ID


def test_peer_id_decodes_back_to_its_key() -> None:
    assert identity.decode_peer_id(PEER_ID) == PUBLIC_KEY


@pytest.mark.parametrize(("secret", "key"), ENDS)
def test_the_ends_of_the_secret_range(secret: int, key: bytes) -> None:
    assert identity.public_key(secret.to_bytes(32, "big")) == key
    assert identity.peer_id(key) == bytes.fromhex("0025") + key
    assert identity.decode_peer_id(bytes.fromhex("0025") + key) == key


IDENTITY = "libp2p identity rejected: EthLib.Networking.Libp2p.IdentityError."


@pytest.mark.parametrize("secret", [0, ORDER, 2**256 - 1])
def test_public_key_refuses_a_secret_outside_the_range(secret: int) -> None:
    with raises(identity.Libp2pIdentityError, IDENTITY + "privateKey") as info:
        identity.public_key(secret.to_bytes(32, "big"))
    assert info.value.code == 3


def test_public_key_refuses_a_secret_of_31_bytes() -> None:
    with raises(identity.Libp2pIdentityError, "expected 32 bytes, got 31") as info:
        identity.public_key(SECRET[1:])
    assert info.value.code == 0


@pytest.mark.parametrize(
    "key",
    [
        # The point without its protobuf header.
        PUBLIC_KEY[4:],
        # Key type 3 is ECDSA, not secp256k1.
        bytes.fromhex("08031221") + PUBLIC_KEY[4:],
        # A 33-byte key with prefix 04, which no compressed point has.
        PUBLIC_KEY[:4] + b"\x04" + PUBLIC_KEY[5:],
        # An uncompressed point: EthLib reads only the 33-byte compressed form of the test vector.
        bytes.fromhex("08021241") + b"\x04" + bytes(64),
        # x = 0 has no point: 7 is not a square modulo p.
        PUBLIC_KEY[:5] + bytes(32),
        # x = p and x = p + 1 are not reduced, though p + 1 spells the x of a point.
        PUBLIC_KEY[:5] + PRIME.to_bytes(32, "big"),
        PUBLIC_KEY[:5] + (PRIME + 1).to_bytes(32, "big"),
        # 33 zero bytes, which some encodings use for the point at infinity.
        PUBLIC_KEY[:4] + bytes(33),
        # A byte after the protobuf.
        PUBLIC_KEY + b"\x00",
    ],
)
def test_peer_id_refuses_a_key_that_is_not_canonical(key: bytes) -> None:
    with raises(identity.Libp2pIdentityError, IDENTITY + "publicKey") as info:
        identity.peer_id(key)
    assert info.value.code == 1


@pytest.mark.parametrize(
    "identifier",
    [
        # A SHA-256 multihash, which names a key of more than 42 bytes.
        bytes.fromhex("1220") + bytes(32),
        # An identity multihash with the wrong length.
        bytes.fromhex("0024") + PUBLIC_KEY,
        b"",
        b"\x00",
    ],
)
def test_decode_peer_id_refuses_another_multihash(identifier: bytes) -> None:
    with raises(identity.Libp2pIdentityError, IDENTITY + "peerId") as info:
        identity.decode_peer_id(identifier)
    assert info.value.code == 2


def test_decode_peer_id_refuses_a_key_that_is_not_canonical() -> None:
    with raises(identity.Libp2pIdentityError, IDENTITY + "publicKey") as info:
        # The peer ID of x = 0, which no point of the curve has.
        identity.decode_peer_id(PEER_ID[:7] + bytes(32))
    assert info.value.code == 1


@pytest.mark.parametrize("identifier", [PEER_ID[:-1], PEER_ID + b"\x00"])
def test_decode_peer_id_refuses_a_key_of_another_length(identifier: bytes) -> None:
    # The prefix 00 25 is right, so the key itself is refused.
    with raises(identity.Libp2pIdentityError, IDENTITY + "publicKey") as info:
        identity.decode_peer_id(identifier)
    assert info.value.code == 1
