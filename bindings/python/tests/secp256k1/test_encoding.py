"""The SEC 1 encodings of a public key, through the exports that read or write one."""

import pytest

from ethlib.cryptography import secp256k1

# The coordinates of the generator `G`, as SEC 2 v2 §2.4.1 prints them.
GX = "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"
GY = "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"

G_COMPRESSED = bytes.fromhex("02" + GX)
G_UNCOMPRESSED = bytes.fromhex("04" + GX + GY)

ONE = (1).to_bytes(32, "big")


@pytest.mark.parametrize("encoding", [G_COMPRESSED, G_UNCOMPRESSED])
def test_decode_generator(encoding: bytes) -> None:
    # ECDH with the private key 1 returns the x of the decoded point.
    # For the compressed form, the decoder recovers y by a square root.
    assert secp256k1.ecdh(ONE, encoding) == bytes.fromhex(GX)


def test_encode_generator() -> None:
    # The private key 1 signs with the public key G, and recovery returns it uncompressed.
    msg_hash = bytes(31) + b"\x01"
    signature = secp256k1.sign(ONE, msg_hash)
    assert secp256k1.recover(msg_hash, signature[:64], signature[64]) == G_UNCOMPRESSED


REJECTED = [
    # G with y + 1 is off the curve.
    ("04" + GX + GY[:-1] + "9", "not on the curve"),
    # x = 2^256 - 1 is not below p.
    ("02" + "FF" * 32, "not below p"),
    # x = 0 has no point: 7 is not a square mod p.
    ("02" + "00" * 32, "no point of the curve has this x"),
    # 05 is no prefix.
    ("05" + GX, "prefix: 5"),
    # The 64 coordinate bytes alone, without a prefix, have no valid length.
    (GX + GY, "size: 64"),
]


@pytest.mark.parametrize("encoding, error", REJECTED)
def test_decode_rejects(encoding: str, error: str) -> None:
    with pytest.raises(ValueError, match=error):
        secp256k1.ecdh(ONE, bytes.fromhex(encoding))
