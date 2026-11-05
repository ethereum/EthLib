"""ECIES of RLPx against the handshake packets of EIP-8."""

# An EIP-8 packet authenticates its 2-byte size prefix as shared data.
# A packet of the older format has no prefix and no shared data.

import pytest

from ethlib.cryptography import keccak
from ethlib.networking import rlpx

from .vectors import (
    ACK_1,
    ACK_2,
    ACK_3,
    AUTH_1,
    AUTH_2,
    AUTH_3,
    EPHEMERAL_KEY_A,
    EPHEMERAL_KEY_B,
    NONCE_A,
    NONCE_B,
    STATIC_KEY_A,
    STATIC_KEY_B,
    public_key,
    rlp_list,
)


def _eip8(key: bytes, packet: bytes) -> bytes:
    size = int.from_bytes(packet[:2], "big")
    assert size == len(packet) - 2
    return rlpx.ecies_decrypt(key, packet[:2], packet[2:])


def test_auth_old_format() -> None:
    # sig: 65 | keccak256(ephemeral-pubk): 32 | pubk: 64 | nonce: 32 | 0x00
    body = rlpx.ecies_decrypt(STATIC_KEY_B, b"", AUTH_1)
    assert len(body) == 194
    assert body[65:97] == keccak.keccak256(public_key(EPHEMERAL_KEY_A))
    assert body[97:161] == public_key(STATIC_KEY_A)
    assert body[161:193] == NONCE_A
    assert body[193] == 0


def test_ack_old_format() -> None:
    # ephemeral-pubk: 64 | nonce: 32 | 0x00
    body = rlpx.ecies_decrypt(STATIC_KEY_A, b"", ACK_1)
    assert body[:97] == public_key(EPHEMERAL_KEY_B) + NONCE_B + b"\x00"


@pytest.mark.parametrize(
    ("packet", "version", "count"), [(AUTH_2, 4, 4), (AUTH_3, 56, 7)], ids=["auth2", "auth3"]
)
def test_auth_eip8(packet: bytes, version: int, count: int) -> None:
    # The RLP list [sig, initiator-pubk, initiator-nonce, auth-vsn, ...], then padding.
    items = rlp_list(_eip8(STATIC_KEY_B, packet))
    assert len(items[0]) == 65
    assert items[1:3] == [public_key(STATIC_KEY_A), NONCE_A]
    assert int.from_bytes(items[3], "big") == version
    assert len(items) == count


@pytest.mark.parametrize(
    ("packet", "version", "count"), [(ACK_2, 4, 3), (ACK_3, 57, 6)], ids=["ack2", "ack3"]
)
def test_ack_eip8(packet: bytes, version: int, count: int) -> None:
    # The RLP list [recipient-ephemeral-pubk, recipient-nonce, ack-vsn, ...], then padding.
    items = rlp_list(_eip8(STATIC_KEY_A, packet))
    assert items[0:2] == [public_key(EPHEMERAL_KEY_B), NONCE_B]
    assert int.from_bytes(items[2], "big") == version
    assert len(items) == count


def test_wrong_key_fails() -> None:
    with pytest.raises(ValueError, match="tag does not match"):
        rlpx.ecies_decrypt(STATIC_KEY_A, b"", AUTH_1)


def test_wrong_shared_data_fails() -> None:
    with pytest.raises(ValueError, match="tag does not match"):
        rlpx.ecies_decrypt(STATIC_KEY_B, b"\x01\xb4", AUTH_2[2:])


RECIPIENT = b"\x04" + public_key(STATIC_KEY_B)
IV = bytes(range(16))


@pytest.mark.parametrize("message", [b"", b"x", bytes(range(256)) * 3])
def test_round_trip(message: bytes) -> None:
    ciphertext = rlpx.ecies_encrypt(RECIPIENT, EPHEMERAL_KEY_A, IV, b"data", message)
    assert len(ciphertext) == 65 + 16 + len(message) + 32
    assert ciphertext[:65] == b"\x04" + public_key(EPHEMERAL_KEY_A)
    assert ciphertext[65:81] == IV
    assert rlpx.ecies_decrypt(STATIC_KEY_B, b"data", ciphertext) == message


@pytest.mark.parametrize("position", [0, 64, 65, 81, 90, -32, -1])
def test_changed_byte_fails(position: int) -> None:
    ciphertext = bytearray(rlpx.ecies_encrypt(RECIPIENT, EPHEMERAL_KEY_A, IV, b"", b"a message"))
    ciphertext[position] ^= 1
    with pytest.raises(ValueError, match="bad ephemeral public key|tag does not match"):
        rlpx.ecies_decrypt(STATIC_KEY_B, b"", bytes(ciphertext))


def test_zero_ephemeral_key_rejected() -> None:
    with pytest.raises(ValueError, match="the point at infinity is not a public key"):
        rlpx.ecies_encrypt(RECIPIENT, bytes(32), IV, b"", b"m")


def test_short_ciphertext_rejected() -> None:
    with pytest.raises(ValueError, match="ciphertext has 112 bytes, fewer than 113"):
        rlpx.ecies_decrypt(STATIC_KEY_B, b"", AUTH_1[:112])
