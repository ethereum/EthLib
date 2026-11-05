"""The RLPx handshake against the secrets of EIP-8."""

import pytest

from ethlib.networking import rlpx
from raising import raises

from .vectors import (
    ACK_2,
    ACK_3,
    AES_SECRET,
    AUTH_2,
    AUTH_3,
    EPHEMERAL_KEY_A,
    EPHEMERAL_KEY_B,
    INGRESS_MAC_FOO,
    MAC_SECRET,
    NONCE_A,
    NONCE_B,
    STATIC_KEY_A,
    STATIC_KEY_B,
    public_key,
    rlp_list,
)

KEYS_A = (STATIC_KEY_A, EPHEMERAL_KEY_A, NONCE_A)
KEYS_B = (STATIC_KEY_B, EPHEMERAL_KEY_B, NONCE_B)


def _parts(secrets: bytes) -> tuple[bytes, bytes, bytes, bytes]:
    # aes-secret | mac-secret | egress digest | ingress digest
    return secrets[0:32], secrets[32:64], secrets[64:96], secrets[96:128]


def test_eip8_recipient_secrets() -> None:
    aes, mac, _, ingress = _parts(rlpx.recipient_secrets(*KEYS_B, AUTH_2, ACK_2, b"foo"))
    assert aes == AES_SECRET
    assert mac == MAC_SECRET
    assert ingress == INGRESS_MAC_FOO


def test_eip8_initiator_secrets() -> None:
    # A's egress state is B's ingress state, so its digest after "foo" is the same.
    aes, mac, egress, _ = _parts(rlpx.finish(*KEYS_A, AUTH_2, ACK_2, b"foo"))
    assert aes == AES_SECRET
    assert mac == MAC_SECRET
    assert egress == INGRESS_MAC_FOO


def test_eip8_extra_elements() -> None:
    # Auth₃ and Ack₃ carry other versions and more list elements, which both sides ignore.
    a = _parts(rlpx.finish(*KEYS_A, AUTH_3, ACK_3, b"probe"))
    b = _parts(rlpx.recipient_secrets(*KEYS_B, AUTH_3, ACK_3, b"probe"))
    assert a[:2] == b[:2]
    assert (a[2], a[3]) == (b[3], b[2])


def test_fields_of_auth() -> None:
    # The signature of Auth₂ used another nonce, so only the other fields can match.
    auth = rlpx.make_auth(
        *KEYS_A, b"\x04" + public_key(STATIC_KEY_B), EPHEMERAL_KEY_B, bytes(16), b""
    )
    ours = rlp_list(rlpx.ecies_decrypt(STATIC_KEY_B, auth[:2], auth[2:]))
    theirs = rlp_list(rlpx.ecies_decrypt(STATIC_KEY_B, AUTH_2[:2], AUTH_2[2:]))
    assert ours[1:4] == theirs[1:4]


@pytest.mark.parametrize("padding", [b"", bytes(100), bytes(range(256))])
def test_round_trip(padding: bytes) -> None:
    auth = rlpx.make_auth(
        *KEYS_A, b"\x04" + public_key(STATIC_KEY_B), EPHEMERAL_KEY_B, bytes(16), padding
    )
    ack, b = rlpx.respond(*KEYS_B, EPHEMERAL_KEY_A, bytes(range(16)), padding, auth, b"x")
    a = rlpx.finish(*KEYS_A, auth, ack, b"x")
    a_aes, a_mac, a_egress, a_ingress = _parts(a)
    b_aes, b_mac, b_egress, b_ingress = _parts(b)
    assert (a_aes, a_mac) == (b_aes, b_mac)
    assert (a_egress, a_ingress) == (b_ingress, b_egress)


def test_changed_auth_rejected() -> None:
    auth = bytearray(AUTH_2)
    auth[100] ^= 1
    with raises(ValueError, "tag does not match"):
        rlpx.recipient_secrets(*KEYS_B, bytes(auth), ACK_2, b"")


def test_wrong_size_prefix_rejected() -> None:
    # Code 102 names a packet whose size prefix does not count the bytes after it.
    with raises(rlpx.RlpxError, "packet of 438 bytes does not match its size prefix") as info:
        rlpx.recipient_secrets(*KEYS_B, AUTH_2 + b"\x00", ACK_2, b"")
    assert info.value.code == 102


def test_changed_tag_keeps_ecies_code() -> None:
    # A wrong ECIES tag keeps the code of ECIES, 5, inside the handshake.
    auth = AUTH_2[:-1] + bytes([AUTH_2[-1] ^ 1])
    with raises(rlpx.RlpxError, "tag does not match") as info:
        rlpx.recipient_secrets(*KEYS_B, auth, ACK_2, b"")
    assert info.value.code == 5


def _rlp_bytes(data: bytes) -> bytes:
    # Every byte string here is under 56 bytes, or exactly 64 or 65 bytes.
    if len(data) == 1 and data[0] < 0x80:
        return data
    if len(data) < 56:
        return bytes([0x80 + len(data)]) + data
    return bytes([0xB8, len(data)]) + data


def _rlp_list(items: list[bytes]) -> bytes:
    payload = b"".join(_rlp_bytes(item) for item in items)
    assert 56 <= len(payload) < 256
    return bytes([0xF8, len(payload)]) + payload


def _packet_to_b(body: bytes) -> bytes:
    # The size prefix counts the 113 bytes that ECIES adds.
    size = (len(body) + 113).to_bytes(2, "big")
    return size + rlpx.ecies_encrypt(
        b"\x04" + public_key(STATIC_KEY_B), EPHEMERAL_KEY_A, bytes(16), size, body
    )


def _code(call, message: str) -> int:
    with raises(rlpx.RlpxError, message) as info:
        call()
    return info.value.code


def test_handshake_codes() -> None:
    sig = bytes(64) + b"\x00"
    pub = public_key(STATIC_KEY_A)
    recipient = b"\x04" + public_key(STATIC_KEY_B)
    # A nonce of the wrong size is a bad argument, with code 0.
    assert (
        _code(
            lambda: rlpx.finish(STATIC_KEY_A, EPHEMERAL_KEY_A, b"", AUTH_2, ACK_2, b""),
            "bad nonce size: 0, expected 32",
        )
        == 0
    )

    # 101: the encrypted message does not fit in a 16-bit size.
    def too_long():
        return rlpx.make_auth(*KEYS_A, recipient, EPHEMERAL_KEY_B, bytes(16), bytes(65536))

    assert _code(too_long, "encrypted message has 65818 bytes, more than 65535") == 101
    # 103: the body is not an RLP list.
    assert (
        _code(
            lambda: rlpx.recipient_secrets(*KEYS_B, _packet_to_b(b"\x00"), ACK_2, b""),
            "message body is not an RLP list of the expected fields",
        )
        == 103
    )
    # 104: the initiator's public key is not on the curve.
    bad_key = _rlp_list([sig, bytes(64), NONCE_A, b"\x04"])
    assert (
        _code(
            lambda: rlpx.recipient_secrets(*KEYS_B, _packet_to_b(bad_key), ACK_2, b""),
            "point is not on the curve",
        )
        == 104
    )
    # 105: the recovery id of the signature is 2.
    bad_id = _rlp_list([bytes(64) + b"\x02", pub, NONCE_A, b"\x04"])
    assert (
        _code(
            lambda: rlpx.recipient_secrets(*KEYS_B, _packet_to_b(bad_id), ACK_2, b""),
            "bad recovery id: 2, expected 0 or 1",
        )
        == 105
    )
