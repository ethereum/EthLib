"""RLPx frames against a transcription of the sections "Framing" and "MAC" of rlpx.md."""

# The source is rlpx.md of ethereum/devp2p at commit 88f1c80800d622cc3a542a2125bbe33cc18c9f9c.
#
# rlpx.md has no framing vectors, so the model below writes the frames from its text.
# It uses only two primitives of the bindings, each checked by its own vector suite.
# The primitives are AES-256 on one block and Keccak-256 of a whole string.
# Counter mode, padding, the header, the MAC seeds and the MAC updates are the model's own.

import random

import pytest

from ethlib.cryptography import aes, keccak
from ethlib.errors import RlpxError
from ethlib.networking import rlpx
from raising import raises

from .vectors import ACK_2, AES_SECRET, AUTH_2, INGRESS_MAC_FOO, MAC_SECRET, NONCE_A, NONCE_B


def _rlp_bytes(data: bytes) -> bytes:
    """The RLP encoding of a byte string."""
    if len(data) == 1 and data[0] < 0x80:
        return data
    return _rlp_prefix(0x80, len(data)) + data


def _rlp_prefix(offset: int, length: int) -> bytes:
    """The RLP prefix of a payload of `length` bytes."""
    if length < 56:
        return bytes([offset + length])
    size = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([offset + 55 + len(size)]) + size


def _rlp_list(items: list[bytes]) -> bytes:
    """The RLP encoding of a list of byte strings."""
    payload = b"".join(_rlp_bytes(item) for item in items)
    return _rlp_prefix(0xC0, len(payload)) + payload


def _xor(a: bytes, b: bytes) -> bytes:
    return bytes(x ^ y for x, y in zip(a, b, strict=True))


class Direction:
    """One direction of a session, as rlpx.md describes it."""

    def __init__(self, aes_secret: bytes, mac_secret: bytes, mac_init: bytes) -> None:
        self.aes_secret = aes_secret
        self.mac_secret = mac_secret
        # The cipher stream starts at the zero counter block.
        self.counter = 0
        # A Keccak-256 state is the string it has absorbed.
        self.mac = mac_init

    def _keystream(self, size: int) -> bytes:
        out = b""
        for _ in range(size // 16):
            out += aes.encrypt_block(self.aes_secret, self.counter.to_bytes(16, "big"))
            self.counter = (self.counter + 1) % 2**128
        return out

    def _digest(self) -> bytes:
        return keccak.keccak256(self.mac)[:16]

    def write(self, data: bytes) -> bytes:
        # header = frame-size (3 bytes) || header-data || header-padding
        header = len(data).to_bytes(3, "big") + bytes([0xC2, 0x80, 0x80])
        header += bytes(16 - len(header))
        header_ct = _xor(header, self._keystream(16))
        # header-mac-seed = aes(mac-secret, keccak256.digest(egress-mac)[:16]) ^ header-ciphertext
        self.mac += _xor(aes.encrypt_block(self.mac_secret, self._digest()), header_ct)
        header_mac = self._digest()
        padded = data + bytes(-len(data) % 16)
        frame_ct = _xor(padded, self._keystream(len(padded)))
        # frame-mac-seed = aes(mac-secret, keccak256.digest(egress-mac)[:16]) ^ that digest
        self.mac += frame_ct
        seed = _xor(aes.encrypt_block(self.mac_secret, self._digest()), self._digest())
        self.mac += seed
        return header_ct + header_mac + frame_ct + self._digest()


SIZES = [0, 1, 15, 16, 17, 31, 32, 255, 1024, 4097]


def _secrets(seed: int) -> tuple[bytes, bytes, bytes]:
    rng = random.Random(seed)
    return rng.randbytes(32), rng.randbytes(32), rng.randbytes(rng.randrange(0, 300))


@pytest.mark.parametrize("seed", range(4))
def test_write_frames(seed: int) -> None:
    aes_secret, mac_secret, mac_init = _secrets(seed)
    rng = random.Random(1000 + seed)
    datas = [rng.randbytes(size) for size in SIZES]
    model = Direction(aes_secret, mac_secret, mac_init)
    expected = b"".join(model.write(data) for data in datas)
    assert rlpx.write_frames(aes_secret, mac_secret, mac_init, _rlp_list(datas)) == expected


@pytest.mark.parametrize("seed", range(4))
def test_read_frames(seed: int) -> None:
    aes_secret, mac_secret, mac_init = _secrets(seed)
    rng = random.Random(2000 + seed)
    datas = [rng.randbytes(size) for size in SIZES]
    model = Direction(aes_secret, mac_secret, mac_init)
    frames = b"".join(model.write(data) for data in datas)
    assert rlpx.read_frames(aes_secret, mac_secret, mac_init, frames) == _rlp_list(datas)


def test_eip8_session() -> None:
    # A sends to B from (mac-secret ^ recipient-nonce) || auth, which EIP-8 gives as B's ingress.
    a_to_b = _xor(MAC_SECRET, NONCE_B) + AUTH_2
    assert keccak.keccak256(a_to_b + b"foo") == INGRESS_MAC_FOO
    datas = [b"hello", bytes(100)]
    frames = rlpx.write_frames(AES_SECRET, MAC_SECRET, a_to_b, _rlp_list(datas))
    model = Direction(AES_SECRET, MAC_SECRET, a_to_b)
    assert frames == b"".join(model.write(data) for data in datas)
    assert rlpx.read_frames(AES_SECRET, MAC_SECRET, a_to_b, frames) == _rlp_list(datas)
    # B sends to A from (mac-secret ^ initiator-nonce) || ack, so its MAC rejects A's frames.
    b_to_a = _xor(MAC_SECRET, NONCE_A) + ACK_2
    with raises(RlpxError, "header MAC does not match") as err:
        rlpx.read_frames(AES_SECRET, MAC_SECRET, b_to_a, frames)
    assert err.value.code == 203


def _frames() -> tuple[bytes, bytes, bytes, bytes]:
    aes_secret, mac_secret, mac_init = _secrets(7)
    frame = Direction(aes_secret, mac_secret, mac_init).write(b"frame data")
    return aes_secret, mac_secret, mac_init, frame


@pytest.mark.parametrize(
    "position, code, message",
    [
        (0, 203, "header MAC does not match"),
        (16, 203, "header MAC does not match"),
        (32, 204, "frame MAC does not match"),
        (48, 204, "frame MAC does not match"),
    ],
    ids=["0-203", "16-203", "32-204", "48-204"],
)
def test_rejects_changed_byte(position: int, code: int, message: str) -> None:
    # Bytes 0 to 31 are the header and its MAC, then the frame and its MAC.
    aes_secret, mac_secret, mac_init, frame = _frames()
    changed = bytearray(frame)
    changed[position] ^= 1
    with raises(RlpxError, message) as err:
        rlpx.read_frames(aes_secret, mac_secret, mac_init, bytes(changed))
    assert err.value.code == code


@pytest.mark.parametrize(
    "cut, message",
    [
        (1, "input has 63 bytes, fewer than 64"),
        (16, "input has 48 bytes, fewer than 64"),
        (31, "input has 33 bytes, fewer than 64"),
        (33, "input has 31 bytes, fewer than 32"),
    ],
    ids=["1", "16", "31", "33"],
)
def test_rejects_truncated(cut: int, message: str) -> None:
    aes_secret, mac_secret, mac_init, frame = _frames()
    with raises(RlpxError, message) as err:
        rlpx.read_frames(aes_secret, mac_secret, mac_init, frame[:-cut])
    assert err.value.code == 202


def test_rejects_bad_inputs() -> None:
    aes_secret, mac_secret, mac_init, frame = _frames()
    with raises(RlpxError, "bad secret size: 31, expected 32") as err:
        rlpx.write_frames(aes_secret[:31], mac_secret, mac_init, _rlp_list([b""]))
    assert err.value.code == 0
    with raises(RlpxError, "frames is not an RLP list of byte strings") as err:
        rlpx.write_frames(aes_secret, mac_secret, mac_init, b"\x01")
    assert err.value.code == 0
    with raises(RlpxError, "frame data has 16777216 bytes, more than 2^24 - 1") as err:
        rlpx.write_frames(aes_secret, mac_secret, mac_init, _rlp_list([bytes(2**24)]))
    assert err.value.code == 201
    with raises(TypeError, "argument 4 must be bytes"):
        rlpx.read_frames(aes_secret, mac_secret, mac_init, "frame")  # ty: ignore[invalid-argument-type]
