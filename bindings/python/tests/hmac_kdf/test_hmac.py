"""HMAC-SHA-256, HKDF and the Concatenation KDF against the test vectors of their RFCs.

Python's `hmac` and `hashlib` modules vouch for each value as an independent implementation.
"""

import hashlib
import hmac as std_hmac
import random

import pytest

from ethlib.cryptography.hmac import hmac_sha256
from ethlib.cryptography.kdf import concat_kdf, hkdf, hkdf_extract

# RFC 4231 §4.2 to §4.8, test cases 1 to 7: key, message and tag, in hex.
# Test case 5 truncates its tag to 128 bits.
RFC4231 = [
    ("0b" * 20, b"Hi There".hex(),
     "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"),
    (b"Jefe".hex(), b"what do ya want for nothing?".hex(),
     "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"),
    ("aa" * 20, "dd" * 50,
     "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"),
    ("0102030405060708090a0b0c0d0e0f10111213141516171819", "cd" * 50,
     "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b"),
    ("0c" * 20, b"Test With Truncation".hex(),
     "a3b6167473100ee06e0c796c2955552b"),
    ("aa" * 131, b"Test Using Larger Than Block-Size Key - Hash Key First".hex(),
     "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"),
    ("aa" * 131,
     b"This is a test using a larger than block-size key and a larger than block-size data."
     b" The key needs to be hashed before being used by the HMAC algorithm.".hex(),
     "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2"),
]


@pytest.mark.parametrize("key, message, tag", RFC4231)
def test_hmac_rfc4231(key: str, message: str, tag: str) -> None:
    key_bytes, message_bytes = bytes.fromhex(key), bytes.fromhex(message)
    expected = bytes.fromhex(tag)
    out = hmac_sha256(key_bytes, message_bytes)
    assert len(out) == 32
    assert out[: len(expected)] == expected
    assert out == std_hmac.new(key_bytes, message_bytes, hashlib.sha256).digest()


def test_hmac_random() -> None:
    # Keys and messages on both sides of the 64-byte block, with a fixed seed.
    rng = random.Random(2104)
    for _ in range(100):
        key, message = rng.randbytes(rng.randrange(150)), rng.randbytes(rng.randrange(300))
        assert hmac_sha256(key, message) == std_hmac.new(key, message, hashlib.sha256).digest()


# RFC 5869 Appendix A.1 to A.3: salt, IKM, info, length, PRK and OKM, in hex.
RFC5869 = [
    ("000102030405060708090a0b0c", "0b" * 22, "f0f1f2f3f4f5f6f7f8f9", 42,
     "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5",
     "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf"
     "34007208d5b887185865"),
    (bytes(range(0x60, 0xB0)).hex(), bytes(range(0x00, 0x50)).hex(),
     bytes(range(0xB0, 0x100)).hex(), 82,
     "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244",
     "b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c"
     "59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71"
     "cc30c58179ec3e87c14c01d5c1f3434f1d87"),
    # A.3: an empty salt and an empty info.
    ("", "0b" * 22, "", 42,
     "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04",
     "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d"
     "9d201395faa4b61a96c8"),
]


@pytest.mark.parametrize("salt, ikm, info, length, prk, okm", RFC5869)
def test_hkdf_rfc5869(salt: str, ikm: str, info: str, length: int, prk: str, okm: str) -> None:
    salt_bytes, ikm_bytes, info_bytes = bytes.fromhex(salt), bytes.fromhex(ikm), bytes.fromhex(info)
    assert hkdf_extract(salt_bytes, ikm_bytes) == bytes.fromhex(prk)
    assert hkdf(salt_bytes, ikm_bytes, info_bytes, length) == bytes.fromhex(okm)


def test_hkdf_lengths() -> None:
    # 255 blocks of 32 bytes is the longest output; one byte more is rejected.
    assert len(hkdf(b"salt", b"ikm", b"info", 255 * 32)) == 255 * 32
    with pytest.raises(ValueError, match="outputTooLong"):
        hkdf(b"salt", b"ikm", b"info", 255 * 32 + 1)
    assert hkdf(b"salt", b"ikm", b"info", 0) == b""


def test_concat_kdf_rfc7518() -> None:
    # RFC 7518 Appendix C: the 128-bit key of an ECDH-ES agreement for A128GCM.
    # The other information is AlgorithmID | PartyUInfo | PartyVInfo | SuppPubInfo.
    z = bytes([
        158, 86, 217, 29, 129, 113, 53, 211, 114, 131, 66, 131, 191, 132, 38, 156,
        251, 49, 110, 163, 218, 128, 106, 72, 246, 218, 167, 121, 140, 254, 144, 196])
    fixed_info = bytes([
        0, 0, 0, 7, 65, 49, 50, 56, 71, 67, 77, 0, 0, 0, 5, 65, 108, 105, 99, 101,
        0, 0, 0, 3, 66, 111, 98, 0, 0, 0, 128])
    key = bytes([86, 170, 141, 234, 248, 35, 109, 32, 92, 34, 40, 205, 113, 167, 16, 26])
    assert concat_kdf(z, fixed_info, 16) == key


def test_concat_kdf_blocks() -> None:
    # Block i is SHA-256(i | Z | FixedInfo), the counter as four big-endian bytes.
    z, fixed_info = b"shared secret", b"fixed info"
    blocks = b"".join(hashlib.sha256(i.to_bytes(4, "big") + z + fixed_info).digest()
                      for i in range(1, 4))
    for length in (1, 31, 32, 33, 64, 65, 96):
        assert concat_kdf(z, fixed_info, length) == blocks[:length]
    with pytest.raises(ValueError, match="emptyOutput"):
        concat_kdf(z, fixed_info, 0)


def test_rejects_non_bytes() -> None:
    with pytest.raises(TypeError):
        hmac_sha256("key", b"message")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        hkdf(b"salt", "ikm", b"info", 32)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        concat_kdf(b"z", "info", 32)  # type: ignore[arg-type]
