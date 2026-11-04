"""AES, CTR and GCM against the examples of FIPS 197, SP 800-38A and the NIST CAVP files."""

import pytest

from ethlib.cryptography import aes
from ethlib.errors import AesError

# FIPS 197-upd1 Appendix B, then FIPS 197 (2001) Appendix C.1 and C.3: key, input, output.
# https://doi.org/10.6028/NIST.FIPS.197-upd1
# https://csrc.nist.gov/files/pubs/fips/197/final/docs/fips-197.pdf
BLOCKS = [
    ("2b7e151628aed2a6abf7158809cf4f3c", "3243f6a8885a308d313198a2e0370734",
     "3925841d02dc09fbdc118597196a0b32"),
    ("000102030405060708090a0b0c0d0e0f", "00112233445566778899aabbccddeeff",
     "69c4e0d86a7b0430d8cdb78070b4c55a"),
    ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
     "00112233445566778899aabbccddeeff", "8ea2b7ca516745bfeafc49904b496089"),
]


@pytest.mark.parametrize("key, plaintext, ciphertext", BLOCKS)
def test_block(key: str, plaintext: str, ciphertext: str) -> None:
    k, p, c = bytes.fromhex(key), bytes.fromhex(plaintext), bytes.fromhex(ciphertext)
    assert aes.encrypt_block(k, p) == c
    assert aes.decrypt_block(k, c) == p


# SP 800-38A Appendix F.5: the initial counter and the plaintext that every CTR example shares.
# https://doi.org/10.6028/NIST.SP.800-38A
F5_COUNTER = "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff"
F5_PLAINTEXT = (
    "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e51"
    "30c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710"
)

# F.5.1 (CTR-AES128) and F.5.5 (CTR-AES256): key and ciphertext.
# F.5.2 and F.5.6 decrypt them back, with the same function.
CTR = [
    ("2b7e151628aed2a6abf7158809cf4f3c",
     "874d6191b620e3261bef6864990db6ce9806f66b7970fdff8617187bb9fffdff"
     "5ae4df3edbd5d35e5b4f09020db03eab1e031dda2fbe03d1792170a0f3009cee"),
    ("603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4",
     "601ec313775789a5b7a7f504bbf3d228f443e3ca4d62b59aca84e990cacaf5c5"
     "2b0930daa23de94ce87017ba2d84988ddfc9c58db67aada613c2dd08457941a6"),
]


@pytest.mark.parametrize("key, ciphertext", CTR)
def test_ctr(key: str, ciphertext: str) -> None:
    k, counter = bytes.fromhex(key), bytes.fromhex(F5_COUNTER)
    p, c = bytes.fromhex(F5_PLAINTEXT), bytes.fromhex(ciphertext)
    assert aes.ctr(k, counter, p) == c
    assert aes.ctr(k, counter, c) == p
    # A partial last block uses only the first bytes of its keystream block.
    assert aes.ctr(k, counter, p[:37]) == c[:37]


# Test cases of the NIST CAVP file gcmtestvectors.zip:
# https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/gcmtestvectors.zip
GCM = [
    # gcmEncryptExtIV128.rsp, Count = 0, in the section
    # `Keylen = 128, IVlen = 96, PTlen = 0, AADlen = 0, Taglen = 128`.
    dict(
        key="11754cd72aec309bf52f7687212e8957",
        iv="3c819d9a9bed087615030b65",
        pt="",
        aad="",
        ct="",
        tag="250327c674aaf477aef2675748cf6971",
    ),
    # gcmEncryptExtIV128.rsp, Count = 0, in the section
    # `Keylen = 128, IVlen = 96, PTlen = 128, AADlen = 128, Taglen = 128`.
    dict(
        key="c939cc13397c1d37de6ae0e1cb7c423c",
        iv="b3d8cc017cbb89b39e0f67e2",
        pt="c3b3c41f113a31b73d9a5cd432103069",
        aad="24825602bd12a984e0092d3e448eda5f",
        ct="93fe7d9e9bfd10348a5606e5cafa7354",
        tag="0032a1dc85f1c9786925a2e71d8272dd",
    ),
    # gcmEncryptExtIV128.rsp, Count = 0, in the section
    # `Keylen = 128, IVlen = 96, PTlen = 128, AADlen = 128, Taglen = 96`.
    dict(
        key="562ae8aadb8d23e0f271a99a7d1bd4d1",
        iv="f7a5e2399413b89b6ad31aff",
        pt="bbdc3504d803682aa08a773cde5f231a",
        aad="2b9680b886b3efb7c6354b38c63b5373",
        ct="e2b7e5ed5ff27fc8664148f5a628a46d",
        tag="cbf2015184fffb82f2651c36",
    ),
    # gcmEncryptExtIV128.rsp, Count = 0, in the section
    # `Keylen = 128, IVlen = 96, PTlen = 104, AADlen = 160, Taglen = 128`.
    dict(
        key="fe0121f42e599f88ff02a985403e19bb",
        iv="3bb9eb7724cbe1943d43de21",
        pt="fd331ca8646091c29f21e5f0a1",
        aad="2662d895035b6519f3510eae0faa3900ad23cfdf",
        ct="59fe29b07b0de8d869efbbd9b4",
        tag="d24c3e9c1c73c0af1097e26061c857de",
    ),
    # gcmEncryptExtIV128.rsp, Count = 0, in the section
    # `Keylen = 128, IVlen = 1024, PTlen = 128, AADlen = 128, Taglen = 128`.
    dict(
        key="ca91e2414409a439b06573d772f90afb",
        iv=(
            "177008f920a06169ccdf753a338553fefd46845869c9244da44997f83d4ce805"
            "a18707c84d114f9c68427b22841591e6caecf5c3e72a25167aa860c51bdc1aa5"
            "6dcd69f29a2f35e70a322b9eba092a98d66a956b4d294383a0ebab26f7c4df1a"
            "5d4060dfc45a14155100ea7d9e32debb6537406b757291710505142e7659fc77"
        ),
        pt="28003e30c4a4ca9e41aafefac1e1c3de",
        aad="bfeb15fcf7b15f0e14c04439b67950bd",
        ct="00e472971f3a7770aa7158fd92f17bb7",
        tag="16661b85eb51646c94cf2be4e42d7a8e",
    ),
    # gcmEncryptExtIV256.rsp, Count = 0, in the section
    # `Keylen = 256, IVlen = 96, PTlen = 128, AADlen = 128, Taglen = 128`.
    dict(
        key=(
            "92e11dcdaa866f5ce790fd24501f92509aacf4cb8b1339d50c9c1240935dd08b"
        ),
        iv="ac93a1a6145299bde902f21a",
        pt="2d71bcfa914e4ac045b2aa60955fad24",
        aad="1e0889016f67601c8ebea4943bc23ad6",
        ct="8995ae2e6df3dbf96fac7b7137bae67f",
        tag="eca5aa77d51d4a0a14d9c51e1da474ab",
    ),]


@pytest.mark.parametrize("case", GCM, ids=range(len(GCM)))
def test_gcm(case: dict) -> None:
    k, iv, p, aad = (bytes.fromhex(case[f]) for f in ("key", "iv", "pt", "aad"))
    c, tag = bytes.fromhex(case["ct"]), bytes.fromhex(case["tag"])
    assert aes.gcm_encrypt(k, iv, p, aad, len(tag)) == c + tag
    assert aes.gcm_decrypt(k, iv, c, aad, tag, len(tag)) == p


def test_gcm_forged_tag() -> None:
    # gcmDecrypt128.rsp, Count = 1, in the section
    # `Keylen = 128, IVlen = 96, PTlen = 128, AADlen = 128, Taglen = 128`: the file marks it FAIL.
    with pytest.raises(AesError, match="authentication") as info:
        aes.gcm_decrypt(
            bytes.fromhex("867fc5d5476d5008f0703d81e3622255"),
            bytes.fromhex("22945529dff947c3c9264df7"),
            bytes.fromhex("1c785025e5a2678e4b29b29276e395bb"),
            bytes.fromhex("261a9efd4f32bc3d07c115b4edcf8adf"),
            bytes.fromhex("87fdf1261846164a950c37a3f2eea17d"),
        )
    assert info.value.code == 6


def test_gcm_rejects_truncated_tag() -> None:
    # The tag length belongs to the key: a 12-byte prefix of a 16-byte tag fails (SP 800-38D §7.2).
    k, iv, p, aad = bytes(16), bytes(12), b"message", b"aad"
    out = aes.gcm_encrypt(k, iv, p, aad, 16)
    c, tag = out[:-16], out[-16:]
    assert aes.gcm_decrypt(k, iv, c, aad, tag, 16) == p
    with pytest.raises(AesError, match="tagLength") as info:
        aes.gcm_decrypt(k, iv, c, aad, tag[:12], 16)
    assert info.value.code == 1


@pytest.mark.parametrize("tag_length", [-1, 2**64 + 16])
def test_gcm_rejects_tag_length_out_of_range(tag_length: int) -> None:
    # A length outside [0, 2^64) is an error, not a value modulo 2^64.
    with pytest.raises(ValueError, match="tag_length"):
        aes.gcm_encrypt(bytes(16), bytes(12), b"", b"", tag_length)
    with pytest.raises(ValueError, match="tag_length"):
        aes.gcm_decrypt(bytes(16), bytes(12), b"", b"", bytes(16), tag_length)


@pytest.mark.parametrize("tag_length", [4, 8])
def test_gcm_rejects_short_tags(tag_length: int) -> None:
    with pytest.raises(AesError, match="shortTag") as info:
        aes.gcm_encrypt(bytes(16), bytes(12), b"", b"", tag_length)
    assert info.value.code == 2


@pytest.mark.parametrize("call, error", [
    (lambda: aes.encrypt_block(bytes(24), bytes(16)), "key size"),
    (lambda: aes.encrypt_block(bytes(16), bytes(15)), "block size"),
    (lambda: aes.ctr(bytes(16), bytes(15), b""), "counter size"),
])
def test_rejects_bad_sizes(call, error: str) -> None:
    # The export reads these sizes itself, so the error has code 0.
    with pytest.raises(AesError, match=error) as info:
        call()
    assert info.value.code == 0
