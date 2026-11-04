"""Key generation against EIP-2333 and `py_ecc.bls.G2ProofOfPossession`.

The `master_SK` cases of EIP-2333 run key generation with no key information.
These tests write no vectors.

File: ERCS/erc-2333.md
Repository: ethereum/ERCs
Commit: be307c948f28897adb8f25afcc253c2c909de35d
"""

import pytest
from py_ecc.bls import G2ProofOfPossession as ref_bls

from ethlib.cryptography import bls

EIP_2333 = [
    ("c55257c360c07c72029aebc1b53c05ed0362ada38ead3e3e9efa3708e53495531f09a6987599d18264"
     "c1e1c92f2cf141630c7a3c4ab7c81b2f001698e7463b04",
     6083874454709270928345386274498605044986640685124978867557563392430687146096),
    ("3141592653589793238462643383279502884197169399375105820974944592",
     29757020647961307431480504535336562678282505419141012933316116377660817309383),
    ("0099FF991111002299DD7744EE3355BBDD8844115566CC55663355668888CC00",
     27580842291869792442942448775674722299803720648445448686099262467207037398656),
    ("d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3",
     19022158461524446591288038168518313374041767046816487870552872741050760015818),
]


@pytest.mark.parametrize("seed, master_sk", EIP_2333)
def test_eip_2333_master_key(seed: str, master_sk: int) -> None:
    assert bls.key_gen(bytes.fromhex(seed)) == master_sk.to_bytes(32, "big")


@pytest.mark.parametrize("ikm", [b"\x00" * 32, bytes(range(32)), b"\xff" * 64])
@pytest.mark.parametrize("key_info", [b"", b"key info"])
def test_matches_reference(ikm: bytes, key_info: bytes) -> None:
    expected = ref_bls.KeyGen(ikm, key_info)
    assert bls.key_gen(ikm, key_info) == expected.to_bytes(32, "big")


def test_rejects_short_input() -> None:
    with pytest.raises(ValueError, match="too short: 31 bytes"):
        bls.key_gen(b"\x01" * 31)
