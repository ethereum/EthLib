"""BLS verification and the hash to G2 against the Wycheproof sets."""

import json
from pathlib import Path

import pytest
from py_ecc.bls.point_compression import compress_G2
from py_ecc.fields import optimized_bls12_381_FQ2 as FQ2

from ethlib.cryptography import bls

# The BLS vectors of Wycheproof.
#
# Files: testvectors_v1/bls_sig_g2_pop_verify_test.json, testvectors_v1/bls_hash_to_g2_test.json
# Repository: C2SP/wycheproof
# Commit: d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9
# Licence: Apache 2.0 (wycheproof/LICENSE)
DIR = Path(__file__).resolve().parent / "wycheproof"

# Ethereum's ciphersuite, the one that `bls.verify` implements.
POP = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_"


def _load(name: str) -> dict:
    data = json.loads((DIR / name).read_text())
    assert sum(len(g["tests"]) for g in data["testGroups"]) == data["numberOfTests"]
    return data


VERIFY = _load("bls_sig_g2_pop_verify_test.json")
HASH = _load("bls_hash_to_g2_test.json")


def _verify_cases() -> list:
    cases = []
    for group in VERIFY["testGroups"]:
        assert group["ciphersuite"] == POP
        pk = bytes.fromhex(group["publicKey"]["pk"])
        cases += [pytest.param(pk, t, id=str(t["tcId"])) for t in group["tests"]]
    return cases


@pytest.mark.parametrize("pk, test", _verify_cases())
def test_pop_verify(pk: bytes, test: dict) -> None:
    # Every invalid case, whatever its fault, must not verify.
    assert test["result"] in ("valid", "invalid")
    msg, sig = bytes.fromhex(test["msg"]), bytes.fromhex(test["sig"])
    assert bls.verify(pk, msg, sig) == (test["result"] == "valid")


def _compress(affine: bytes) -> bytes:
    """The compressed form of an affine `x.c0 ‖ x.c1 ‖ y.c0 ‖ y.c1`, computed by py_ecc."""
    c = [int.from_bytes(affine[48 * i : 48 * (i + 1)], "big") for i in range(4)]
    z1, z2 = compress_G2((FQ2([c[0], c[1]]), FQ2([c[2], c[3]]), FQ2.one()))
    return z1.to_bytes(48, "big") + z2.to_bytes(48, "big")


def _hash_cases() -> list:
    cases = []
    for group in HASH["testGroups"]:
        dst = group["dst"].encode()
        cases += [pytest.param(dst, t, id=str(t["tcId"])) for t in group["tests"]]
    return cases


@pytest.mark.parametrize("dst, test", _hash_cases())
def test_hash_to_g2(dst: bytes, test: dict) -> None:
    # The set gives the compressed point, and the binding the affine one; py_ecc compresses it.
    assert test["result"] == "valid"
    expected = bytes.fromhex(test["expected"])
    assert _compress(bls.hash_to_g2(bytes.fromhex(test["msg"]), dst)) == expected
    # EthLib decodes the expected point and encodes it back unchanged.
    assert bls.decode_g2(expected) == expected
    # Its negative has the same x coordinate and the other compressed sign bit.
    negative = bytes([expected[0] ^ 0x20]) + expected[1:]
    assert bls.decode_g2(negative) == negative
