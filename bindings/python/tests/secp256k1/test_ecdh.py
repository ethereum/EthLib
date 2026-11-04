"""ECDH against the Wycheproof ECDH set of secp256k1."""

import hashlib
import json
from pathlib import Path

import pytest

from ethlib.cryptography import secp256k1

# `testvectors_v1/ecdh_secp256k1_test.json` of `C2SP/wycheproof` at commit
# d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9, under the Apache License 2.0 in `wycheproof/LICENSE`.
SET = Path(__file__).resolve().parent / "wycheproof" / "ecdh_secp256k1_test.json"

# The SHA-256 of the vendored file, so an edit to it fails the suite.
SET_SHA256 = "049fa2be70e9db836a043aba6132b53cd97de4c0de5277bca6d65a2770075cae"

# SEQUENCE { SEQUENCE { id-ecPublicKey, secp256k1 }, BIT STRING of 66 bytes }, then 0x04.
# Only keys under this header, with an uncompressed point, are kept.
# Most other tests check the ASN.1 parser or the curve parameters, which EthLib does not read.
# Four give a compressed point under another header.
HEADER = bytes.fromhex("3056301006072a8648ce3d020106052b8104000a034200")

N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def _cases():
    """Each kept test, as (tcId, private key, public key, shared secret or None)."""
    data = json.loads(SET.read_bytes())
    for group in data["testGroups"]:
        for test in group["tests"]:
            public = bytes.fromhex(test["public"])
            if not (public.startswith(HEADER) and len(public) == len(HEADER) + 65):
                continue
            # "acceptable" marks behaviour the set allows either way, so it pins nothing.
            if test["result"] == "acceptable":
                continue
            # The private key is a DER integer, which may carry a leading zero byte.
            d = int(test["private"], 16)
            assert 0 < d < N
            shared = bytes.fromhex(test["shared"]) if test["result"] == "valid" else None
            yield test["tcId"], d.to_bytes(32, "big"), public[len(HEADER):], shared


CASES = list(_cases())


def test_set_pinned() -> None:
    assert hashlib.sha256(SET.read_bytes()).hexdigest() == SET_SHA256


def test_case_count() -> None:
    # Most of the set's 752 tests encode the key in the standard way.
    assert len(CASES) > 400


@pytest.mark.parametrize("tc_id, private_key, public_key, shared", CASES,
                         ids=[f"tc{c[0]}" for c in CASES])
def test_ecdh(tc_id: int, private_key: bytes, public_key: bytes, shared: bytes | None) -> None:
    if shared is None:
        with pytest.raises(ValueError):
            secp256k1.ecdh(private_key, public_key)
    else:
        assert secp256k1.ecdh(private_key, public_key) == shared


def test_ecdh_rejects_zero_key() -> None:
    # Test 1 of the set, with the private key 0: d Q is the point at infinity.
    public_key = CASES[0][2]
    with pytest.raises(ValueError):
        secp256k1.ecdh(bytes(32), public_key)
