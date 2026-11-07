"""Verification and recovery against the invalid ECDSA fixtures of `bitcoinjs/tiny-secp256k1`."""

import json
from pathlib import Path

import pytest

from ethlib.cryptography import secp256k1
from ethlib.errors import Secp256k1Error
from raising import raises

# The ECDSA fixtures of tiny-secp256k1, pinned by `test_sign.py`.
#
# File: tests/fixtures/ecdsa.json
# Repository: bitcoinjs/tiny-secp256k1
# Commit: e1fd7a77bb0ca87fb4726fb1fd4f424f30a04db9
# Licence: MIT (tiny_secp256k1/LICENSE)
FIXTURES = Path(__file__).resolve().parent / "tiny_secp256k1" / "ecdsa.json"

INVALID = json.loads(FIXTURES.read_bytes())["invalid"]

# The SEC 1 v2 §2.3.4 decoding error that each malformed public key of the fixtures meets.
# Each value is the message and the code of the Lean error.
# In a message, {prefix} stands for the first byte of the key.
KEY_ERRORS = {
    "Bad sequence prefix": ("bad point encoding prefix: {prefix}", 2),
    "Bad X coordinate (== 0)": ("point is not on the curve", 4),
    "Bad Y coordinate (== 0)": ("point is not on the curve", 4),
    "Bad X/Y coordinate (== 0)": ("point is not on the curve", 4),
    "Bad X coordinate (== P)": ("point coordinate is not below p", 3),
    "Bad Y coordinate (== P)": ("point coordinate is not below p", 3),
    "Bad X coordinate (> P)": ("point coordinate is not below p", 3),
    "Bad Y coordinate (> P)": ("point coordinate is not below p", 3),
}

BAD_KEYS = [c for c in INVALID["verify"] if c.get("exception") == "Expected Point"]
BAD_SIGNATURES = [c for c in INVALID["verify"] if c.get("exception") != "Expected Point"]


def _ids(case: dict) -> str:
    return f"{case['description']} ({len(case.get('Q', '')) // 2})"


@pytest.mark.parametrize("case", BAD_KEYS, ids=_ids)
def test_verify_rejects_key(case: dict) -> None:
    q, m, s = (bytes.fromhex(case[k]) for k in ("Q", "m", "signature"))
    message, code = KEY_ERRORS[case["description"]]
    # A compressed key with x = 0 meets a different error.
    # 0^3 + 7 has no square root mod p, so no point has that x (SEC 1 v2 §2.3.4, step 2.4.1).
    if len(q) == 33 and case["description"] == "Bad X coordinate (== 0)":
        message, code = "no point of the curve has this x", 5
    with raises(Secp256k1Error, message.format(prefix=q[0])) as error:
        secp256k1.verify(q, m, s)
    assert error.value.code == code


@pytest.mark.parametrize("case", BAD_SIGNATURES, ids=_ids)
def test_verify_rejects_signature(case: dict) -> None:
    # r or s is 0 or at least n, which SEC 1 v2 §4.1.4 step 1 rejects.
    # Or s is high, which the strict mode of tiny-secp256k1 rejects.
    # EthLib leaves a high s to the EIP-2 check.
    q, m, s = (bytes.fromhex(case[k]) for k in ("Q", "m", "signature"))
    if case.get("strict"):
        assert secp256k1.verify(q, m, s)
        assert not secp256k1.is_low_s(s)
    else:
        assert not secp256k1.verify(q, m, s)


# The error EthLib names for each invalid recovery of the fixtures, message and code.
RECOVER_ERRORS = {
    "Invalid r, s values (== 0)": ("signature integer is not in [1, n - 1]", 7),
    "Invalid r value (== 0)": ("signature integer is not in [1, n - 1]", 7),
    "Invalid s value (== 0)": ("signature integer is not in [1, n - 1]", 7),
    "Invalid r value (>= n)": ("signature integer is not in [1, n - 1]", 7),
    "Invalid s value (>= n)": ("signature integer is not in [1, n - 1]", 7),
    # Recovery ids 2 and 3 name x = r + n, which Ethereum never uses; EthLib takes 0 or 1.
    "Invalid r value for r (should be less than p - order)": (
        "bad recovery id: 2, expected 0 or 1",
        13,
    ),
    # r is in [1, n - 1], but r^3 + 7 is not a square mod p (SEC 1 v2 §4.1.6, step 1.3).
    "Invalid X coordinate value for r": ("no point of the curve has this x", 5),
    "Invalid hash length": ("bad hash size: 33, expected 32", 11),
}


@pytest.mark.parametrize("case", INVALID["recover"], ids=lambda c: c["description"])
def test_recover_rejects(case: dict) -> None:
    m, s = bytes.fromhex(case["m"]), bytes.fromhex(case["signature"])
    message, code = RECOVER_ERRORS[case["description"]]
    with raises(Secp256k1Error, message) as error:
        secp256k1.recover(m, s, case.get("recoveryId", 0))
    assert error.value.code == code


def test_case_counts() -> None:
    # Every invalid verify and recover case runs above.
    assert len(BAD_KEYS) + len(BAD_SIGNATURES) == len(INVALID["verify"]) == 25
    assert len(INVALID["recover"]) == 8
