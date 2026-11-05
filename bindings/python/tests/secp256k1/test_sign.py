"""Signing against the ECDSA fixtures of `bitcoinjs/tiny-secp256k1`."""

import hashlib
import json
from pathlib import Path

import pytest

from ethlib.cryptography import secp256k1
from raising import raises

# The ECDSA fixtures of tiny-secp256k1.
#
# File: tests/fixtures/ecdsa.json
# Repository: bitcoinjs/tiny-secp256k1
# Commit: e1fd7a77bb0ca87fb4726fb1fd4f424f30a04db9
# Licence: MIT (tiny_secp256k1/LICENSE)
FIXTURES = Path(__file__).resolve().parent / "tiny_secp256k1" / "ecdsa.json"

# The SHA-256 of the vendored file, so an edit to it fails the suite.
FIXTURES_SHA256 = "b830aa30d0ab3b6c51440caffac9206b24ae5450a387a2db73789f5ce795595d"

DATA = json.loads(FIXTURES.read_bytes())


def test_fixtures_pinned() -> None:
    assert hashlib.sha256(FIXTURES.read_bytes()).hexdigest() == FIXTURES_SHA256


@pytest.mark.parametrize("i", range(len(DATA["valid"])))
def test_sign_valid(i: int) -> None:
    case = DATA["valid"][i]
    private_key, msg_hash = bytes.fromhex(case["d"]), bytes.fromhex(case["m"])
    signature = bytes.fromhex(case["signature"])
    # The signature, then its recovery id, byte for byte.
    assert secp256k1.sign(private_key, msg_hash) == signature + bytes([case["recoveryId"]])


def test_sign_verifies() -> None:
    # The first valid case: its recovery id recovers the key that signed, which verifies it.
    case = DATA["valid"][0]
    msg_hash = bytes.fromhex(case["m"])
    out = secp256k1.sign(bytes.fromhex(case["d"]), msg_hash)
    public_key = secp256k1.recover(msg_hash, out[:64], out[64])
    assert secp256k1.verify(public_key, msg_hash, out[:64])
    assert secp256k1.is_low_s(out[:64])


# The error of each invalid private key of the fixtures: a zero key, and every key not below n.
SIGN_ERRORS = {
    "Private key == 0": "private key is zero",
    "Private key >= G": "bad private key: not below the group order n",
}


@pytest.mark.parametrize("case", DATA["invalid"]["sign"], ids=lambda c: c["description"])
def test_sign_rejects_key(case: dict) -> None:
    with raises(ValueError, SIGN_ERRORS[case["description"]]):
        secp256k1.sign(bytes.fromhex(case["d"]), bytes.fromhex(case["m"]))


def test_sign_rejects_sizes() -> None:
    with raises(ValueError, "bad private key size: 31, expected 32"):
        secp256k1.sign(bytes(31), bytes(32))
    with raises(ValueError, "bad hash size: 31, expected 32"):
        secp256k1.sign(bytes(31) + b"\x01", bytes(31))
