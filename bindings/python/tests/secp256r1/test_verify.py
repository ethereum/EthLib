"""Test-vector generator: `verify`.

Every case is a test of the Wycheproof IEEE P1363 set for secp256r1 with SHA-256.

File: testvectors_v1/ecdsa_secp256r1_sha256_p1363_test.json
Repository: C2SP/wycheproof
Commit: d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9
Licence: Apache 2.0 (wycheproof/LICENSE)

The expected result of each case is Wycheproof's.
The hash is EthLib's own SHA-256, which its NIST vectors pin.
"""

import json
from pathlib import Path

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import secp256r1
from ethlib.cryptography.sha256 import sha256
from raising import raises

SET = Path(__file__).resolve().parent / "wycheproof" / "ecdsa_secp256r1_sha256_p1363_test.json"

N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551


def _cases():
    """Each test of the set, as (tcId, public key, hash, signature, valid)."""
    data = json.loads(SET.read_text())
    for group in data["testGroups"]:
        # The uncompressed SEC 1 key is 0x04, then x and y: the export takes x and y.
        uncompressed = bytes.fromhex(group["publicKey"]["uncompressed"])
        assert uncompressed[0] == 4 and len(uncompressed) == 65
        public_key = uncompressed[1:]
        for test in group["tests"]:
            # The set has no "acceptable" result, only valid and invalid.
            assert test["result"] in ("valid", "invalid")
            msg_hash = sha256(bytes.fromhex(test["msg"]))
            yield (
                test["tcId"],
                public_key,
                msg_hash,
                bytes.fromhex(test["sig"]),
                test["result"] == "valid",
            )


CASES = list(_cases())


def _verify(public_key: bytes, msg_hash: bytes, signature: bytes) -> bool | None:
    # A signature of the wrong length is rejected, written as a null output.
    try:
        return secp256r1.verify(public_key, msg_hash, signature)
    except ValueError:
        return None


@pytest.mark.parametrize(
    "tc_id, public_key, msg_hash, signature, valid", CASES, ids=[f"tc{c[0]}" for c in CASES]
)
def test_p1363(tc_id, public_key, msg_hash, signature, valid) -> None:
    result = _verify(public_key, msg_hash, signature)
    # A rejection, whether by length or by ECDSA, matches an invalid test.
    assert bool(result) == valid
    write_case(
        "secp256r1",
        "verify",
        f"verify_wycheproof_p1363_{tc_id}",
        {
            "input": {
                "public_key": hex_str(public_key),
                "msg_hash": hex_str(msg_hash),
                "signature": hex_str(signature),
            },
            "output": result,
        },
    )


def test_high_s_verifies() -> None:
    # ECDSA accepts `(r, n - s)` with `(r, s)`.
    _, public_key, msg_hash, signature, _ = next(c for c in CASES if c[4] and len(c[3]) == 64)
    s = int.from_bytes(signature[32:], "big")
    flipped = signature[:32] + (N - s).to_bytes(32, "big")
    assert secp256r1.verify(public_key, msg_hash, flipped)


def test_sizes() -> None:
    assert (secp256r1.PUBLIC_KEY_LEN, secp256r1.HASH_LEN, secp256r1.SIGNATURE_LEN) == (64, 32, 64)


@pytest.mark.parametrize(
    "public_key, message",
    [
        (bytes(63), "bad public key size: 63, expected 64"),
        (bytes(65), "bad public key size: 65, expected 64"),
        (b"\xff" * 64, "bad public key: a coordinate is not below p"),
    ],
)
def test_bad_public_key_raises(public_key: bytes, message: str) -> None:
    # A wrong length, or a coordinate not below p, is malformed input.
    _, _, msg_hash, signature, _ = CASES[0]
    with raises(ValueError, message):
        secp256r1.verify(public_key, msg_hash, signature)
