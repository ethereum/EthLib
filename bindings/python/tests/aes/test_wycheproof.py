"""AES-GCM against the Wycheproof set `aes_gcm_test.json`."""

import json
from pathlib import Path

import pytest

from ethlib.cryptography import aes
from ethlib.errors import AesError

# The AES-GCM vectors of Wycheproof.
#
# File: testvectors_v1/aes_gcm_test.json
# Repository: C2SP/wycheproof
# Commit: d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9
# Licence: Apache 2.0 (wycheproof/LICENSE)
SET = Path(__file__).resolve().parent / "wycheproof" / "aes_gcm_test.json"


def _cases() -> list:
    """Each test of the set, with the key size of its group."""
    data = json.loads(SET.read_text())
    cases = [(group["keySize"], test) for group in data["testGroups"] for test in group["tests"]]
    assert len(cases) == data["numberOfTests"]
    return cases


CASES = _cases()
# EthLib implements AES-128 and AES-256 only, the two that Ethereum's protocols use.
SUPPORTED = [(size, test) for size, test in CASES if size in (128, 256)]
AES192 = [test for size, test in CASES if size == 192]


def _fields(test: dict) -> tuple[bytes, ...]:
    return tuple(bytes.fromhex(test[f]) for f in ("key", "iv", "aad", "msg", "ct", "tag"))


@pytest.mark.parametrize(
    "test", [t for _, t in SUPPORTED if t["result"] == "valid"], ids=lambda t: t["tcId"])
def test_valid(test: dict) -> None:
    key, iv, aad, msg, ct, tag = _fields(test)
    assert aes.gcm_encrypt(key, iv, msg, aad, len(tag)) == ct + tag
    assert aes.gcm_decrypt(key, iv, ct, aad, tag, len(tag)) == msg


@pytest.mark.parametrize(
    "test", [t for _, t in SUPPORTED if t["flags"] == ["ModifiedTag"]], ids=lambda t: t["tcId"])
def test_modified_tag(test: dict) -> None:
    key, iv, aad, _, ct, tag = _fields(test)
    assert test["result"] == "invalid"
    with pytest.raises(AesError, match="authentication") as info:
        aes.gcm_decrypt(key, iv, ct, aad, tag, len(tag))
    assert info.value.code == 6


@pytest.mark.parametrize(
    "test", [t for _, t in SUPPORTED if t["flags"] == ["ZeroLengthIv"]], ids=lambda t: t["tcId"])
def test_zero_length_iv(test: dict) -> None:
    # SP 800-38D §5.2.1.1 requires an IV of at least one bit, for encryption and decryption.
    key, iv, aad, msg, ct, tag = _fields(test)
    assert test["result"] == "invalid" and iv == b""
    with pytest.raises(AesError, match="ivLength") as info:
        aes.gcm_encrypt(key, iv, msg, aad, len(tag))
    assert info.value.code == 3
    with pytest.raises(AesError, match="ivLength") as info:
        aes.gcm_decrypt(key, iv, ct, aad, tag, len(tag))
    assert info.value.code == 3


def test_every_invalid_case_has_a_test() -> None:
    # A new kind of invalid case in a later pin must get its own test, not pass unread.
    flags = {tuple(t["flags"]) for _, t in SUPPORTED if t["result"] == "invalid"}
    assert flags == {("ModifiedTag",), ("ZeroLengthIv",)}
    assert {t["result"] for _, t in CASES} == {"valid", "invalid"}


def test_aes192_keys_are_rejected() -> None:
    # A 24-byte key selects no cipher of EthLib, so the export rejects it before GCM.
    assert len(AES192) == 103
    for test in AES192:
        key, iv, aad, msg, ct, tag = _fields(test)
        assert len(key) == 24
        with pytest.raises(AesError, match="key size: 24") as info:
            aes.gcm_encrypt(key, iv, msg, aad, len(tag))
        assert info.value.code == 0
        with pytest.raises(AesError, match="key size: 24") as info:
            aes.gcm_decrypt(key, iv, ct, aad, tag, len(tag))
        assert info.value.code == 0
