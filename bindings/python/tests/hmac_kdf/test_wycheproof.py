"""HMAC-SHA-256 and HKDF-SHA-256 against the Wycheproof sets."""

import json
from pathlib import Path

import pytest

from ethlib.cryptography.hmac import hmac_sha256
from ethlib.cryptography.kdf import HkdfError, hkdf

# The HMAC-SHA-256 and HKDF-SHA-256 vectors of Wycheproof.
#
# Files: testvectors_v1/hmac_sha256_test.json, testvectors_v1/hkdf_sha256_test.json
# Repository: C2SP/wycheproof
# Commit: d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9
# Licence: Apache 2.0 (wycheproof/LICENSE)
DIR = Path(__file__).resolve().parent / "wycheproof"


def _tests(name: str) -> list[dict]:
    """Each test of a set, with the tag size of its group when it has one."""
    data = json.loads((DIR / name).read_text())
    tests = [
        dict(test, tagSize=group.get("tagSize"))
        for group in data["testGroups"]
        for test in group["tests"]
    ]
    assert len(tests) == data["numberOfTests"]
    return tests


HMAC = _tests("hmac_sha256_test.json")
HKDF = _tests("hkdf_sha256_test.json")


@pytest.mark.parametrize("test", HMAC, ids=lambda t: t["tcId"])
def test_hmac(test: dict) -> None:
    # The binding returns the full 32-byte tag; a set with 128-bit tags keeps its first 16 bytes,
    # as RFC 2104 §5 truncates. A modified tag must differ from the tag EthLib computes.
    tag = hmac_sha256(bytes.fromhex(test["key"]), bytes.fromhex(test["msg"]))
    assert len(tag) == 32
    truncated = tag[: test["tagSize"] // 8]
    expected = bytes.fromhex(test["tag"])
    assert test["result"] in ("valid", "invalid")
    assert (truncated == expected) == (test["result"] == "valid")


def test_hmac_invalid_cases_are_modified_tags() -> None:
    # The only invalid kind in the pinned set; a new kind in a later pin needs its own test.
    assert {tuple(t["flags"]) for t in HMAC if t["result"] == "invalid"} == {("ModifiedTag",)}


@pytest.mark.parametrize("test", HKDF, ids=lambda t: t["tcId"])
def test_hkdf(test: dict) -> None:
    salt, ikm, info = (bytes.fromhex(test[f]) for f in ("salt", "ikm", "info"))
    if test["result"] == "valid":
        assert hkdf(salt, ikm, info, test["size"]) == bytes.fromhex(test["okm"])
    else:
        # RFC 5869 §2.3 caps the output at 255 hash lengths, 8160 bytes for SHA-256.
        assert test["flags"] == ["SizeTooLarge"] and test["size"] == 255 * 32 + 1
        with pytest.raises(HkdfError, match="outputTooLong") as error:
            hkdf(salt, ikm, info, test["size"])
        assert error.value.code == 2
