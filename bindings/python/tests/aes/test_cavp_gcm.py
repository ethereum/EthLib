"""AES-GCM against the test vectors of NIST CAVP, `gcmtestvectors.zip`."""

from pathlib import Path

import pytest

from ethlib.cryptography import aes
from ethlib.errors import AesError

CAVP = Path(__file__).resolve().parent / "cavp"

# The encryption and decryption files for the two key sizes that EthLib implements.
ENCRYPT = ["gcmEncryptExtIV128.rsp", "gcmEncryptExtIV256.rsp"]
DECRYPT = ["gcmDecrypt128.rsp", "gcmDecrypt256.rsp"]

# EthLib accepts tags of 96 to 128 bits, the lengths of SP 800-38D §5.2.1.2 without Appendix C.
# The files also hold 32-bit and 64-bit tags, which EthLib rejects with its `shortTag` error.
SHORT_TAGS = (32, 64)


def _cases(name: str) -> list[dict]:
    """Each case of one file, with the parameters of its section in bits."""
    cases, section, case = [], {}, None
    for line in (CAVP / name).read_text().splitlines():
        line = line.strip()
        if line.startswith("[") and " = " in line:
            key, value = line[1:-1].split(" = ")
            section[key] = int(value)
        elif line.startswith("Count = "):
            case = dict(section, Count=int(line.split(" = ")[1]))
            cases.append(case)
        elif line == "FAIL":
            case["FAIL"] = True
        elif " = " in line and case is not None:
            key, value = line.split(" = ")
            case[key] = bytes.fromhex(value)
        elif line.endswith(" =") and case is not None:
            case[line[:-2]] = b""
    return cases


SECTION = ("Keylen", "IVlen", "PTlen", "AADlen", "Taglen")


def _sections(names: list[str]) -> list:
    """The cases of each file, one test per section of 15 cases, to keep the run short."""
    params = []
    for name in names:
        groups: dict[tuple, list] = {}
        for case in _cases(name):
            groups.setdefault(tuple(case.get(k) for k in SECTION), []).append(case)
        params += [pytest.param(group, id=f"{name[:-4]}-" + "-".join(map(str, key)))
                   for key, group in groups.items()]
    return params


ENCRYPT_SECTIONS = _sections(ENCRYPT)
DECRYPT_SECTIONS = _sections(DECRYPT)


def test_case_count() -> None:
    # Each file has 7875 cases: 525 sections of 15, every pairing of the IV, text, data and tag
    # lengths of the file.
    for sections in (ENCRYPT_SECTIONS, DECRYPT_SECTIONS):
        assert len(sections) == 2 * 525
        assert all(len(p.values[0]) == 15 for p in sections)
        for case in (c for p in sections for c in p.values[0]):
            assert len(case["Key"]) * 8 == case["Keylen"]
            assert len(case["IV"]) * 8 == case["IVlen"]
            assert len(case["Tag"]) * 8 == case["Taglen"]
            assert len(case["AAD"]) * 8 == case["AADlen"]


@pytest.mark.parametrize("section", ENCRYPT_SECTIONS)
def test_encrypt(section: list) -> None:
    for case in section:
        _encrypt(case)


@pytest.mark.parametrize("section", DECRYPT_SECTIONS)
def test_decrypt(section: list) -> None:
    for case in section:
        _decrypt(case)


def _encrypt(case: dict) -> None:
    tag_length = case["Taglen"] // 8
    if case["Taglen"] in SHORT_TAGS:
        with pytest.raises(AesError, match="shortTag") as error:
            aes.gcm_encrypt(case["Key"], case["IV"], case["PT"], case["AAD"], tag_length)
        assert error.value.code == 2
        return
    out = aes.gcm_encrypt(case["Key"], case["IV"], case["PT"], case["AAD"], tag_length)
    assert out == case["CT"] + case["Tag"], case["Count"]


def _decrypt(case: dict) -> None:
    tag_length = case["Taglen"] // 8
    args = (case["Key"], case["IV"], case["CT"], case["AAD"], case["Tag"], tag_length)
    if case["Taglen"] in SHORT_TAGS:
        with pytest.raises(AesError, match="shortTag") as error:
            aes.gcm_decrypt(*args)
        assert error.value.code == 2
    elif case.get("FAIL"):
        # The file marks a case FAIL when the tag does not authenticate the input.
        assert "PT" not in case
        with pytest.raises(AesError, match="authentication") as error:
            aes.gcm_decrypt(*args)
        assert error.value.code == 6
    else:
        assert aes.gcm_decrypt(*args) == case["PT"], case["Count"]
