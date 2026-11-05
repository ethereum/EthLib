"""AES-GCM against the test vectors of NIST CAVP, `gcmtestvectors.zip`."""

from pathlib import Path
from typing import cast

import pytest

from ethlib.cryptography import aes
from ethlib.errors import AesError

CAVP = Path(__file__).resolve().parent / "cavp"

# The archive that holds the whole files; the weekly job reads it.
ARCHIVE = "nist-cavp/gcmtestvectors"

# The encryption and decryption files for the two key sizes that EthLib implements.
ENCRYPT = ["gcmEncryptExtIV128.rsp", "gcmEncryptExtIV256.rsp"]
DECRYPT = ["gcmDecrypt128.rsp", "gcmDecrypt256.rsp"]

# EthLib accepts tags of 96 to 128 bits, the lengths of SP 800-38D §5.2.1.2 without Appendix C.
# The files also hold 32-bit and 64-bit tags, which EthLib rejects with its `shortTag` error.
SHORT_TAGS = (32, 64)
TAGS = {32, 64, 96, 104, 112, 120, 128}

SECTION = ("Keylen", "IVlen", "PTlen", "AADlen", "Taglen")

# The sections that the vendored excerpt of each file keeps, with every tag length.
# Each IV length of the files is there, with a text and data that end in a partial block.
EXCERPT = {"IVlen": {8, 96, 1024}, "PTlen": {104}, "AADlen": {160}}


def _sections(text: str) -> tuple[str, list[tuple[dict, str]]]:
    """The header of a file, and each section with its parameters and its text."""
    lines = text.splitlines(keepends=True)
    starts = [i for i, line in enumerate(lines) if line.startswith("[Keylen")]
    header = "".join(lines[: starts[0]])
    sections = []
    for start, end in zip(starts, starts[1:] + [len(lines)], strict=True):
        body = "".join(lines[start:end])
        params = {}
        for line in lines[start:end]:
            line = line.strip()
            if line.startswith("[") and " = " in line:
                key, value = line[1:-1].split(" = ")
                params[key] = int(value)
        sections.append((params, body))
    return header, sections


def excerpt(text: str) -> str:
    """The header of a file, and its sections that `EXCERPT` selects, unchanged."""
    header, sections = _sections(text)
    kept = [
        body
        for params, body in sections
        if all(params[key] in values for key, values in EXCERPT.items())
    ]
    return header + "".join(kept)


def _cases(params: dict, body: str) -> list[dict]:
    """Each case of a section, with the parameters of the section in bits."""
    cases, case = [], None
    for line in body.splitlines():
        line = line.strip()
        if line.startswith("Count = "):
            case = dict(params, Count=int(line.split(" = ")[1]))
            cases.append(case)
        elif line == "FAIL":
            # A FAIL line follows the Count line of its case.
            cast(dict, case)["FAIL"] = True
        elif " = " in line and case is not None:
            key, value = line.split(" = ")
            case[key] = bytes.fromhex(value)
        elif line.endswith(" =") and case is not None:
            case[line[:-2]] = b""
    return cases


def _excerpt_name(name: str) -> str:
    return name.replace(".rsp", ".excerpt.rsp")


def _params(names: list[str]) -> list:
    """One test per section of each vendored excerpt."""
    params = []
    for name in names:
        _, sections = _sections((CAVP / _excerpt_name(name)).read_text())
        for section in sections:
            label = "-".join(str(section[0][key]) for key in SECTION)
            params.append(pytest.param(name, section, id=f"{name[:-4]}-{label}"))
    return params


ENCRYPT_SECTIONS = _params(ENCRYPT)
DECRYPT_SECTIONS = _params(DECRYPT)


def test_excerpt_covers_every_tag_length() -> None:
    for sections in (ENCRYPT_SECTIONS, DECRYPT_SECTIONS):
        # 3 IV lengths and 7 tag lengths for each of the 2 files, 15 cases a section.
        assert len(sections) == 2 * 3 * 7
        assert {p.values[1][0]["Taglen"] for p in sections} == TAGS
        for p in sections:
            cases = _cases(*p.values[1])
            assert len(cases) == 15
            for case in cases:
                assert len(case["Key"]) * 8 == case["Keylen"]
                assert len(case["IV"]) * 8 == case["IVlen"]
                assert len(case["Tag"]) * 8 == case["Taglen"]
                assert len(case["AAD"]) * 8 == case["AADlen"]
    # The decryption excerpts hold tags that do not authenticate their input.
    assert any(c.get("FAIL") for p in DECRYPT_SECTIONS for c in _cases(*p.values[1]))


@pytest.mark.parametrize("name, section", ENCRYPT_SECTIONS)
def test_encrypt(name: str, section: tuple) -> None:
    for case in _cases(*section):
        _encrypt(case)


@pytest.mark.parametrize("name, section", DECRYPT_SECTIONS)
def test_decrypt(name: str, section: tuple) -> None:
    for case in _cases(*section):
        _decrypt(case)


@pytest.mark.archive(ARCHIVE, *ENCRYPT, *DECRYPT)
@pytest.mark.parametrize("name", ENCRYPT + DECRYPT)
def test_excerpt_of_the_archive(archive: Path, name: str) -> None:
    # Each vendored excerpt is the selected sections of the NIST file, byte for byte.
    text = (archive / name).read_bytes().decode()
    assert excerpt(text).encode() == (CAVP / _excerpt_name(name)).read_bytes()


@pytest.mark.archive(ARCHIVE, *ENCRYPT, *DECRYPT)
@pytest.mark.parametrize("name", ENCRYPT + DECRYPT)
def test_whole_file(archive: Path, name: str) -> None:
    # Each file has 7875 cases: 525 sections of 15, every pairing of the IV, text, data and tag
    # lengths of the file.
    _, sections = _sections((archive / name).read_text())
    assert len(sections) == 525
    check = _encrypt if name in ENCRYPT else _decrypt
    for params, body in sections:
        cases = _cases(params, body)
        assert len(cases) == 15
        for case in cases:
            check(case)


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
