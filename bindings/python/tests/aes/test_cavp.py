"""The AES block cipher against the ECB known answers of NIST CAVP (AESAVS)."""

from pathlib import Path

import pytest

from ethlib.cryptography import aes

CAVP = Path(__file__).resolve().parent / "cavp"

# The four known-answer tests of AESAVS §6.2, at the two key sizes EthLib implements.
FILES = [
    f"ECB{test}{bits}.rsp"
    for test in ("GFSbox", "KeySbox", "VarKey", "VarTxt")
    for bits in (128, 256)
]


def _cases(name: str) -> list[tuple[str, bytes, bytes, bytes]]:
    """The (direction, key, plaintext, ciphertext) of each case of one `.rsp` file."""
    cases, direction, case = [], None, {}
    for line in (CAVP / name).read_text().splitlines():
        line = line.strip()
        if line in ("[ENCRYPT]", "[DECRYPT]"):
            direction = line[1:-1]
            continue
        key, sep, value = line.partition(" = ")
        if not sep:
            continue
        case[key] = value
        # The last field of a case is CIPHERTEXT in an encrypt section, PLAINTEXT in a decrypt one.
        if key == ("CIPHERTEXT" if direction == "ENCRYPT" else "PLAINTEXT"):
            cases.append(
                (
                    direction,
                    bytes.fromhex(case["KEY"]),
                    bytes.fromhex(case["PLAINTEXT"]),
                    bytes.fromhex(case["CIPHERTEXT"]),
                )
            )
            case = {}
    return cases


CASES = [(name, *case) for name in FILES for case in _cases(name)]


def test_case_count() -> None:
    # The cases of each file, at 128 and 256 bits:
    # - GFSbox 7 and 5
    # - KeySbox 21 and 16
    # - VarKey 128 and 256
    # - VarTxt 128 and 128
    #
    # Each case appears in an encrypt section and in a decrypt section.
    # A parser that drops cases fails here.
    assert len(CASES) == 2 * (7 + 5 + 21 + 16 + 128 + 256 + 128 + 128)


@pytest.mark.parametrize("name, direction, key, plaintext, ciphertext", CASES)
def test_ecb(name: str, direction: str, key: bytes, plaintext: bytes, ciphertext: bytes) -> None:
    assert len(key) * 8 == int(name[-7:-4])
    if direction == "ENCRYPT":
        assert aes.encrypt_block(key, plaintext) == ciphertext
    else:
        assert aes.decrypt_block(key, ciphertext) == plaintext
