"""The trie root against the trie tests of ethereum/tests."""

# Each case sets its keys one after another, starting from an empty trie, and gives the root.
# `trietests/README.md` gives the origin of the files and their licence.

import json
from pathlib import Path

import pytest

from ethlib.cryptography import keccak
from ethlib.execution import trie
from raising import raises

_DIR = Path(__file__).resolve().parent / "trietests"

# The five files, with whether the trie of each hashes its keys.
_FILES = {
    "trietest.json": False,
    "trieanyorder.json": False,
    "trietest_secureTrie.json": True,
    "trieanyorder_secureTrie.json": True,
    "hex_encoded_securetrie_test.json": True,
}


def _bytes(text: str | None) -> bytes:
    # A null value removes its key, as the empty byte string does.
    if text is None:
        return b""
    # Hex after `0x`, and ASCII text otherwise.
    return bytes.fromhex(text[2:]) if text.startswith("0x") else text.encode()


def _cases() -> list[tuple[str, bool, list[tuple[bytes, bytes]], bytes]]:
    """Each case as its name, whether its trie is secured, its pairs in order, and its root."""
    cases = []
    for file, secured in _FILES.items():
        for name, case in json.loads((_DIR / file).read_text()).items():
            # The ordered files list pairs; the other files map keys to values, in file order.
            pairs = case["in"] if isinstance(case["in"], list) else list(case["in"].items())
            cases.append(
                (
                    f"{file}:{name}",
                    secured,
                    [(_bytes(key), _bytes(value)) for key, value in pairs],
                    bytes.fromhex(case["root"][2:]),
                )
            )
    return cases


_CASES = _cases()

# Invariant: the 25 cases of the five files.
assert len(_CASES) == 25, "unexpected cases"


@pytest.mark.parametrize("name, secured, pairs, expected", _CASES, ids=[c[0] for c in _CASES])
def test_root(name: str, secured: bool, pairs: list[tuple[bytes, bytes]], expected: bytes) -> None:
    assert trie.root(pairs, secured) == expected


@pytest.mark.parametrize("secured", [False, True])
def test_empty_root(secured: bool) -> None:
    # The root of the empty trie is the hash of 0x80, the RLP encoding of the empty byte string.
    assert trie.root([], secured) == keccak.keccak256(b"\x80")


def test_rejects_malformed_pairs() -> None:
    # A pair must be a list of exactly two byte strings.
    with raises(ValueError, "not enough values to unpack (expected 2, got 1)"):
        trie.root([(b"key",)], False)  # ty: ignore[invalid-argument-type]
