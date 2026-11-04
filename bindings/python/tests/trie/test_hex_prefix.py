"""The hex-prefix encoding of trie paths against the cases of ethereum/tests."""

# `trietests/README.md` gives the origin of `hexencodetest.json` and its licence.

import json
from pathlib import Path

import pytest

from ethlib.errors import TrieError
from ethlib.execution import trie

_FILE = Path(__file__).resolve().parent / "trietests" / "hexencodetest.json"
_CASES = json.loads(_FILE.read_text())


@pytest.mark.parametrize("name", list(_CASES))
def test_hexencodetest(name: str) -> None:
    case = _CASES[name]
    assert trie.hex_prefix(case["seq"], case["term"]).hex() == case["out"]


@pytest.mark.parametrize("nibbles, out", [
    # Worked by hand from HP of Appendix C of the Yellow Paper.
    # An even leaf path: the flag 2 and a padding nibble 0 make the first byte.
    ([0, 0xF, 1, 0xC, 0xB, 8], "200f1cb8"),
    # An odd leaf path: the flag 3 and the first nibble share the first byte.
    ([0xF, 1, 0xC, 0xB, 8], "3f1cb8"),
])
def test_leaf_paths(nibbles: list[int], out: str) -> None:
    assert trie.hex_prefix(nibbles, True).hex() == out


def test_not_a_nibble() -> None:
    with pytest.raises(TrieError) as info:
        trie.hex_prefix([16], False)
    assert info.value.code == 0
