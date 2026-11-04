"""Test-vector generator: `verify`.

Each opening verifies at its own index with its output, and each rejection changes one input.
"""

import pytest

from ethlib.cryptography import vrf

from . import fixtures as F
from dumper import hex_str, write_case


HANDLER = "verify"

# The two openings, by the name of their index.
CASES = {
    "zero": (F.ROOT_ZERO, F.INDEX_ZERO, F.OPENING_ZERO, F.OUTPUT_ZERO),
    "last": (F.ROOT_LAST, F.INDEX_LAST, F.OPENING_LAST, F.OUTPUT_LAST),
}


def _emit(case: str, root: bytes, index: int, opening: bytes, expected: bytes | None) -> None:
    # A rejection is written as a null output.
    result = vrf.verify(root, index, opening)
    assert result == expected
    write_case("vrf", HANDLER, case, {
        "input": {"root": hex_str(root), "index": index, "opening": hex_str(opening)},
        "output": None if result is None else hex_str(result),
    })


@pytest.mark.parametrize("name", CASES)
def test_valid(name: str) -> None:
    root, index, opening, output = CASES[name]
    _emit(f"{HANDLER}_valid_{name}", root, index, opening, output)


@pytest.mark.parametrize("name", CASES)
def test_wrong_secret(name: str) -> None:
    # The first byte of the secret: the leaf changes, so the path reaches another root.
    root, index, opening, _ = CASES[name]
    _emit(f"{HANDLER}_wrong_secret_{name}", root, index, F.flip(opening, 0), None)


@pytest.mark.parametrize("name", CASES)
def test_wrong_sibling(name: str) -> None:
    # The last byte of the top sibling, the last byte of the opening.
    root, index, opening, _ = CASES[name]
    _emit(f"{HANDLER}_wrong_sibling_{name}", root, index, F.flip(opening, len(opening) - 1), None)


@pytest.mark.parametrize("name, other", [("zero", 1), ("last", 0xFFFF_FFFE)])
def test_other_index(name: str, other: int) -> None:
    # The neighbouring index orders the bottom pair the other way.
    root, _, opening, _ = CASES[name]
    _emit(f"{HANDLER}_other_index_{name}", root, other, opening, None)


def test_index_out_of_range() -> None:
    # Index 2^32 is outside the tree, so even the valid opening at index 0 is rejected.
    _emit(f"{HANDLER}_index_out_of_range", F.ROOT_ZERO, 1 << 32, F.OPENING_ZERO, None)


@pytest.mark.parametrize("field, size", [("root", 31), ("opening", 1055)])
def test_wrong_length(field: str, size: int) -> None:
    # A root or an opening of another length is rejected, never padded or truncated.
    root = F.ROOT_ZERO[:size] if field == "root" else F.ROOT_ZERO
    opening = F.OPENING_ZERO[:size] if field == "opening" else F.OPENING_ZERO
    _emit(f"{HANDLER}_short_{field}", root, F.INDEX_ZERO, opening, None)


def test_rejects_non_bytes() -> None:
    with pytest.raises(TypeError):
        vrf.verify(bytearray(F.ROOT_ZERO), 0, F.OPENING_ZERO)  # type: ignore[arg-type]
