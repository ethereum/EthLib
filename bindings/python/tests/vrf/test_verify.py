"""Test-vector generator: `verify`."""

# Each opening verifies at its own index with its output, and each rejection changes one input.

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import keccak, vrf
from raising import raises

from . import fixtures

HANDLER = "verify"

# The two openings, by the name of their index.
CASES = {
    "zero": (fixtures.ROOT_ZERO, fixtures.INDEX_ZERO, fixtures.OPENING_ZERO, fixtures.OUTPUT_ZERO),
    "last": (fixtures.ROOT_LAST, fixtures.INDEX_LAST, fixtures.OPENING_LAST, fixtures.OUTPUT_LAST),
}


def _emit(case: str, root: bytes, index: int, opening: bytes, expected: bytes | None) -> None:
    # A rejection is written as a null output.
    result = vrf.verify(root, index, opening)
    assert result == expected
    write_case(
        "vrf",
        HANDLER,
        case,
        {
            "input": {"root": hex_str(root), "index": index, "opening": hex_str(opening)},
            "output": None if result is None else hex_str(result),
        },
    )


@pytest.mark.parametrize("name", CASES)
def test_valid(name: str) -> None:
    root, index, opening, output = CASES[name]
    _emit(f"{HANDLER}_valid_{name}", root, index, opening, output)


@pytest.mark.parametrize("name", CASES)
def test_wrong_secret(name: str) -> None:
    # The first byte of the secret: the leaf changes, so the path reaches another root.
    root, index, opening, _ = CASES[name]
    _emit(f"{HANDLER}_wrong_secret_{name}", root, index, fixtures.flip(opening, 0), None)


@pytest.mark.parametrize("name", CASES)
def test_wrong_sibling(name: str) -> None:
    # The last byte of the top sibling, the last byte of the opening.
    root, index, opening, _ = CASES[name]
    _emit(
        f"{HANDLER}_wrong_sibling_{name}",
        root,
        index,
        fixtures.flip(opening, len(opening) - 1),
        None,
    )


@pytest.mark.parametrize("name, other", [("zero", 1), ("last", 0xFFFF_FFFE)])
def test_other_index(name: str, other: int) -> None:
    # The neighbouring index orders the bottom pair the other way.
    root, _, opening, _ = CASES[name]
    _emit(f"{HANDLER}_other_index_{name}", root, other, opening, None)


def test_index_out_of_range() -> None:
    # Index 2^32 is outside the tree, so even the valid opening at index 0 is rejected.
    _emit(f"{HANDLER}_index_out_of_range", fixtures.ROOT_ZERO, 1 << 32, fixtures.OPENING_ZERO, None)


@pytest.mark.parametrize("field, size", [("root", 31), ("opening", 1055)])
def test_wrong_length(field: str, size: int) -> None:
    # A root or an opening of another length is rejected, never padded or truncated.
    root = fixtures.ROOT_ZERO[:size] if field == "root" else fixtures.ROOT_ZERO
    opening = fixtures.OPENING_ZERO[:size] if field == "opening" else fixtures.OPENING_ZERO
    _emit(f"{HANDLER}_short_{field}", root, fixtures.INDEX_ZERO, opening, None)


def test_one_secret_at_every_leaf() -> None:
    # One secret at all 2^32 leaves: each level has one node value, so 33 hashes build the tree.
    # The same opening verifies at every index, and the output of each index reads that index.
    secret = fixtures.SECRET_ZERO
    path = [keccak.keccak256(b"PQ_VRF_LEAF" + secret)]
    for _ in range(31):
        path.append(keccak.keccak256(b"PQ_VRF_NODE" + path[-1] + path[-1]))
    root = keccak.keccak256(b"PQ_VRF_NODE" + path[-1] + path[-1])
    opening = secret + b"".join(path)
    outputs = {
        index: vrf.verify(root, index, opening) for index in (0, 1, 0x0102_0304, 0xFFFF_FFFF)
    }
    for index, output in outputs.items():
        assert output == keccak.keccak256(b"PQ_VRF_OUTPUT" + index.to_bytes(4, "little") + secret)
    assert len(set(outputs.values())) == len(outputs)


def test_rejects_non_bytes() -> None:
    with raises(TypeError, "root and opening must be bytes"):
        vrf.verify(bytearray(fixtures.ROOT_ZERO), 0, fixtures.OPENING_ZERO)  # ty: ignore[invalid-argument-type]
