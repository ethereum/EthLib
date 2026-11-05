"""Test-vector generator: `keccak_f1600` (the permutation)."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import keccak

from . import fixtures

HANDLER = "permutation"


@pytest.mark.parametrize("i", range(len(fixtures.PERMUTATIONS)))
def test_permutation(i: int) -> None:
    # One Keccak team example: the Lean permutation must give the published state.
    state_in, state_out = fixtures.PERMUTATIONS[i]
    assert keccak.keccak_f1600(state_in) == state_out
    # Write the checked vector as one case of the committed suite.
    write_case(
        "keccak",
        HANDLER,
        fixtures.PERMUTATION_NAMES[i],
        {"input": {"state": hex_str(state_in)}, "output": hex_str(state_out)},
    )


@pytest.mark.parametrize("size", [0, 199, 201])
def test_rejects_wrong_size(size: int) -> None:
    # The state is exactly 25 lanes of 8 bytes.
    with pytest.raises(ValueError, match="state: expected 200 bytes"):
        keccak.keccak_f1600(bytes(size))


def test_rejects_non_bytes() -> None:
    # The binding takes only `bytes`.
    with pytest.raises(TypeError):
        keccak.keccak_f1600(bytearray(200))  # ty: ignore[invalid-argument-type]
