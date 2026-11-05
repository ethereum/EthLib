"""Test-vector generator: `keccak256` (the hash function)."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import keccak

from . import fixtures as F

HANDLER = "hash"


@pytest.mark.parametrize("i", range(len(F.VECTORS)))
def test_hash(i: int) -> None:
    # One Keccak team vector: the Lean digest must equal the published one.
    message, digest = F.VECTORS[i]
    assert keccak.keccak256(message) == digest
    # Write the checked vector as one case of the committed suite.
    write_case(
        "keccak",
        HANDLER,
        F.CASE_NAMES[i],
        {"input": {"message": hex_str(message)}, "output": hex_str(digest)},
    )


def test_rejects_non_bytes() -> None:
    # The binding takes only `bytes`.
    with pytest.raises(TypeError):
        keccak.keccak256("abc")  # type: ignore[arg-type]
