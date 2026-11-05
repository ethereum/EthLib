"""Test-vector generator: `keccak512` (the hash function)."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import keccak
from raising import raises

from . import fixtures

HANDLER = "hash_512"


@pytest.mark.parametrize("i", range(len(fixtures.VECTORS_512)))
def test_hash512(i: int) -> None:
    # One Keccak team vector: the Lean digest must equal the published one.
    message, digest = fixtures.VECTORS_512[i]
    assert keccak.keccak512(message) == digest
    # Write the checked vector as one case of the committed suite.
    write_case(
        "keccak",
        HANDLER,
        fixtures.CASE_NAMES_512[i],
        {"input": {"message": hex_str(message)}, "output": hex_str(digest)},
    )


def test_rejects_non_bytes() -> None:
    # The binding takes only `bytes`.
    with raises(TypeError, "data must be bytes"):
        keccak.keccak512("abc")  # ty: ignore[invalid-argument-type]
