"""Test-vector generator: `sha256` (the hash function)."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import sha256
from raising import raises

from . import fixtures

HANDLER = "hash"


@pytest.mark.parametrize("i", range(len(fixtures.VECTORS)))
def test_hash(i: int) -> None:
    # One NIST vector: the Lean digest must equal the published one.
    message, digest = fixtures.VECTORS[i]
    assert sha256.sha256(message) == digest
    # Write the checked vector as one case of the committed suite.
    write_case(
        "sha256",
        HANDLER,
        fixtures.CASE_NAMES[i],
        {"input": {"message": hex_str(message)}, "output": hex_str(digest)},
    )


def test_rejects_non_bytes() -> None:
    # The binding takes only `bytes`.
    with raises(TypeError, "data must be bytes"):
        sha256.sha256("abc")  # ty: ignore[invalid-argument-type]
