"""Test-vector generator: `sha256` (the hash function)."""

import pytest

from ethlib.cryptography import sha256

from . import fixtures as F
from dumper import hex_str, write_case


HANDLER = "hash"


@pytest.mark.parametrize("i", range(len(F.VECTORS)))
def test_hash(i: int) -> None:
    message, digest = F.VECTORS[i]
    assert sha256.sha256(message) == digest
    write_case(
        "sha256", HANDLER, F.CASE_NAMES[i],
        {"input": {"message": hex_str(message)}, "output": hex_str(digest)},
    )
