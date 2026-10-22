"""Test-vector generator: `blob_to_kzg_commitment`."""

import pytest

from ethlib.cryptography import kzg

from . import fixtures as F
from dumper import hex_str, write_case


HANDLER = "blob_to_kzg_commitment"


@pytest.mark.parametrize("i", range(len(F.VALID_BLOBS)))
def test_valid_blob(i: int) -> None:
    blob = F.VALID_BLOBS[i]
    commitment = kzg.blob_to_kzg_commitment(blob)
    write_case(
        "kzg", HANDLER, f"{HANDLER}_case_valid_blob_{i}",
        {"input": {"blob": hex_str(blob)}, "output": hex_str(commitment)},
    )


@pytest.mark.parametrize("i", range(len(F.INVALID_BLOBS)))
def test_invalid_blob(i: int) -> None:
    blob = F.INVALID_BLOBS[i]
    with pytest.raises(Exception):
        kzg.blob_to_kzg_commitment(blob)
    write_case(
        "kzg", HANDLER, f"{HANDLER}_case_invalid_blob_{i}",
        {"input": {"blob": hex_str(blob)}, "output": None},
    )
