"""Test-vector generator: `compute_cells`."""

import pytest

from dumper import hex_list, hex_str, write_case
from ethlib.cryptography import kzg

from . import fixtures

HANDLER = "compute_cells"


@pytest.mark.parametrize("i", range(len(fixtures.VALID_BLOBS)))
def test_valid(i: int) -> None:
    blob = fixtures.VALID_BLOBS[i]
    cells = kzg.compute_cells(blob)
    write_case(
        "kzg",
        HANDLER,
        f"{HANDLER}_case_valid_{i}",
        {"input": {"blob": hex_str(blob)}, "output": hex_list(cells)},
    )


@pytest.mark.parametrize("i", range(len(fixtures.INVALID_BLOBS)))
def test_invalid_blob(i: int) -> None:
    blob = fixtures.INVALID_BLOBS[i]
    with pytest.raises(fixtures.invalid_blob_error(blob)):
        kzg.compute_cells(blob)
    write_case(
        "kzg",
        HANDLER,
        f"{HANDLER}_invalid_blob_{i}",
        {"input": {"blob": hex_str(blob)}, "output": None},
    )
