"""Test-vector generator: `compute_cells_and_kzg_proofs`."""

import pytest

from dumper import hex_list, hex_str, write_case
from ethlib.cryptography import kzg

from . import fixtures

HANDLER = "compute_cells_and_kzg_proofs"


@pytest.mark.parametrize("i", range(len(fixtures.VALID_BLOBS)))
def test_valid(i: int) -> None:
    blob = fixtures.VALID_BLOBS[i]
    cells, proofs = fixtures.cached_cells_and_proofs(blob)
    write_case(
        "kzg",
        HANDLER,
        f"{HANDLER}_case_valid_{i}",
        {
            "input": {"blob": hex_str(blob)},
            "output": [hex_list(cells), hex_list(proofs)],
        },
    )


@pytest.mark.parametrize("i", range(len(fixtures.INVALID_BLOBS)))
def test_invalid_blob(i: int) -> None:
    blob = fixtures.INVALID_BLOBS[i]
    with pytest.raises(fixtures.invalid_blob_error(blob)):
        kzg.compute_cells_and_kzg_proofs(blob)
    write_case(
        "kzg",
        HANDLER,
        f"{HANDLER}_case_invalid_blob_{i}",
        {"input": {"blob": hex_str(blob)}, "output": None},
    )
