"""Test-vector generator: `compute_cells`."""

import pytest

from ethlib.cryptography import kzg

from . import fixtures as F
from dumper import hex_list, hex_str, write_case


HANDLER = "compute_cells"


@pytest.mark.parametrize("i", range(len(F.VALID_BLOBS)))
def test_valid(i: int) -> None:
    blob = F.VALID_BLOBS[i]
    cells = kzg.compute_cells(blob)
    write_case("kzg", HANDLER, f"{HANDLER}_case_valid_{i}",
               {"input":  {"blob": hex_str(blob)},
                "output": hex_list(cells)})


@pytest.mark.parametrize("i", range(len(F.INVALID_BLOBS)))
def test_invalid_blob(i: int) -> None:
    blob = F.INVALID_BLOBS[i]
    with pytest.raises(Exception):
        kzg.compute_cells(blob)
    write_case("kzg", HANDLER, f"{HANDLER}_invalid_blob_{i}",
               {"input": {"blob": hex_str(blob)}, "output": None})
