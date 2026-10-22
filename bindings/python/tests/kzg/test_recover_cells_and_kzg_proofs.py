"""Test-vector generator: `recover_cells_and_kzg_proofs`."""

import random

import pytest

from ethlib.cryptography import kzg

from . import fixtures as F
from dumper import hex_list, write_case


HANDLER = "recover_cells_and_kzg_proofs"


def _emit(case: str, cell_indices: list[int], cells: list[bytes],
          *, valid: bool) -> None:
    output: list[list[str]] | None
    try:
        rec_cells, rec_proofs = kzg.recover_cells_and_kzg_proofs(cell_indices, cells)
        output = [hex_list(rec_cells), hex_list(rec_proofs)]
    except Exception:
        output = None
    assert (output is not None) == valid
    write_case("kzg", HANDLER, case, {
        "input":  {"cell_indices": cell_indices, "cells": hex_list(cells)},
        "output": output,
    })


# ---- Valid cases ----------------------------------------------------------


def test_valid_no_missing() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[0])
    _emit(f"{HANDLER}_case_valid_no_missing",
          list(range(kzg.CELLS_PER_EXT_BLOB)), list(cells), valid=True)


def test_valid_half_missing_every_other_cell() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[1])
    idx = list(range(0, kzg.CELLS_PER_EXT_BLOB, 2))
    _emit(f"{HANDLER}_case_valid_half_missing_every_other_cell",
          idx, [cells[i] for i in idx], valid=True)


def test_valid_half_missing_first_half() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[2])
    idx = list(range(kzg.CELLS_PER_EXT_BLOB // 2))
    _emit(f"{HANDLER}_case_valid_half_missing_first_half",
          idx, [cells[i] for i in idx], valid=True)


def test_valid_half_missing_second_half() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[3])
    idx = list(range(kzg.CELLS_PER_EXT_BLOB // 2, kzg.CELLS_PER_EXT_BLOB))
    _emit(f"{HANDLER}_case_valid_half_missing_second_half",
          idx, [cells[i] for i in idx], valid=True)


# ---- Invalid cases --------------------------------------------------------


def test_invalid_all_cells_are_missing() -> None:
    _emit(f"{HANDLER}_case_invalid_all_cells_are_missing", [], [], valid=False)


def test_invalid_more_than_half_missing() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[4])
    idx = list(range(kzg.CELLS_PER_EXT_BLOB // 2 - 1))
    _emit(f"{HANDLER}_case_invalid_more_than_half_missing",
          idx, [cells[i] for i in idx], valid=False)


def test_invalid_more_cells_than_cells_per_ext_blob() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[5])
    idx = list(range(kzg.CELLS_PER_EXT_BLOB)) + [0]
    _emit(f"{HANDLER}_case_invalid_more_cells_than_cells_per_ext_blob",
          idx, [cells[i] for i in idx], valid=False)


def test_invalid_cell_index() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[6])
    idx = list(range(kzg.CELLS_PER_EXT_BLOB // 2))
    cells_taken = [cells[i] for i in idx]
    idx[0] = kzg.CELLS_PER_EXT_BLOB
    _emit(f"{HANDLER}_case_invalid_cell_index", idx, cells_taken, valid=False)


@pytest.mark.parametrize("i", range(len(F.INVALID_INDIVIDUAL_CELL_BYTES)))
def test_invalid_cell(i: int) -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[6])
    idx = list(range(kzg.CELLS_PER_EXT_BLOB // 2))
    partial = [cells[j] for j in idx]
    partial[0] = F.INVALID_INDIVIDUAL_CELL_BYTES[i]
    _emit(f"{HANDLER}_case_invalid_cell_{i}", idx, partial, valid=False)


def test_invalid_more_cell_indices_than_cells() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[0])
    idx = list(range(0, kzg.CELLS_PER_EXT_BLOB, 2))
    partial = [cells[i] for i in idx]
    _emit(f"{HANDLER}_case_invalid_more_cell_indices_than_cells",
          idx + [kzg.CELLS_PER_EXT_BLOB - 1], partial, valid=False)


def test_invalid_more_cells_than_cell_indices() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[1])
    idx = list(range(0, kzg.CELLS_PER_EXT_BLOB, 2))
    partial = [cells[i] for i in idx] + [F.CELL_RANDOM_VALID1]
    _emit(f"{HANDLER}_case_invalid_more_cells_than_cell_indices",
          idx, partial, valid=False)


def test_invalid_duplicate_cell_index() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[2])
    idx = list(range(kzg.CELLS_PER_EXT_BLOB // 2 + 1))
    partial = [cells[i] for i in idx]
    idx[0] = idx[1]
    _emit(f"{HANDLER}_case_invalid_duplicate_cell_index",
          idx, partial, valid=False)


def test_invalid_shuffled_no_missing() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[4])
    idx = list(range(kzg.CELLS_PER_EXT_BLOB))
    random.Random(42).shuffle(idx)
    _emit(f"{HANDLER}_case_invalid_shuffled_no_missing",
          idx, [cells[i] for i in idx], valid=False)


def test_invalid_shuffled_one_missing() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[5])
    idx = list(range(kzg.CELLS_PER_EXT_BLOB - 1))
    random.Random(42).shuffle(idx)
    _emit(f"{HANDLER}_case_invalid_shuffled_one_missing",
          idx, [cells[i] for i in idx], valid=False)


def test_invalid_shuffled_half_missing() -> None:
    cells, _ = F.cached_cells_and_proofs(F.VALID_BLOBS[5])
    idx = list(range(kzg.CELLS_PER_EXT_BLOB // 2))
    random.Random(42).shuffle(idx)
    _emit(f"{HANDLER}_case_invalid_shuffled_half_missing",
          idx, [cells[i] for i in idx], valid=False)
