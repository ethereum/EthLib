"""Test-vector generator: `compute_verify_cell_kzg_proof_batch_challenge`."""

from ethlib.cryptography import kzg

from . import fixtures as F
from dumper import hex_list, hex_str, write_case


HANDLER = "compute_verify_cell_kzg_proof_batch_challenge"


def _emit(case: str, *, commitments: list[bytes], commitment_indices: list[int],
          cell_indices: list[int], cosets_evals: list[list[bytes]],
          proofs: list[bytes], valid: bool) -> None:
    challenge: bytes | None
    try:
        challenge = kzg.compute_verify_cell_kzg_proof_batch_challenge(
            commitments, commitment_indices, cell_indices, cosets_evals, proofs,
        )
    except Exception:
        challenge = None
    if valid:
        assert challenge is not None
    else:
        assert challenge is None
    write_case("kzg", HANDLER, case, {
        "input": {
            "commitments":        hex_list(commitments),
            "commitment_indices": commitment_indices,
            "cell_indices":       cell_indices,
            "cosets_evals":       [hex_list(ce) for ce in cosets_evals],
            "proofs":             hex_list(proofs),
        },
        "output": hex_str(challenge) if challenge is not None else None,
    })


def _ce(cell: bytes) -> list[bytes]:
    return F.cell_to_coset_evals(cell)


def test_empty() -> None:
    _emit(f"{HANDLER}_case_empty",
          commitments=[], commitment_indices=[], cell_indices=[],
          cosets_evals=[], proofs=[], valid=True)


def test_single_cell() -> None:
    cells, proofs = F.cached_cells_and_proofs(F.VALID_BLOBS[0])
    com = F.cached_commitment(F.VALID_BLOBS[0])
    _emit(f"{HANDLER}_case_single_cell",
          commitments=[com], commitment_indices=[0], cell_indices=[0],
          cosets_evals=[_ce(cells[0])], proofs=[proofs[0]], valid=True)


def test_multiple_cells_single_blob() -> None:
    cells, proofs = F.cached_cells_and_proofs(F.VALID_BLOBS[1])
    com = F.cached_commitment(F.VALID_BLOBS[1])
    n = 4
    _emit(f"{HANDLER}_case_multiple_cells_single_blob",
          commitments=[com], commitment_indices=[0]*n,
          cell_indices=list(range(n)),
          cosets_evals=[_ce(cells[i]) for i in range(n)],
          proofs=[proofs[i] for i in range(n)], valid=True)


def test_multiple_cells_multiple_blobs() -> None:
    c0, p0 = F.cached_cells_and_proofs(F.VALID_BLOBS[2])
    c1, p1 = F.cached_cells_and_proofs(F.VALID_BLOBS[3])
    com0 = F.cached_commitment(F.VALID_BLOBS[2])
    com1 = F.cached_commitment(F.VALID_BLOBS[3])
    _emit(f"{HANDLER}_case_multiple_cells_multiple_blobs",
          commitments=[com0, com1],
          commitment_indices=[0, 1, 0, 1],
          cell_indices=[0, 1, 2, 3],
          cosets_evals=[_ce(c0[0]), _ce(c1[1]), _ce(c0[2]), _ce(c1[3])],
          proofs=[p0[0], p1[1], p0[2], p1[3]],
          valid=True)


def test_duplicate_cells() -> None:
    cells, proofs = F.cached_cells_and_proofs(F.VALID_BLOBS[4])
    com = F.cached_commitment(F.VALID_BLOBS[4])
    dup = 3
    _emit(f"{HANDLER}_case_duplicate_cells",
          commitments=[com], commitment_indices=[0]*dup, cell_indices=[5]*dup,
          cosets_evals=[_ce(cells[5])]*dup, proofs=[proofs[5]]*dup, valid=True)


def test_many_cells() -> None:
    cells, proofs = F.cached_cells_and_proofs(F.VALID_BLOBS[5])
    com = F.cached_commitment(F.VALID_BLOBS[5])
    half = kzg.CELLS_PER_EXT_BLOB // 2
    _emit(f"{HANDLER}_case_many_cells",
          commitments=[com], commitment_indices=[0]*half,
          cell_indices=list(range(half)),
          cosets_evals=[_ce(cells[i]) for i in range(half)],
          proofs=[proofs[i] for i in range(half)], valid=True)


def test_non_sequential_indices() -> None:
    cells, proofs = F.cached_cells_and_proofs(F.VALID_BLOBS[6])
    com = F.cached_commitment(F.VALID_BLOBS[6])
    indices = [10, 5, 20, 15, 0, 30]
    _emit(f"{HANDLER}_case_non_sequential_indices",
          commitments=[com], commitment_indices=[0]*len(indices),
          cell_indices=indices,
          cosets_evals=[_ce(cells[i]) for i in indices],
          proofs=[proofs[i] for i in indices], valid=True)


def test_mixed_commitment_indices() -> None:
    c0, p0 = F.cached_cells_and_proofs(F.VALID_BLOBS[0])
    c1, p1 = F.cached_cells_and_proofs(F.VALID_BLOBS[1])
    c2, p2 = F.cached_cells_and_proofs(F.VALID_BLOBS[2])
    com0 = F.cached_commitment(F.VALID_BLOBS[0])
    com1 = F.cached_commitment(F.VALID_BLOBS[1])
    com2 = F.cached_commitment(F.VALID_BLOBS[2])
    _emit(f"{HANDLER}_case_mixed_commitment_indices",
          commitments=[com0, com1, com2],
          commitment_indices=[2, 0, 1, 0, 2, 1],
          cell_indices=[0, 1, 2, 3, 4, 5],
          cosets_evals=[
              _ce(c2[0]), _ce(c0[1]), _ce(c1[2]),
              _ce(c0[3]), _ce(c2[4]), _ce(c1[5]),
          ],
          proofs=[p2[0], p0[1], p1[2], p0[3], p2[4], p1[5]],
          valid=True)


def test_max_cell_indices() -> None:
    cells, proofs = F.cached_cells_and_proofs(F.VALID_BLOBS[3])
    com = F.cached_commitment(F.VALID_BLOBS[3])
    mx = kzg.CELLS_PER_EXT_BLOB - 1
    indices = [mx, mx-1, mx-2]
    _emit(f"{HANDLER}_case_max_cell_indices",
          commitments=[com], commitment_indices=[0]*len(indices),
          cell_indices=indices,
          cosets_evals=[_ce(cells[i]) for i in indices],
          proofs=[proofs[i] for i in indices], valid=True)


def test_all_cells() -> None:
    cells, proofs = F.cached_cells_and_proofs(F.VALID_BLOBS[4])
    com = F.cached_commitment(F.VALID_BLOBS[4])
    n = kzg.CELLS_PER_EXT_BLOB
    _emit(f"{HANDLER}_case_all_cells",
          commitments=[com], commitment_indices=[0]*n,
          cell_indices=list(range(n)),
          cosets_evals=[_ce(cells[i]) for i in range(n)],
          proofs=list(proofs), valid=True)
