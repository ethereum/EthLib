"""Which error a bad input of the cell checks produces, by its code and its message."""

from ethlib.cryptography import kzg
from raising import raises

# The inputs are all zero.
# Every case fails on a count or an index.
# The checks of the counts and of the indices come before the checks of the points.
# So the zero bytes never reach a point check.
COMMITMENT = bytes(kzg.BYTES_PER_COMMITMENT)
CELL = bytes(kzg.BYTES_PER_CELL)
PROOF = bytes(kzg.BYTES_PER_PROOF)


def test_verify_cells_missing() -> None:
    """A batch with a commitment but no cell fails on the cells."""
    with raises(kzg.KzgError, "input length mismatch: cells has length 0, expected 1") as info:
        kzg.verify_cell_kzg_proof_batch([COMMITMENT], [0], [], [PROOF])
    assert info.value.code == 9


def test_verify_proofs_missing() -> None:
    """A batch with a commitment but no proof fails on the proofs."""
    message = "input length mismatch: proofsBytes has length 0, expected 1"
    with raises(kzg.KzgError, message) as info:
        kzg.verify_cell_kzg_proof_batch([COMMITMENT], [0], [CELL], [])
    assert info.value.code == 9


def test_verify_extra_cell_index() -> None:
    """A batch with two cell indices for one commitment fails on the indices."""
    message = "input length mismatch: cellIndices has length 2, expected 1"
    with raises(kzg.KzgError, message) as info:
        kzg.verify_cell_kzg_proof_batch([COMMITMENT], [0, 1], [CELL], [PROOF])
    assert info.value.code == 9


def test_verify_cell_index_out_of_bounds() -> None:
    """The index 128 is one past the last cell of an extended blob."""
    with raises(kzg.KzgError, "cell index out of bounds") as info:
        kzg.verify_cell_kzg_proof_batch([COMMITMENT], [kzg.CELLS_PER_EXT_BLOB], [CELL], [PROOF])
    assert info.value.code == 12


def test_recover_cells_missing() -> None:
    """An index with no cell fails on the cells."""
    with raises(kzg.KzgError, "input length mismatch: cells has length 0, expected 1") as info:
        kzg.recover_cells_and_kzg_proofs([0], [])
    assert info.value.code == 9


def test_recover_not_enough_cells() -> None:
    """Fewer than half of the 128 cells do not recover the blob."""
    half = kzg.CELLS_PER_EXT_BLOB // 2
    with raises(kzg.KzgError, "not enough cells provided") as info:
        kzg.recover_cells_and_kzg_proofs(list(range(half - 1)), [CELL] * (half - 1))
    assert info.value.code == 14


def test_recover_too_many_cells() -> None:
    """More cells than an extended blob holds are rejected, before their indices are read."""
    count = kzg.CELLS_PER_EXT_BLOB + 1
    with raises(kzg.KzgError, "too many cells provided") as info:
        kzg.recover_cells_and_kzg_proofs(list(range(count)), [CELL] * count)
    assert info.value.code == 15


def test_recover_cell_index_out_of_bounds() -> None:
    """Half of the cells are given, the last at the index 128."""
    indices = [*range(65, kzg.CELLS_PER_EXT_BLOB), kzg.CELLS_PER_EXT_BLOB]
    with raises(kzg.KzgError, "cell index out of bounds") as info:
        kzg.recover_cells_and_kzg_proofs(indices, [CELL] * len(indices))
    assert info.value.code == 12


def test_recover_repeated_index() -> None:
    """Half of the cells are given, the last at the index of the one before."""
    indices = [*range(63), 62]
    with raises(kzg.KzgError, "indices not strictly ascending") as info:
        kzg.recover_cells_and_kzg_proofs(indices, [CELL] * len(indices))
    assert info.value.code == 13


# These two errors come from the C layer.
# They are ValueErrors, and no Lean code has run when they are raised.
def test_blob_batch_counts_differ() -> None:
    """A batch of two blobs with one commitment and one proof fails on the counts."""
    blob = bytes(kzg.BYTES_PER_BLOB)
    with raises(ValueError, "blobs/commitments/proofs must have equal length"):
        kzg.verify_blob_kzg_proof_batch([blob, blob], [COMMITMENT], [PROOF])


def test_challenge_short_coset() -> None:
    """A coset of one field element, where a cell holds 64, is rejected."""
    short = [bytes(kzg.BYTES_PER_FIELD_ELEMENT)]
    with raises(ValueError, "each cosets_evals[i] must have FIELD_ELEMENTS_PER_CELL entries"):
        kzg.compute_verify_cell_kzg_proof_batch_challenge([], [], [], [short], [])
