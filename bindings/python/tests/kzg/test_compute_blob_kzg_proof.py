"""Test-vector generator: `compute_blob_kzg_proof`."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import kzg

from . import fixtures

HANDLER = "compute_blob_kzg_proof"


def _emit(case: str, blob: bytes, commitment: bytes, valid: bool) -> None:
    proof: bytes | None
    try:
        proof = kzg.compute_blob_kzg_proof(blob, commitment)
    except Exception:
        proof = None
    assert (proof is not None) == valid
    write_case(
        "kzg",
        HANDLER,
        case,
        {
            "input": {"blob": hex_str(blob), "commitment": hex_str(commitment)},
            "output": hex_str(proof) if proof is not None else None,
        },
    )


@pytest.mark.parametrize("i", range(len(fixtures.VALID_BLOBS)))
def test_valid_blob(i: int) -> None:
    blob = fixtures.VALID_BLOBS[i]
    _emit(f"{HANDLER}_case_valid_blob_{i}", blob, fixtures.cached_commitment(blob), valid=True)


@pytest.mark.parametrize("i", range(len(fixtures.INVALID_BLOBS)))
def test_invalid_blob(i: int) -> None:
    _emit(f"{HANDLER}_case_invalid_blob_{i}", fixtures.INVALID_BLOBS[i], fixtures.G1, valid=False)


@pytest.mark.parametrize("i", range(len(fixtures.INVALID_G1_POINTS)))
def test_invalid_commitment(i: int) -> None:
    _emit(
        f"{HANDLER}_case_invalid_commitment_{i}",
        fixtures.VALID_BLOBS[1],
        fixtures.INVALID_G1_POINTS[i],
        valid=False,
    )
