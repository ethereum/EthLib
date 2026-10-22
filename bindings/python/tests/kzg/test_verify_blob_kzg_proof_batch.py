"""Test-vector generator: `verify_blob_kzg_proof_batch`."""

import pytest

from ethlib.cryptography import kzg

from . import fixtures as F
from dumper import hex_list, write_case


HANDLER = "verify_blob_kzg_proof_batch"


def _emit(case: str, blobs: list[bytes], commitments: list[bytes],
          proofs: list[bytes], *, expected: bool | None, valid: bool) -> None:
    if valid:
        result = kzg.verify_blob_kzg_proof_batch(blobs, commitments, proofs)
        if expected is not None:
            assert result == expected
    else:
        try:
            result = kzg.verify_blob_kzg_proof_batch(blobs, commitments, proofs)
        except Exception:
            result = None
        assert result is None
    write_case("kzg", HANDLER, case, {
        "input": {
            "blobs":       hex_list(blobs),
            "commitments": hex_list(commitments),
            "proofs":      hex_list(proofs),
        },
        "output": result,
    })


def _all() -> tuple[list[bytes], list[bytes], list[bytes]]:
    blobs = list(F.VALID_BLOBS)
    commitments = [F.cached_commitment(b) for b in blobs]
    proofs = [F.cached_blob_kzg_proof(b, c) for b, c in zip(blobs, commitments)]
    return blobs, commitments, proofs


@pytest.mark.parametrize("length", range(len(F.VALID_BLOBS)))
def test_length(length: int) -> None:
    blobs, commitments, proofs = _all()
    _emit(f"{HANDLER}_case_{length}",
          blobs[:length], commitments[:length], proofs[:length],
          expected=True, valid=True)


def test_incorrect_proof_add_one() -> None:
    blobs, commitments, proofs = _all()
    _emit(f"{HANDLER}_case_incorrect_proof_add_one",
          blobs, commitments,
          [F.bls_add_one(proofs[0])] + proofs[1:],
          expected=False, valid=True)


def test_incorrect_proof_point_at_infinity() -> None:
    blob = F.BLOB_RANDOM_VALID1
    _emit(f"{HANDLER}_case_incorrect_proof_point_at_infinity",
          [blob], [F.cached_commitment(blob)], [F.G1_POINT_AT_INFINITY],
          expected=False, valid=True)


@pytest.mark.parametrize("i", range(len(F.INVALID_BLOBS)))
def test_invalid_blob(i: int) -> None:
    blobs, commitments, proofs = _all()
    blobs = list(F.VALID_BLOBS[:4]) + [F.INVALID_BLOBS[i]] + list(F.VALID_BLOBS[5:])
    _emit(f"{HANDLER}_case_invalid_blob_{i}",
          blobs, commitments, proofs, expected=None, valid=False)


@pytest.mark.parametrize("i", range(len(F.INVALID_G1_POINTS)))
def test_invalid_commitment(i: int) -> None:
    blobs, commitments, proofs = _all()
    commitments = [F.INVALID_G1_POINTS[i]] + commitments[1:]
    _emit(f"{HANDLER}_case_invalid_commitment_{i}",
          blobs, commitments, proofs, expected=None, valid=False)


@pytest.mark.parametrize("i", range(len(F.INVALID_G1_POINTS)))
def test_invalid_proof(i: int) -> None:
    blobs, commitments, proofs = _all()
    proofs = [F.INVALID_G1_POINTS[i]] + proofs[1:]
    _emit(f"{HANDLER}_case_invalid_proof_{i}",
          blobs, commitments, proofs, expected=None, valid=False)


def test_blob_length_different() -> None:
    blobs, commitments, proofs = _all()
    _emit(f"{HANDLER}_case_blob_length_different",
          blobs[:-1], commitments, proofs, expected=None, valid=False)


def test_commitment_length_different() -> None:
    blobs, commitments, proofs = _all()
    _emit(f"{HANDLER}_case_commitment_length_different",
          blobs, commitments[:-1], proofs, expected=None, valid=False)


def test_proof_length_different() -> None:
    blobs, commitments, proofs = _all()
    _emit(f"{HANDLER}_case_proof_length_different",
          blobs, commitments, proofs[:-1], expected=None, valid=False)
