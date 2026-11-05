"""Test-vector generator: `verify_blob_kzg_proof`."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import kzg

from . import fixtures

HANDLER = "verify_blob_kzg_proof"


def _emit(
    case: str, blob: bytes, commitment: bytes, proof: bytes, *, expected: bool | None, valid: bool
) -> None:
    if valid:
        result = kzg.verify_blob_kzg_proof(blob, commitment, proof)
        if expected is not None:
            assert result == expected
    else:
        try:
            result = kzg.verify_blob_kzg_proof(blob, commitment, proof)
        except Exception:
            result = None
        assert result is None
    write_case(
        "kzg",
        HANDLER,
        case,
        {
            "input": {
                "blob": hex_str(blob),
                "commitment": hex_str(commitment),
                "proof": hex_str(proof),
            },
            "output": result,
        },
    )


@pytest.mark.parametrize("i", range(len(fixtures.VALID_BLOBS)))
def test_correct_proof(i: int) -> None:
    blob = fixtures.VALID_BLOBS[i]
    commitment = fixtures.cached_commitment(blob)
    proof = fixtures.cached_blob_kzg_proof(blob, commitment)
    _emit(f"{HANDLER}_case_correct_proof_{i}", blob, commitment, proof, expected=True, valid=True)


@pytest.mark.parametrize("i", range(len(fixtures.VALID_BLOBS)))
def test_incorrect_proof(i: int) -> None:
    blob = fixtures.VALID_BLOBS[i]
    commitment = fixtures.cached_commitment(blob)
    proof = fixtures.cached_blob_kzg_proof(blob, commitment)
    _emit(
        f"{HANDLER}_case_incorrect_proof_{i}",
        blob,
        commitment,
        fixtures.bls_add_one(proof),
        expected=False,
        valid=True,
    )


def test_incorrect_proof_point_at_infinity() -> None:
    blob = fixtures.BLOB_RANDOM_VALID1
    _emit(
        f"{HANDLER}_case_incorrect_proof_point_at_infinity",
        blob,
        fixtures.cached_commitment(blob),
        fixtures.G1_POINT_AT_INFINITY,
        expected=False,
        valid=True,
    )


def test_correct_proof_point_at_infinity_for_zero_poly() -> None:
    blob = fixtures.BLOB_ALL_ZEROS
    _emit(
        f"{HANDLER}_case_correct_proof_point_at_infinity_for_zero_poly",
        blob,
        fixtures.cached_commitment(blob),
        fixtures.G1_POINT_AT_INFINITY,
        expected=True,
        valid=True,
    )


def test_correct_proof_point_at_infinity_for_twos_poly() -> None:
    blob = fixtures.BLOB_ALL_TWOS
    _emit(
        f"{HANDLER}_case_correct_proof_point_at_infinity_for_twos_poly",
        blob,
        fixtures.cached_commitment(blob),
        fixtures.G1_POINT_AT_INFINITY,
        expected=True,
        valid=True,
    )


@pytest.mark.parametrize("i", range(len(fixtures.INVALID_BLOBS)))
def test_invalid_blob(i: int) -> None:
    _emit(
        f"{HANDLER}_case_invalid_blob_{i}",
        fixtures.INVALID_BLOBS[i],
        fixtures.G1,
        fixtures.G1,
        expected=None,
        valid=False,
    )


@pytest.mark.parametrize("i", range(len(fixtures.INVALID_G1_POINTS)))
def test_invalid_commitment(i: int) -> None:
    _emit(
        f"{HANDLER}_case_invalid_commitment_{i}",
        fixtures.VALID_BLOBS[1],
        fixtures.INVALID_G1_POINTS[i],
        fixtures.G1,
        expected=None,
        valid=False,
    )


@pytest.mark.parametrize("i", range(len(fixtures.INVALID_G1_POINTS)))
def test_invalid_proof(i: int) -> None:
    _emit(
        f"{HANDLER}_case_invalid_proof_{i}",
        fixtures.VALID_BLOBS[1],
        fixtures.G1,
        fixtures.INVALID_G1_POINTS[i],
        expected=None,
        valid=False,
    )
