"""Test-vector generator: `verify_kzg_proof`."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import kzg

from . import fixtures

HANDLER = "verify_kzg_proof"


def _emit(
    case: str,
    commitment: bytes,
    z: bytes,
    y: bytes,
    proof: bytes,
    *,
    expected: bool | None,
    valid: bool,
) -> None:
    if valid:
        result = kzg.verify_kzg_proof(commitment, z, y, proof)
        if expected is not None:
            assert result == expected
    else:
        try:
            result = kzg.verify_kzg_proof(commitment, z, y, proof)
        except Exception:
            result = None
        assert result is None
    write_case(
        "kzg",
        HANDLER,
        case,
        {
            "input": {
                "commitment": hex_str(commitment),
                "z": hex_str(z),
                "y": hex_str(y),
                "proof": hex_str(proof),
            },
            "output": result,
        },
    )


@pytest.mark.parametrize("bi", range(len(fixtures.VALID_BLOBS)))
@pytest.mark.parametrize("zi", range(len(fixtures.VALID_FIELD_ELEMENTS)))
def test_correct_proof(bi: int, zi: int) -> None:
    blob, z = fixtures.VALID_BLOBS[bi], fixtures.VALID_FIELD_ELEMENTS[zi]
    proof, y = fixtures.cached_kzg_proof(blob, z)
    commitment = fixtures.cached_commitment(blob)
    _emit(
        f"{HANDLER}_case_correct_proof_{bi}_{zi}",
        commitment,
        z,
        y,
        proof,
        expected=True,
        valid=True,
    )


@pytest.mark.parametrize("bi", range(len(fixtures.VALID_BLOBS)))
@pytest.mark.parametrize("zi", range(len(fixtures.VALID_FIELD_ELEMENTS)))
def test_incorrect_proof(bi: int, zi: int) -> None:
    blob, z = fixtures.VALID_BLOBS[bi], fixtures.VALID_FIELD_ELEMENTS[zi]
    proof, y = fixtures.cached_kzg_proof(blob, z)
    commitment = fixtures.cached_commitment(blob)
    _emit(
        f"{HANDLER}_case_incorrect_proof_{bi}_{zi}",
        commitment,
        z,
        y,
        fixtures.bls_add_one(proof),
        expected=False,
        valid=True,
    )


@pytest.mark.parametrize("zi", range(len(fixtures.VALID_FIELD_ELEMENTS)))
def test_incorrect_proof_point_at_infinity(zi: int) -> None:
    blob = fixtures.BLOB_RANDOM_VALID1
    z = fixtures.VALID_FIELD_ELEMENTS[zi]
    _, y = fixtures.cached_kzg_proof(blob, z)
    _emit(
        f"{HANDLER}_case_incorrect_proof_point_at_infinity_{zi}",
        fixtures.cached_commitment(blob),
        z,
        y,
        fixtures.G1_POINT_AT_INFINITY,
        expected=False,
        valid=True,
    )


@pytest.mark.parametrize("zi", range(len(fixtures.VALID_FIELD_ELEMENTS)))
def test_correct_proof_point_at_infinity_for_zero_poly(zi: int) -> None:
    blob = fixtures.BLOB_ALL_ZEROS
    z = fixtures.VALID_FIELD_ELEMENTS[zi]
    _, y = fixtures.cached_kzg_proof(blob, z)
    _emit(
        f"{HANDLER}_case_correct_proof_point_at_infinity_for_zero_poly_{zi}",
        fixtures.cached_commitment(blob),
        z,
        y,
        fixtures.G1_POINT_AT_INFINITY,
        expected=True,
        valid=True,
    )


@pytest.mark.parametrize("zi", range(len(fixtures.VALID_FIELD_ELEMENTS)))
def test_correct_proof_point_at_infinity_for_twos_poly(zi: int) -> None:
    blob = fixtures.BLOB_ALL_TWOS
    z = fixtures.VALID_FIELD_ELEMENTS[zi]
    _, y = fixtures.cached_kzg_proof(blob, z)
    _emit(
        f"{HANDLER}_case_correct_proof_point_at_infinity_for_twos_poly_{zi}",
        fixtures.cached_commitment(blob),
        z,
        y,
        fixtures.G1_POINT_AT_INFINITY,
        expected=True,
        valid=True,
    )


@pytest.mark.parametrize("i", range(len(fixtures.INVALID_G1_POINTS)))
def test_invalid_commitment(i: int) -> None:
    blob, z = fixtures.VALID_BLOBS[2], fixtures.VALID_FIELD_ELEMENTS[1]
    proof, y = fixtures.cached_kzg_proof(blob, z)
    _emit(
        f"{HANDLER}_case_invalid_commitment_{i}",
        fixtures.INVALID_G1_POINTS[i],
        z,
        y,
        proof,
        expected=None,
        valid=False,
    )


@pytest.mark.parametrize("i", range(len(fixtures.INVALID_FIELD_ELEMENTS)))
def test_invalid_z(i: int) -> None:
    blob, validz = fixtures.VALID_BLOBS[4], fixtures.VALID_FIELD_ELEMENTS[1]
    proof, y = fixtures.cached_kzg_proof(blob, validz)
    _emit(
        f"{HANDLER}_case_invalid_z_{i}",
        fixtures.cached_commitment(blob),
        fixtures.INVALID_FIELD_ELEMENTS[i],
        y,
        proof,
        expected=None,
        valid=False,
    )


@pytest.mark.parametrize("i", range(len(fixtures.INVALID_FIELD_ELEMENTS)))
def test_invalid_y(i: int) -> None:
    blob, z = fixtures.VALID_BLOBS[4], fixtures.VALID_FIELD_ELEMENTS[1]
    proof, _ = fixtures.cached_kzg_proof(blob, z)
    _emit(
        f"{HANDLER}_case_invalid_y_{i}",
        fixtures.cached_commitment(blob),
        z,
        fixtures.INVALID_FIELD_ELEMENTS[i],
        proof,
        expected=None,
        valid=False,
    )


@pytest.mark.parametrize("i", range(len(fixtures.INVALID_G1_POINTS)))
def test_invalid_proof(i: int) -> None:
    blob, z = fixtures.VALID_BLOBS[2], fixtures.VALID_FIELD_ELEMENTS[1]
    _, y = fixtures.cached_kzg_proof(blob, z)
    _emit(
        f"{HANDLER}_case_invalid_proof_{i}",
        fixtures.cached_commitment(blob),
        z,
        y,
        fixtures.INVALID_G1_POINTS[i],
        expected=None,
        valid=False,
    )
