"""Test-vector generator: `compute_challenge`."""

import pytest

from dumper import hex_str, write_case
from ethlib.cryptography import kzg

from . import fixtures

HANDLER = "compute_challenge"


def _emit(case: str, blob: bytes, commitment: bytes) -> None:
    challenge = kzg.compute_challenge(blob, commitment)
    write_case(
        "kzg",
        HANDLER,
        case,
        {
            "input": {"blob": hex_str(blob), "commitment": hex_str(commitment)},
            "output": hex_str(challenge),
        },
    )


@pytest.mark.parametrize("i", range(len(fixtures.VALID_BLOBS)))
def test_valid(i: int) -> None:
    blob = fixtures.VALID_BLOBS[i]
    _emit(f"{HANDLER}_case_valid_{i}", blob, fixtures.cached_commitment(blob))


def test_mismatched_commitment() -> None:
    _emit(
        f"{HANDLER}_case_mismatched_commitment",
        fixtures.VALID_BLOBS[3],
        fixtures.cached_commitment(fixtures.VALID_BLOBS[4]),
    )


def test_commitment_at_infinity() -> None:
    _emit(
        f"{HANDLER}_case_commitment_at_infinity",
        fixtures.VALID_BLOBS[4],
        fixtures.G1_POINT_AT_INFINITY,
    )
