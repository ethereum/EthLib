"""Test-vector generator: `compute_kzg_proof`."""

import pytest

from ethlib.cryptography import kzg

from . import fixtures as F
from dumper import hex_str, write_case


HANDLER = "compute_kzg_proof"


def _emit(case: str, blob: bytes, z: bytes, valid: bool) -> None:
    output: list[str] | None = None
    try:
        proof, y = kzg.compute_kzg_proof(blob, z)
        output = [hex_str(proof), hex_str(y)]
    except Exception:
        pass
    assert (output is not None) == valid
    write_case("kzg", HANDLER, case, {
        "input":  {"blob": hex_str(blob), "z": hex_str(z)},
        "output": output,
    })


@pytest.mark.parametrize("bi", range(len(F.VALID_BLOBS)))
@pytest.mark.parametrize("zi", range(len(F.VALID_FIELD_ELEMENTS)))
def test_valid(bi: int, zi: int) -> None:
    _emit(f"{HANDLER}_case_valid_blob_{bi}_{zi}",
          F.VALID_BLOBS[bi], F.VALID_FIELD_ELEMENTS[zi], valid=True)


@pytest.mark.parametrize("i", range(len(F.INVALID_BLOBS)))
def test_invalid_blob(i: int) -> None:
    _emit(f"{HANDLER}_case_invalid_blob_{i}",
          F.INVALID_BLOBS[i], F.VALID_FIELD_ELEMENTS[0], valid=False)


@pytest.mark.parametrize("i", range(len(F.INVALID_FIELD_ELEMENTS)))
def test_invalid_z(i: int) -> None:
    _emit(f"{HANDLER}_case_invalid_z_{i}",
          F.VALID_BLOBS[4], F.INVALID_FIELD_ELEMENTS[i], valid=False)
