"""The ECRECOVER precompile against the cases of execution-specs.

`execution_specs_cases.json` holds every case of `test_precompiles` in
`tests/frontier/precompiles/test_ecrecover.py`, in `ethereum/execution-specs`
at commit e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e, under CC0-1.0.

Each case is the 128-byte input, `hash || v || r || s`, and the expected output.
They were read from that file's `pytest.param` lists, without running anything.
"""

import json
from pathlib import Path

import pytest

from ethlib.precompiles.ecrecover import ECRECOVER_GAS, ecrecover

CASES = json.loads((Path(__file__).resolve().parent / "execution_specs_cases.json").read_text())


@pytest.mark.parametrize("case", CASES, ids=[c["id"] for c in CASES])
def test_execution_specs(case) -> None:
    assert ecrecover(bytes.fromhex(case["input"]), ECRECOVER_GAS) == bytes.fromhex(case["output"])


def test_out_of_gas() -> None:
    with pytest.raises(ValueError):
        ecrecover(bytes.fromhex(CASES[0]["input"]), ECRECOVER_GAS - 1)


def test_trailing_bytes_ignored() -> None:
    case = CASES[0]
    data = bytes.fromhex(case["input"])
    assert ecrecover(data + b"\x01" * 50, ECRECOVER_GAS) == bytes.fromhex(case["output"])
