"""The BLS12-381 precompiles against the vectors of EIP-2537 that the kernel does not run.

`eip2537_cases.json` holds cases of `assets/eip-2537` in `ethereum/EIPs`, at commit
`d386b29b5a31bd5cfd8d21bbf4e8a0c87734085e`, under CC0-1.0:

- every case of `pairing_check_bls.json`;
- the cases of `msm_G1_bls.json` and `msm_G2_bls.json` with 5 to 8 pairs.

The Lean known answers run the other files, and the MSM cases with at most 4 pairs.
"""

import json
from pathlib import Path

import pytest

from ethlib.precompiles import run

CASES = json.loads((Path(__file__).parent / "eip2537_cases.json").read_text())

ADDRESS = {"pairing": 0x0F, "msm_g1": 0x0C, "msm_g2": 0x0E}

PARAMS = [
    pytest.param(ADDRESS[kind], case, id=f"{kind}:{case['Name']}")
    for kind, cases in CASES.items()
    for case in cases
]


@pytest.mark.parametrize("address, case", PARAMS)
def test_exact_price(address: int, case: dict) -> None:
    assert run(address, bytes.fromhex(case["Input"]), case["Gas"]).hex() == case["Expected"]


@pytest.mark.parametrize("address, case", PARAMS)
def test_one_gas_short(address: int, case: dict) -> None:
    with pytest.raises(ValueError, match="outOfGas"):
        run(address, bytes.fromhex(case["Input"]), case["Gas"] - 1)
