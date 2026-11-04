"""The BLS12-381 precompiles against the vectors of EIP-2537."""

import json
from pathlib import Path

import pytest

from ethlib.precompiles import run

# The cases of EIP-2537, keyed by file, except the MSM cases with more than 8 pairs.
#
# Directory: assets/eip-2537
# Repository: ethereum/EIPs
# Commit: 0ce679f4654ba4d120c97113626f320475e22fa9
# Licence: CC0-1.0
CASES = json.loads((Path(__file__).parent / "eip2537_cases.json").read_text())

# The address of the precompile that each file tests.
ADDRESS = {
    "add_G1_bls": 0x0B,
    "add_G2_bls": 0x0D,
    "mul_G1_bls": 0x0C,
    "mul_G2_bls": 0x0E,
    "msm_G1_bls": 0x0C,
    "msm_G2_bls": 0x0E,
    "pairing_check_bls": 0x0F,
    "map_fp_to_G1_bls": 0x10,
    "map_fp2_to_G2_bls": 0x11,
}

# The error of the Lean specification for each error that the vectors name.
ERROR = {
    "invalid input length": "invalidInputLength",
    "invalid field element top bytes": "invalidPadding",
    "invalid fp.Element encoding": "invalidFieldElement",
    "invalid point: not on curve": "notOnCurve",
    "g1 point is not in the correct subgroup": "notInSubgroup",
    "g2 point is not in the correct subgroup": "notInSubgroup",
}

# A failing case lists no gas, so it runs with more than any of these calls costs.
AMPLE_GAS = 10**9

SUCCESS = [
    pytest.param(ADDRESS[name], case, id=f"{name}:{case['Name']}")
    for name, cases in CASES.items()
    if not name.startswith("fail-")
    for case in cases
]

FAILURE = [
    pytest.param(ADDRESS[name.removeprefix("fail-")], case, id=f"{name}:{case['Name']}")
    for name, cases in CASES.items()
    if name.startswith("fail-")
    for case in cases
]


@pytest.mark.parametrize("address, case", SUCCESS)
def test_exact_price(address: int, case: dict) -> None:
    assert run(address, bytes.fromhex(case["Input"]), case["Gas"]).hex() == case["Expected"]


@pytest.mark.parametrize("address, case", SUCCESS)
def test_one_gas_short(address: int, case: dict) -> None:
    with pytest.raises(ValueError, match="outOfGas"):
        run(address, bytes.fromhex(case["Input"]), case["Gas"] - 1)


@pytest.mark.parametrize("address, case", FAILURE)
def test_error(address: int, case: dict) -> None:
    with pytest.raises(ValueError, match=rf"\.{ERROR[case['ExpectedError']]}\b"):
        run(address, bytes.fromhex(case["Input"]), AMPLE_GAS)
