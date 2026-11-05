"""The alt_bn128 precompiles of EIP-196 and EIP-197 against the cases of execution-specs."""

import json
from pathlib import Path

import pytest

from ethlib import precompiles
from ethlib.precompiles import run
from raising import raises

from .forks import since

# The prices change once, at Istanbul (EIP-1108), so the cases run on each side of that change
# and at the latest fork.
FORKS = ("byzantium", "petersburg", "istanbul", "bpo2")
EIP_1108_FORKS = since("istanbul")

# Every input and output case of the tests of EIP-196 and EIP-197.
#
# Directory: tests/byzantium
# Files: eip196_ec_add_mul/test_ecadd.py, eip196_ec_add_mul/test_ecmul.py
# Files: eip197_ec_pairing/test_ecpairing.py, eip197_ec_pairing/test_ecpairing_fuzzed.py
# Files: eip196_ec_add_mul/test_gas.py, eip197_ec_pairing/test_gas.py
# Repository: ethereum/execution-specs
# Commit: e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e
# Licence: CC0-1.0
#
# `extract_alt_bn128_cases.py` read the `pytest.param` lists with Python's `ast`.
# It evaluated their expressions over the constants of each `spec.py`, without running the files.
# An empty output marks a call that must fail, and a null output one that must succeed.
# The gas modifier is added to the price: -1 must run out of gas, and an invalid input fails
# with any extra gas.
#
# The `test_gas.py` files give no price; the price below is that of EIP-196, EIP-197 and EIP-1108.
# The ported state test `stZeroKnowledge/test_pairing_test.py` calls the precompile from EVM code,
# so it is not read.
CASES = json.loads((Path(__file__).parent / "alt_bn128_cases.json").read_text())


def price(fork: str, address: int, data: bytes) -> int:
    """The price of EIP-196 and EIP-197 before Istanbul, and of EIP-1108 from Istanbul on."""
    if fork not in EIP_1108_FORKS:
        if address == 0x06:
            return 500
        if address == 0x07:
            return 40000
        return 100000 + 80000 * (len(data) // 192)
    if address == 0x06:
        return 150
    if address == 0x07:
        return 6000
    # A pairing check costs 34000 per pair of 192 bytes, and 45000 more.
    return 45000 + 34000 * (len(data) // 192)


def _group(test) -> list:
    return [pytest.param(c, id=c["id"]) for c in CASES if test(c)]


VALID = _group(lambda c: c["output"] and c["gas_modifier"] == 0)
SUCCEEDS = _group(lambda c: c["output"] is None)
INVALID = _group(lambda c: c["output"] == "" and c["gas_modifier"] >= 0)
SHORT = _group(lambda c: c["gas_modifier"] < 0)

# The error of each invalid case, as EthLib reports it; every G2 subgroup case is notInSubgroup.
INVALID_ERROR = {
    "eip196_ec_add_mul/test_gas::test_invalid_gas_consumption[ecadd-exact]": "notOnCurve",
    "eip196_ec_add_mul/test_gas::test_invalid_gas_consumption[ecadd-extra_100k]": "notOnCurve",
    "eip196_ec_add_mul/test_gas::test_invalid_gas_consumption[ecmul-exact]": "notOnCurve",
    "eip196_ec_add_mul/test_gas::test_invalid_gas_consumption[ecmul-extra_100k]": "notOnCurve",
    "eip197_ec_pairing/test_gas::"
    "test_invalid_gas_consumption[invalid_g1_point-exact]": "notOnCurve",
    "eip197_ec_pairing/test_gas::"
    "test_invalid_gas_consumption[invalid_g1_point-extra_100k]": "notOnCurve",
    "test_ecadd::test_invalid[0_P_plus_inf]": "invalidFieldElement",
    "test_ecadd::test_invalid[1_Pplus2_plus_inf]": "invalidFieldElement",
    "test_ecadd::test_invalid[P_0_plus_inf]": "invalidFieldElement",
    "test_ecadd::test_invalid[Pplus1_2_plus_inf]": "invalidFieldElement",
    "test_ecadd::test_invalid[inf_plus_0_P]": "invalidFieldElement",
    "test_ecadd::test_invalid[inf_plus_1_Pplus2]": "invalidFieldElement",
    "test_ecadd::test_invalid[inf_plus_P_0]": "invalidFieldElement",
    "test_ecadd::test_invalid[inf_plus_Pplus1_2]": "invalidFieldElement",
    "test_ecadd::test_invalid[inf_plus_pt_1_3]": "notOnCurve",
    "test_ecadd::test_invalid[not_on_curve_plus_not_on_curve]": "notOnCurve",
    "test_ecadd::test_invalid[not_on_curve_plus_valid]": "notOnCurve",
    "test_ecadd::test_invalid[pt_0_3_plus_inf]": "notOnCurve",
    "test_ecadd::test_invalid[pt_1_1_plus_inf]": "notOnCurve",
    "test_ecadd::test_invalid[pt_1_3_plus_16_zero_bytes]": "notOnCurve",
    "test_ecadd::test_invalid[pt_1_3_plus_1_zero_byte]": "notOnCurve",
    "test_ecadd::test_invalid[pt_1_3_plus_32_zero_bytes]": "notOnCurve",
    "test_ecadd::test_invalid[pt_6_9_plus_pt_0x126198c_0x1e4dc]": "notOnCurve",
    "test_ecadd::test_invalid[valid_plus_not_on_curve]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_0_3-32_extra_byte_0x00]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_0_3-length_80]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_0_3_no_scalar]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_0_3_times_2_pow_128-length_80]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_0_3_times_2_pow_128]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_0_3_times_2_pow_256_minus_1]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_0_3_times_group_order]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_0_3_times_group_order_minus_one]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_0_3_times_nine]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_0_3_times_one]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_0_3_times_two]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_0_3_times_zero]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_1_3-32_extra_byte_0x00]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_1_3-length_80]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_1_3_no_scalar]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_1_3_times_2_pow_128-length_80]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_1_3_times_2_pow_128]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_1_3_times_2_pow_256_minus_1]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_1_3_times_group_order]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_1_3_times_group_order_minus_one]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_1_3_times_nine]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_1_3_times_one]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_1_3_times_two]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_1_3_times_zero]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_7827_6598_times_one]": "notOnCurve",
    "test_ecmul::test_invalid[not_on_curve_7827_6598_times_zero]": "notOnCurve",
    "test_ecmul::test_invalid[x_eq_P]": "invalidFieldElement",
    "test_ecmul::test_invalid[x_plus_P]": "invalidFieldElement",
    "test_ecmul::test_invalid[y_eq_P]": "invalidFieldElement",
    "test_ecmul::test_invalid[y_plus_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[bad_length_191]": "invalidInputLength 191",
    "test_ecpairing::test_invalid[bad_length_193]": "invalidInputLength 193",
    "test_ecpairing::test_invalid[g1_not_on_curve]": "notOnCurve",
    "test_ecpairing::test_invalid[g1_x_eq_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g1_x_plus_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g1_y_eq_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g1_y_plus_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_x0_eq_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_x0_plus_N]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_x0_plus_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_x0_plus_one]": "notOnCurve",
    "test_ecpairing::test_invalid[g2_x1_eq_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_x1_plus_N]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_x1_plus_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_x1_plus_one]": "notOnCurve",
    "test_ecpairing::test_invalid[g2_y0_eq_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_y0_plus_N]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_y0_plus_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_y0_plus_one]": "notOnCurve",
    "test_ecpairing::test_invalid[g2_y1_eq_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_y1_plus_N]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_y1_plus_P]": "invalidFieldElement",
    "test_ecpairing::test_invalid[g2_y1_plus_one]": "notOnCurve",
    "test_ecpairing::test_invalid[one_point_not_in_subgroup]": "notOnCurve",
    "test_ecpairing::test_invalid[one_point_with_g2_zero_and_g1_invalid]": "notOnCurve",
    "test_ecpairing::test_invalid[perturb_x0_by_curve_order]": "notOnCurve",
    "test_ecpairing::test_invalid[perturb_x1_by_curve_order]": "notOnCurve",
    "test_ecpairing::test_invalid[perturb_zeropoint_by_field_modulus]": "invalidFieldElement",
    "test_ecpairing::test_invalid[perturb_zeropoint_by_one]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data0]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data10]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data11]": "invalidFieldElement",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data12]": "invalidFieldElement",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data1]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data2]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data3]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data4]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data5]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data6]": "invalidFieldElement",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data7]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data8]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g1_point[input_data9]": "invalidFieldElement",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data0]": "invalidFieldElement",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data10]": "invalidFieldElement",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data11]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data12]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data13]": "invalidFieldElement",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data1]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data2]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data3]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data4]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data5]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data6]": "invalidFieldElement",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data7]": "notOnCurve",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data8]": "invalidFieldElement",
    "test_ecpairing_fuzzed::test_invalid_g2_point[input_data9]": "invalidFieldElement",
}


def error(variant: str) -> str:
    """The message of a failed call, from the variant of its error."""
    return (
        "EthLib.Execution.Evm.Precompiles.PrecompileError.altBn128\n  "
        f"(EthLib.Execution.Evm.Precompiles.AltBn128.AltBn128Error.{variant})"
    )


def test_case_count() -> None:
    # Every case is in exactly one group.
    groups = (VALID, SUCCEEDS, INVALID, SHORT)
    assert sum(map(len, groups)) == len(CASES) == 371
    assert tuple(map(len, groups)) == (173, 3, 189, 6)


@pytest.mark.parametrize("case", VALID)
@pytest.mark.parametrize("fork", FORKS)
def test_valid(fork: str, case: dict) -> None:
    data = bytes.fromhex(case["input"])
    assert (
        run(fork, case["address"], data, price(fork, case["address"], data)).hex() == case["output"]
    )


@pytest.mark.parametrize("case", VALID)
@pytest.mark.parametrize("fork", FORKS)
def test_valid_one_gas_short(fork: str, case: dict) -> None:
    data = bytes.fromhex(case["input"])
    cost = price(fork, case["address"], data)
    with raises(ValueError, error(f"outOfGas {cost} {cost - 1}")):
        run(fork, case["address"], data, cost - 1)


@pytest.mark.parametrize("case", INVALID)
@pytest.mark.parametrize("fork", FORKS)
def test_invalid(fork: str, case: dict) -> None:
    # The call fails at its price or above, so it fails for its input and not for lack of gas.
    data = bytes.fromhex(case["input"])
    if case["id"].startswith("test_ecpairing_fuzzed::test_invalid_g2_subgroup["):
        expected = "notInSubgroup"
    else:
        expected = INVALID_ERROR[case["id"]]
    with raises(ValueError, error(expected)):
        run(fork, case["address"], data, price(fork, case["address"], data) + case["gas_modifier"])


@pytest.mark.parametrize("case", SUCCEEDS)
@pytest.mark.parametrize("fork", FORKS)
def test_succeeds_at_price(fork: str, case: dict) -> None:
    # The file checks only that the call succeeds; the length is that of the precompile's output.
    data = bytes.fromhex(case["input"])
    out = run(fork, case["address"], data, price(fork, case["address"], data))
    assert len(out) == (32 if case["address"] == 0x08 else 64)


@pytest.mark.parametrize("case", SHORT)
@pytest.mark.parametrize("fork", FORKS)
def test_short_of_gas(fork: str, case: dict) -> None:
    data = bytes.fromhex(case["input"])
    cost = price(fork, case["address"], data)
    with raises(ValueError, error(f"outOfGas {cost} {cost + case['gas_modifier']}")):
        run(fork, case["address"], data, cost + case["gas_modifier"])


@pytest.mark.parametrize("fork", FORKS)
def test_price_export(fork: str) -> None:
    # The price that EthLib exports is the price of the EIPs, on every input of the files.
    for case in CASES:
        data = bytes.fromhex(case["input"])
        assert precompiles.price(fork, case["address"], data) == price(fork, case["address"], data)
