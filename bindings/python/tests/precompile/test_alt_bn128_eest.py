"""The alt_bn128 precompiles of EIP-196 and EIP-197 against the cases of execution-specs."""

import json
from pathlib import Path

import pytest

from ethlib.precompiles import run

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
# Repository: ethereum/execution-specs
# Commit: e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e
# Licence: CC0-1.0
#
# `extract_alt_bn128_cases.py` read the `pytest.param` lists with Python's `ast`.
# It evaluated their expressions over the constants of each `spec.py`, without running the files.
# An empty output marks a call that must fail.
# A gas modifier of -1 marks a call given one unit of gas less than its price.
#
# Two kinds of test there are not read.
# The `test_gas.py` files check the price at every fork from Byzantium; `test_alt_bn128.py`
# checks those prices, from EIP-196, EIP-197 and EIP-1108.
# The ported state test `stZeroKnowledge/test_pairing_test.py` calls the precompile from EVM code.
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


VALID = [pytest.param(c, id=c["id"]) for c in CASES if c["output"] and not c["gas_modifier"]]
INVALID = [pytest.param(c, id=c["id"]) for c in CASES if not c["output"] and not c["gas_modifier"]]
SHORT = [pytest.param(c, id=c["id"]) for c in CASES if c["gas_modifier"]]


def test_case_count() -> None:
    # Every case is in exactly one group, and the three groups are those of the files.
    assert len(VALID) + len(INVALID) + len(SHORT) == len(CASES) == 359
    assert (len(VALID), len(INVALID), len(SHORT)) == (173, 183, 3)


@pytest.mark.parametrize("case", VALID)
@pytest.mark.parametrize("fork", FORKS)
def test_valid(fork: str, case: dict) -> None:
    data = bytes.fromhex(case["input"])
    assert run(fork, case["address"], data, price(fork, case["address"], data)).hex() == case["output"]


@pytest.mark.parametrize("case", VALID)
@pytest.mark.parametrize("fork", FORKS)
def test_valid_one_gas_short(fork: str, case: dict) -> None:
    data = bytes.fromhex(case["input"])
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, case["address"], data, price(fork, case["address"], data) - 1)


@pytest.mark.parametrize("case", INVALID)
@pytest.mark.parametrize("fork", FORKS)
def test_invalid(fork: str, case: dict) -> None:
    # The call fails at its full price, so it fails for its input and not for lack of gas.
    data = bytes.fromhex(case["input"])
    with pytest.raises(ValueError, match=r"PrecompileError\.altBn128") as error:
        run(fork, case["address"], data, price(fork, case["address"], data))
    assert "outOfGas" not in str(error.value)


@pytest.mark.parametrize("case", SHORT)
@pytest.mark.parametrize("fork", FORKS)
def test_short_of_gas(fork: str, case: dict) -> None:
    data = bytes.fromhex(case["input"])
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, case["address"], data, price(fork, case["address"], data) + case["gas_modifier"])
