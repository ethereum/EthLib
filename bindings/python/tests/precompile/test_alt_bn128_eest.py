"""The alt_bn128 precompiles of EIP-196 and EIP-197 against the cases of execution-specs."""

import json
from pathlib import Path

import pytest

from ethlib import precompiles
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
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, case["address"], data, price(fork, case["address"], data) - 1)


@pytest.mark.parametrize("case", INVALID)
@pytest.mark.parametrize("fork", FORKS)
def test_invalid(fork: str, case: dict) -> None:
    # The call fails at its price or above, so it fails for its input and not for lack of gas.
    data = bytes.fromhex(case["input"])
    with pytest.raises(ValueError, match=r"PrecompileError\.altBn128") as error:
        run(fork, case["address"], data, price(fork, case["address"], data) + case["gas_modifier"])
    assert "outOfGas" not in str(error.value)


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
    with pytest.raises(ValueError, match="outOfGas"):
        run(fork, case["address"], data, price(fork, case["address"], data) + case["gas_modifier"])


@pytest.mark.parametrize("fork", FORKS)
def test_price_export(fork: str) -> None:
    # The price that EthLib exports is the price of the EIPs, on every input of the files.
    for case in CASES:
        data = bytes.fromhex(case["input"])
        assert precompiles.price(fork, case["address"], data) == price(fork, case["address"], data)
