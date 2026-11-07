"""The alt_bn128 precompiles of EIP-196 and EIP-197 against the cases of execution-specs."""

import json
from pathlib import Path

import pytest

from ethlib import precompiles
from ethlib.precompiles import run
from raising import raises

from .forks import since

# The prices change once, at Istanbul (EIP-1108).
# So the cases run on each side of that change and at the latest fork.
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
# The gas modifier is added to the price.
# With -1 the call must run out of gas, and an invalid input fails with any extra gas.
#
# The `test_gas.py` files give no price; the price below is that of EIP-196, EIP-197 and EIP-1108.
# The ported state test `stZeroKnowledge/test_pairing_test.py` calls the precompile from EVM code.
# So it is not read.
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

# The field modulus p and the group order r of EIP-196 and EIP-197.
P = 0x30644E72E131A029B85045B68181585D97816A916871CA8D3C208C16D87CFD47
R = 0x30644E72E131A029B85045B68181585D2833E84879B9709143E1F593F0000001

# An element a + b * i of F_p^2 = F_p[i] / (i^2 + 1) is the pair (a, b).
Fq2 = tuple[int, int]


def fq2_add(a: Fq2, b: Fq2) -> Fq2:
    """The sum in F_p^2."""
    return ((a[0] + b[0]) % P, (a[1] + b[1]) % P)


def fq2_sub(a: Fq2, b: Fq2) -> Fq2:
    """The difference in F_p^2."""
    return ((a[0] - b[0]) % P, (a[1] - b[1]) % P)


def fq2_mul(a: Fq2, b: Fq2) -> Fq2:
    """The product in F_p^2."""
    return ((a[0] * b[0] - a[1] * b[1]) % P, (a[0] * b[1] + a[1] * b[0]) % P)


def fq2_inv(a: Fq2) -> Fq2:
    """The inverse in F_p^2 of a nonzero element: (a - b * i) / (a^2 + b^2)."""
    norm = pow(a[0] * a[0] + a[1] * a[1], -1, P)
    return (a[0] * norm % P, -a[1] * norm % P)


# The twist of EIP-197 is y^2 = x^3 + 3 / (9 + i).
TWIST_B = fq2_mul((3, 0), fq2_inv((9, 1)))


def g2_add(a: tuple[Fq2, Fq2] | None, b: tuple[Fq2, Fq2] | None) -> tuple[Fq2, Fq2] | None:
    """The sum of two points of the twist in affine form, with None for the point at infinity."""
    if a is None:
        return b
    if b is None:
        return a
    if a[0] == b[0] and a[1] != b[1]:
        return None
    if a == b:
        x_squared = fq2_mul(a[0], a[0])
        slope = fq2_mul(
            fq2_add(fq2_add(x_squared, x_squared), x_squared), fq2_inv(fq2_add(a[1], a[1]))
        )
    else:
        slope = fq2_mul(fq2_sub(b[1], a[1]), fq2_inv(fq2_sub(b[0], a[0])))
    x = fq2_sub(fq2_sub(fq2_mul(slope, slope), a[0]), b[0])
    return (x, fq2_sub(fq2_mul(slope, fq2_sub(a[0], x)), a[1]))


def g2_times_r(point: tuple[Fq2, Fq2]) -> tuple[Fq2, Fq2] | None:
    """The point times the group order r, by double and add."""
    result = None
    for bit in bin(R)[2:]:
        result = g2_add(result, result)
        if bit == "1":
            result = g2_add(result, point)
    return result


def g1_variant(x: int, y: int) -> str | None:
    """The error of a G1 point of EIP-196, or None for a point of the curve y^2 = x^3 + 3."""
    if x >= P or y >= P:
        return "invalidFieldElement"
    if (x, y) != (0, 0) and (y * y - x**3 - 3) % P != 0:
        return "notOnCurve"
    return None


def invalid_variant(address: int, data: bytes) -> str:
    """The error of an input that EIP-196 or EIP-197 rejects, read from its bytes in order."""
    # ECADD reads two G1 points and ECMUL one, from the input padded with zeros.
    if address in (0x06, 0x07):
        padded = data.ljust(128, b"\0")
        for offset in (0, 64) if address == 0x06 else (0,):
            x = int.from_bytes(padded[offset : offset + 32], "big")
            y = int.from_bytes(padded[offset + 32 : offset + 64], "big")
            if variant := g1_variant(x, y):
                return variant
        raise AssertionError("an invalid case with a valid ECADD or ECMUL input")
    # A pairing input is a list of 192-byte pairs of a G1 point and a G2 point.
    # EIP-197 fixes no order among the errors.
    # So a case with several faults expects the first one that a reader meets.
    # The reader checks each pair in full before the next.
    if len(data) % 192 != 0:
        return f"invalidInputLength {len(data)}"
    for offset in range(0, len(data), 192):
        words = [
            int.from_bytes(data[offset + i : offset + i + 32], "big") for i in range(0, 192, 32)
        ]
        if variant := g1_variant(words[0], words[1]):
            return variant
        if any(word >= P for word in words[2:]):
            return "invalidFieldElement"
        # EIP-197 writes each coordinate of G2 as its imaginary part, then its real part.
        g2 = ((words[3], words[2]), (words[5], words[4]))
        if g2 == ((0, 0), (0, 0)):
            continue
        x_cubed = fq2_mul(fq2_mul(g2[0], g2[0]), g2[0])
        if fq2_mul(g2[1], g2[1]) != fq2_add(x_cubed, TWIST_B):
            return "notOnCurve"
        if g2_times_r(g2) is not None:
            return "notInSubgroup"
    raise AssertionError("an invalid case with a valid pairing input")


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
    with raises(ValueError, error(invalid_variant(case["address"], data))):
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
