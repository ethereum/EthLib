"""The alt_bn128 precompiles of EIP-196 and EIP-197 against py_ecc."""

import pytest
from py_ecc import bn128

from ethlib.precompiles import price, run
from raising import raises

from .forks import since

# py_ecc 8.0.0 computes every expected point independently of EthLib.
#
# Byzantium adds the precompiles, at the prices of EIP-196 and EIP-197.
# They are 500 for an addition, 40000 for a multiplication, and `100000 + 80000 * k` for k pairs.
# From Istanbul, EIP-1108 lowers them to 150, 6000 and `45000 + 34000 * k`.

# The prices change once, at Istanbul, so the calls run on each side of that change and at the
# latest fork. The price test runs at every fork.
FORKS = ("byzantium", "petersburg", "istanbul", "bpo2")
EIP_1108_FORKS = since("istanbul")


def add_price(fork: str) -> int:
    return 150 if fork in EIP_1108_FORKS else 500


def mul_price(fork: str) -> int:
    return 6000 if fork in EIP_1108_FORKS else 40000


def pairing_price(fork: str, k: int) -> int:
    if fork in EIP_1108_FORKS:
        return 45000 + 34000 * k
    return 100000 + 80000 * k


@pytest.mark.parametrize("fork", since("byzantium"))
def test_prices(fork: str) -> None:
    assert price(fork, 0x06, b"") == add_price(fork)
    assert price(fork, 0x07, b"") == mul_price(fork)
    # A partial pair is not counted.
    assert price(fork, 0x08, bytes(2 * 192 + 1)) == pairing_price(fork, 2)


@pytest.mark.parametrize("address", [0x06, 0x07, 0x08])
@pytest.mark.parametrize("fork", since("frontier", "byzantium"))
def test_absent_before_byzantium(fork: str, address: int) -> None:
    with raises(ValueError, f"no precompile at address {address} at fork {fork}"):
        run(fork, address, b"", 10**6)


def out_of_gas(cost: int) -> str:
    """The message of a call that has one gas less than its price."""
    return (
        "EthLib.Execution.Evm.Precompiles.PrecompileError.altBn128\n  "
        f"(EthLib.Execution.Evm.Precompiles.AltBn128.AltBn128Error.outOfGas {cost} {cost - 1})"
    )


def word(value: int) -> bytes:
    return value.to_bytes(32, "big")


def g1(point) -> bytes:
    """A G1 point as two 32-byte words, the point at infinity as zeros."""
    if point is None:
        return bytes(64)
    return word(point[0].n) + word(point[1].n)


def g2(point) -> bytes:
    """A G2 point as four 32-byte words: the imaginary part of each coordinate comes first."""
    x, y = point
    return b"".join(word(int(c)) for c in (x.coeffs[1], x.coeffs[0], y.coeffs[1], y.coeffs[0]))


def mul1(k: int):
    return bn128.multiply(bn128.G1, k)


@pytest.mark.parametrize(
    "a, b",
    [
        (1, 1),
        (1, 2),
        (1, bn128.curve_order - 1),
        (5, 7),
        (3, bn128.curve_order - 3),
        (0, 9),
        (0, 0),
    ],
)
@pytest.mark.parametrize("fork", FORKS)
def test_ecadd(fork: str, a: int, b: int) -> None:
    expected = g1(bn128.add(mul1(a), mul1(b)))
    assert run(fork, 0x06, g1(mul1(a)) + g1(mul1(b)), add_price(fork)) == expected


@pytest.mark.parametrize("fork", FORKS)
def test_ecadd_short_input_is_zero_padded(fork: str) -> None:
    # Missing bytes read as zero, so an empty input adds two points at infinity.
    assert run(fork, 0x06, b"", add_price(fork)) == bytes(64)
    # Call data that stops after G adds the point at infinity to it.
    assert run(fork, 0x06, g1(bn128.G1), add_price(fork)) == g1(bn128.G1)


@pytest.mark.parametrize("fork", FORKS)
def test_ecadd_errors(fork: str) -> None:
    with raises(
        ValueError,
        (
            "EthLib.Execution.Evm.Precompiles.PrecompileError.altBn128\n  "
            "(EthLib.Execution.Evm.Precompiles.AltBn128.AltBn128Error.notOnCurve)"
        ),
    ):
        run(fork, 0x06, word(1) + word(3) + bytes(64), add_price(fork))
    with raises(
        ValueError,
        (
            "EthLib.Execution.Evm.Precompiles.PrecompileError.altBn128\n  "
            "(EthLib.Execution.Evm.Precompiles.AltBn128.AltBn128Error.invalidFieldElement)"
        ),
    ):
        run(fork, 0x06, word(bn128.field_modulus) + word(2) + bytes(64), add_price(fork))
    with raises(ValueError, out_of_gas(add_price(fork))):
        run(fork, 0x06, b"", add_price(fork) - 1)


SCALARS = [
    0,
    1,
    2,
    3,
    2**128 + 1,
    bn128.curve_order - 1,
    bn128.curve_order,
    bn128.curve_order + 1,
    2**256 - 1,
]


@pytest.mark.parametrize("k", SCALARS)
@pytest.mark.parametrize("base", [1, 7])
@pytest.mark.parametrize("fork", FORKS)
def test_ecmul(fork: str, base: int, k: int) -> None:
    # The scalar is not reduced, but the result wraps around the group of order q.
    point = mul1(base)
    assert run(fork, 0x07, g1(point) + word(k), mul_price(fork)) == g1(
        bn128.multiply(point, k % bn128.curve_order)
    )


@pytest.mark.parametrize("fork", FORKS)
def test_ecmul_short_scalar(fork: str) -> None:
    # A missing scalar reads as 0, so the result is the point at infinity.
    assert run(fork, 0x07, g1(bn128.G1), mul_price(fork)) == bytes(64)


@pytest.mark.parametrize("fork", FORKS)
def test_ecmul_not_on_curve(fork: str) -> None:
    with raises(
        ValueError,
        (
            "EthLib.Execution.Evm.Precompiles.PrecompileError.altBn128\n  "
            "(EthLib.Execution.Evm.Precompiles.AltBn128.AltBn128Error.notOnCurve)"
        ),
    ):
        run(fork, 0x07, word(1) + word(3) + word(2), mul_price(fork))


@pytest.mark.parametrize("fork", FORKS)
def test_ecmul_out_of_gas(fork: str) -> None:
    with raises(ValueError, out_of_gas(mul_price(fork))):
        run(fork, 0x07, g1(bn128.G1) + word(2), mul_price(fork) - 1)


def pairing_input(pairs) -> bytes:
    return b"".join(g1(p) + g2(q) for p, q in pairs)


@pytest.mark.parametrize(
    "pairs, holds",
    [
        # The empty product is 1.
        ([], True),
        # e(G1, G2) is not 1.
        ([(bn128.G1, bn128.G2)], False),
        # e(G1, G2) * e(-G1, G2) = 1.
        ([(bn128.G1, bn128.G2), (bn128.neg(bn128.G1), bn128.G2)], True),
        # e(6 G1, 5 G2) * e(-30 G1, G2) = 1, by bilinearity.
        ([(mul1(6), bn128.multiply(bn128.G2, 5)), (bn128.neg(mul1(30)), bn128.G2)], True),
        # e(6 G1, 5 G2) * e(-29 G1, G2) = e(G1, G2), which is not 1.
        ([(mul1(6), bn128.multiply(bn128.G2, 5)), (bn128.neg(mul1(29)), bn128.G2)], False),
        # A pair with a point at infinity contributes 1.
        ([(None, bn128.G2), (bn128.G1, bn128.G2), (bn128.neg(bn128.G1), bn128.G2)], True),
    ],
)
@pytest.mark.parametrize("fork", FORKS)
def test_ecpairing(fork: str, pairs, holds: bool) -> None:
    data = pairing_input(pairs)
    assert run(fork, 0x08, data, pairing_price(fork, len(pairs))) == word(int(holds))
    with raises(ValueError, out_of_gas(pairing_price(fork, len(pairs)))):
        run(fork, 0x08, data, pairing_price(fork, len(pairs)) - 1)


@pytest.mark.parametrize("fork", FORKS)
def test_ecpairing_invalid_length(fork: str) -> None:
    with raises(
        ValueError,
        (
            "EthLib.Execution.Evm.Precompiles.PrecompileError.altBn128\n  "
            "(EthLib.Execution.Evm.Precompiles.AltBn128.AltBn128Error.invalidInputLength 191)"
        ),
    ):
        run(fork, 0x08, bytes(191), 10**6)


@pytest.mark.parametrize("fork", FORKS)
def test_ecpairing_g2_x_is_p(fork: str) -> None:
    # The imaginary part of the G2 x coordinate is p, which is not a field element.
    data = bytearray(pairing_input([(bn128.G1, bn128.G2)]))
    data[64:96] = word(bn128.field_modulus)
    with raises(
        ValueError,
        (
            "EthLib.Execution.Evm.Precompiles.PrecompileError.altBn128\n  "
            "(EthLib.Execution.Evm.Precompiles.AltBn128.AltBn128Error.invalidFieldElement)"
        ),
    ):
        run(fork, 0x08, bytes(data), pairing_price(fork, 1))


@pytest.mark.parametrize("fork", FORKS)
def test_ecpairing_g2_not_on_curve(fork: str) -> None:
    data = bytearray(pairing_input([(bn128.G1, bn128.G2)]))
    data[-1] ^= 1
    with raises(
        ValueError,
        (
            "EthLib.Execution.Evm.Precompiles.PrecompileError.altBn128\n  "
            "(EthLib.Execution.Evm.Precompiles.AltBn128.AltBn128Error.notOnCurve)"
        ),
    ):
        run(fork, 0x08, bytes(data), pairing_price(fork, 1))
