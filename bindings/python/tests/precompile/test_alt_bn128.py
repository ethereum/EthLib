"""The alt_bn128 precompiles of EIP-196 and EIP-197 against py_ecc.

py_ecc 8.0.0 computes every expected point independently of EthLib.

The prices are those of EIP-1108: 150 for an addition, 6000 for a multiplication,
and `45000 + 34000 * k` for a pairing check on `k` pairs.
"""

import pytest
from py_ecc import bn128

from ethlib.precompiles import run


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


@pytest.mark.parametrize("a, b", [
    (1, 1), (1, 2), (1, bn128.curve_order - 1), (5, 7), (3, bn128.curve_order - 3), (0, 9), (0, 0),
])
def test_ecadd(a: int, b: int) -> None:
    expected = g1(bn128.add(mul1(a), mul1(b)))
    assert run(0x06, g1(mul1(a)) + g1(mul1(b)), 150) == expected


def test_ecadd_short_input_is_zero_padded() -> None:
    # Missing bytes read as zero, so an empty input adds two points at infinity.
    assert run(0x06, b"", 150) == bytes(64)
    # Call data that stops after G adds the point at infinity to it.
    assert run(0x06, g1(bn128.G1), 150) == g1(bn128.G1)


def test_ecadd_errors() -> None:
    with pytest.raises(ValueError, match="notOnCurve"):
        run(0x06, word(1) + word(3) + bytes(64), 150)
    with pytest.raises(ValueError, match="invalidFieldElement"):
        run(0x06, word(bn128.field_modulus) + word(2) + bytes(64), 150)
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x06, b"", 149)


SCALARS = [
    0, 1, 2, 3, 2**128 + 1, bn128.curve_order - 1, bn128.curve_order, bn128.curve_order + 1,
    2**256 - 1,
]


@pytest.mark.parametrize("k", SCALARS)
@pytest.mark.parametrize("base", [1, 7])
def test_ecmul(base: int, k: int) -> None:
    # The scalar is not reduced, but the result wraps around the group of order q.
    point = mul1(base)
    assert run(0x07, g1(point) + word(k), 6000) == g1(bn128.multiply(point, k % bn128.curve_order))


def test_ecmul_short_scalar() -> None:
    # A missing scalar reads as 0, so the result is the point at infinity.
    assert run(0x07, g1(bn128.G1), 6000) == bytes(64)


def test_ecmul_not_on_curve() -> None:
    with pytest.raises(ValueError, match="notOnCurve"):
        run(0x07, word(1) + word(3) + word(2), 6000)


def test_ecmul_out_of_gas() -> None:
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x07, g1(bn128.G1) + word(2), 5999)


def pairing_input(pairs) -> bytes:
    return b"".join(g1(p) + g2(q) for p, q in pairs)


def pairing_price(k: int) -> int:
    return 45000 + 34000 * k


@pytest.mark.parametrize("pairs, holds", [
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
])
def test_ecpairing(pairs, holds: bool) -> None:
    data = pairing_input(pairs)
    assert run(0x08, data, pairing_price(len(pairs))) == word(int(holds))
    with pytest.raises(ValueError, match="outOfGas"):
        run(0x08, data, pairing_price(len(pairs)) - 1)


def test_ecpairing_invalid_length() -> None:
    with pytest.raises(ValueError, match="invalidInputLength"):
        run(0x08, bytes(191), 10**6)


def test_ecpairing_g2_x_is_p() -> None:
    # The imaginary part of the G2 x coordinate is p, which is not a field element.
    data = bytearray(pairing_input([(bn128.G1, bn128.G2)]))
    data[64:96] = word(bn128.field_modulus)
    with pytest.raises(ValueError, match="invalidFieldElement"):
        run(0x08, bytes(data), pairing_price(1))


def test_ecpairing_g2_not_on_curve() -> None:
    data = bytearray(pairing_input([(bn128.G1, bn128.G2)]))
    data[-1] ^= 1
    with pytest.raises(ValueError, match="notOnCurve"):
        run(0x08, bytes(data), pairing_price(1))
