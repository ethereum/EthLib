"""The first fault of a BLS12-381 precompile input of EIP-2537, with the values its error names."""

from py_ecc.optimized_bls12_381 import FQ, FQ2, curve_order, field_modulus, is_inf, multiply

# The base field modulus of EIP-2537, as py_ecc 8.0.0 defines it independently of EthLib.
P = field_modulus

# EIP-2537: a field element is 64 bytes, 16 zero bytes of padding and then 48 bytes.
PADDED, PAD = 64, 16

# The items of the call data of each precompile, and whether its points are in a subgroup check.
# An item is a G1 point, a G2 point, a 32-byte scalar or a field element of Fp or Fp2.
ITEMS = {
    0x0B: (["g1", "g1"], False),
    0x0C: (["g1", "scalar"], True),
    0x0D: (["g2", "g2"], False),
    0x0E: (["g2", "scalar"], True),
    0x0F: (["g1", "g2"], True),
    0x10: (["fp"], False),
    0x11: (["fp2"], False),
}

# The padded field elements of each item.
ELEMENTS = {"g1": 2, "g2": 4, "fp": 1, "fp2": 2, "scalar": 0}
SIZE = {"g1": 128, "g2": 256, "fp": 64, "fp2": 128, "scalar": 32}


def _items(address: int, data: bytes) -> list[tuple[str, bytes]]:
    """The items of the call data, in order; a call repeats its group of items."""
    group, _ = ITEMS[address]
    out, at = [], 0
    while at < len(data):
        for kind in group:
            out.append((kind, data[at : at + SIZE[kind]]))
            at += SIZE[kind]
    return out


def _on_curve(kind: str, values: list[int]) -> bool:
    """Whether an affine point is on its curve: y^2 = x^3 + 4, or y^2 = x^3 + 4 (1 + i) on G2."""
    if kind == "g1":
        x, y = values
        return (y * y - x**3 - 4) % P == 0
    x, y = FQ2(values[0:2]), FQ2(values[2:4])
    return y * y == x * x * x + FQ2([4, 4])


def _in_subgroup(kind: str, values: list[int]) -> bool:
    """Whether a point on its curve has the order of the subgroup."""
    # Each branch multiplies over one field, so the point has one coordinate type.
    if kind == "g1":
        return is_inf(multiply((FQ(values[0]), FQ(values[1]), FQ(1)), curve_order))
    return is_inf(multiply((FQ2(values[0:2]), FQ2(values[2:4]), FQ2([1, 0])), curve_order))


def first_fault(address: int, data: bytes) -> str:
    """The error of an input with a fault after its length check, with the values it names."""
    # Every padding comes first.
    # Then each item in order: its field elements, its curve and, for some calls, its subgroup.
    items = [(kind, raw) for kind, raw in _items(address, data) if kind != "scalar"]
    for kind, raw in items:
        for i in range(ELEMENTS[kind]):
            padding = raw[PADDED * i : PADDED * i + PAD]
            if any(padding):
                return f"invalidPadding (padding := 0x{padding.hex()})"
    _, subgroup = ITEMS[address]
    for kind, raw in items:
        unpadded = b"".join(raw[PADDED * i + PAD : PADDED * (i + 1)] for i in range(ELEMENTS[kind]))
        values = [
            int.from_bytes(unpadded[48 * i : 48 * (i + 1)], "big") for i in range(ELEMENTS[kind])
        ]
        for value in values:
            if value >= P:
                return f"invalidFieldElement (value := {value})"
        if kind in ("fp", "fp2") or not any(values):
            continue
        if not _on_curve(kind, values):
            return f"notOnCurve (point := 0x{unpadded.hex()})"
        if subgroup and not _in_subgroup(kind, values):
            return f"notInSubgroup (point := 0x{unpadded.hex()})"
    raise AssertionError(f"no fault in the input of precompile {address:#x}")
