"""The EVM stack instructions and the price of memory, through the bindings."""

import pytest

from ethlib.errors import EvmError
from ethlib.execution.evm import extend_memory, immediate_depths, memory_gas_cost, word_op
from raising import raises

OPCODES = {
    "MOD": 0x06,
    "SDIV": 0x05,
    "SMOD": 0x07,
    "ADDMOD": 0x08,
    "EXP": 0x0A,
    "SIGNEXTEND": 0x0B,
    "LT": 0x10,
    "SLT": 0x12,
    "SGT": 0x13,
    "BYTE": 0x1A,
    "SHL": 0x1B,
    "SHR": 0x1C,
    "SAR": 0x1D,
}

MAX = 2**256 - 1
INT_MIN = 2**255


def signed(value: int) -> int:
    """The word of a signed integer in two's complement."""
    return value % 2**256


# The test cases of EIP-145, "Test Cases".
# Each case is the opcode, the shift, the value and the result.
#
# File: EIPS/eip-145.md
# Repository: ethereum/EIPs
# Commit: b055feec322fbc37e9d77a393a50b3ff56b31c92
# Licence: CC0-1.0
EIP_145 = [
    (
        "SHL",
        0x0,
        0x0000000000000000000000000000000000000000000000000000000000000001,
        0x0000000000000000000000000000000000000000000000000000000000000001,
    ),
    (
        "SHL",
        0x1,
        0x0000000000000000000000000000000000000000000000000000000000000001,
        0x0000000000000000000000000000000000000000000000000000000000000002,
    ),
    (
        "SHL",
        0xFF,
        0x0000000000000000000000000000000000000000000000000000000000000001,
        0x8000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SHL",
        0x100,
        0x0000000000000000000000000000000000000000000000000000000000000001,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SHL",
        0x101,
        0x0000000000000000000000000000000000000000000000000000000000000001,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SHL",
        0x0,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
    ),
    (
        "SHL",
        0x1,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE,
    ),
    (
        "SHL",
        0xFF,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0x8000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SHL",
        0x100,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SHL",
        0x1,
        0x0000000000000000000000000000000000000000000000000000000000000000,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SHL",
        0x1,
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE,
    ),
    (
        "SHR",
        0x0,
        0x0000000000000000000000000000000000000000000000000000000000000001,
        0x0000000000000000000000000000000000000000000000000000000000000001,
    ),
    (
        "SHR",
        0x1,
        0x0000000000000000000000000000000000000000000000000000000000000001,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SHR",
        0x1,
        0x8000000000000000000000000000000000000000000000000000000000000000,
        0x4000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SHR",
        0xFF,
        0x8000000000000000000000000000000000000000000000000000000000000000,
        0x0000000000000000000000000000000000000000000000000000000000000001,
    ),
    (
        "SHR",
        0x100,
        0x8000000000000000000000000000000000000000000000000000000000000000,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SHR",
        0x101,
        0x8000000000000000000000000000000000000000000000000000000000000000,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SHR",
        0x0,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
    ),
    (
        "SHR",
        0x1,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
    ),
    (
        "SHR",
        0xFF,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0x0000000000000000000000000000000000000000000000000000000000000001,
    ),
    (
        "SHR",
        0x100,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SHR",
        0x1,
        0x0000000000000000000000000000000000000000000000000000000000000000,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SAR",
        0x0,
        0x0000000000000000000000000000000000000000000000000000000000000001,
        0x0000000000000000000000000000000000000000000000000000000000000001,
    ),
    (
        "SAR",
        0x1,
        0x0000000000000000000000000000000000000000000000000000000000000001,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SAR",
        0x1,
        0x8000000000000000000000000000000000000000000000000000000000000000,
        0xC000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SAR",
        0xFF,
        0x8000000000000000000000000000000000000000000000000000000000000000,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
    ),
    (
        "SAR",
        0x100,
        0x8000000000000000000000000000000000000000000000000000000000000000,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
    ),
    (
        "SAR",
        0x101,
        0x8000000000000000000000000000000000000000000000000000000000000000,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
    ),
    (
        "SAR",
        0x0,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
    ),
    (
        "SAR",
        0x1,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
    ),
    (
        "SAR",
        0xFF,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
    ),
    (
        "SAR",
        0x100,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
    ),
    (
        "SAR",
        0x1,
        0x0000000000000000000000000000000000000000000000000000000000000000,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SAR",
        0xFE,
        0x4000000000000000000000000000000000000000000000000000000000000000,
        0x0000000000000000000000000000000000000000000000000000000000000001,
    ),
    (
        "SAR",
        0xF8,
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0x000000000000000000000000000000000000000000000000000000000000007F,
    ),
    (
        "SAR",
        0xFE,
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0x0000000000000000000000000000000000000000000000000000000000000001,
    ),
    (
        "SAR",
        0xFF,
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
    (
        "SAR",
        0x100,
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    ),
]


@pytest.mark.parametrize("op, shift, value, result", EIP_145)
def test_eip_145(op: str, shift: int, value: int, result: int) -> None:
    # The shift is on top of the stack, and the value below it.
    assert word_op(OPCODES[op], shift, value) == result


@pytest.mark.parametrize(
    "op, operands, result",
    [
        # A divisor of 0 gives 0.
        ("MOD", (7, 0), 0),
        # -2^255 / -1 overflows to -2^255.
        ("SDIV", (INT_MIN, MAX), INT_MIN),
        # -7 / 2 rounds toward 0, to -3.
        ("SDIV", (signed(-7), 2), signed(-3)),
        # -7 mod 2 takes the sign of the dividend, so -1.
        ("SMOD", (signed(-7), 2), signed(-1)),
        # (2^256 - 1) + 2 = 2^256 + 1, and 2^256 + 1 mod 3 = 2, where wrapping first would give 1.
        ("ADDMOD", (MAX, 2, 3), 2),
        # 2^256 wraps to 0.
        ("EXP", (2, 256), 0),
        # 0x7f has sign bit 0 in one byte, so it stays 0x7f.
        ("SIGNEXTEND", (0, 0x127F), 0x7F),
        # 0xff has sign bit 1 in one byte, so it becomes -1.
        ("SIGNEXTEND", (0, 0xFF), MAX),
        # A byte index above 31 leaves the value.
        ("SIGNEXTEND", (32, 0xFF), 0xFF),
        # -1 is below 0 as a signed word.
        ("SLT", (MAX, 0), 1),
        # 2^256 - 1 is above 0 as an unsigned word.
        ("LT", (MAX, 0), 0),
        # -2^255 is the smallest signed word.
        ("SGT", (INT_MIN, MAX), 0),
        # Byte 31 is the least significant.
        ("BYTE", (31, 0xABCD), 0xCD),
        # Byte 32 is out of range.
        ("BYTE", (32, MAX), 0),
    ],
)
def test_edge_cases(op: str, operands: tuple, result: int) -> None:
    assert word_op(OPCODES[op], *operands) == result


def test_opcode_outside_the_table() -> None:
    # JUMP depends on more than its operands.
    with raises(EvmError, "opcode 86 does not push a word of its operands alone") as info:
        word_op(0x56, 0)
    assert info.value.code == 0


def test_integers_out_of_range() -> None:
    # An opcode is one byte and an operand one word, so Lean rejects a larger integer with code 0.
    with raises(EvmError, "expected an int below 256, got 256") as info:
        word_op(0x100, 0, 0)
    assert info.value.code == 0
    with raises(EvmError, f"expected an int below {2**256}, got {2**256}") as info:
        word_op(0x01, 2**256, 0)
    assert info.value.code == 0
    with raises(OverflowError, "the opcode and the immediate must be below 256"):
        immediate_depths(0xE6, 0x100)
    with raises(ValueError, "cannot pass a negative int to Lean"):
        memory_gas_cost(-1)


@pytest.mark.parametrize("argument", ["opcode", "immediate"])
@pytest.mark.parametrize(
    "value",
    [
        -1,
        256,
        2**32,
        2**32 + 0xE6,
        -(2**32),
        0xE6 - 2**32,
        2**64,
        2**64 + 0xE6,
        -(2**64),
        0xE6 - 2**64,
        2**128,
        -(2**128),
    ],
)
def test_immediate_depths_integer_out_of_range(argument: str, value: int) -> None:
    # Each argument is a byte; values must not wrap at a 32-bit or 64-bit C boundary.
    opcode, immediate = (value, 0) if argument == "opcode" else (0xE6, value)
    with raises(OverflowError, "the opcode and the immediate must be below 256"):
        immediate_depths(opcode, immediate)


@pytest.mark.parametrize(
    "opcode, immediate, message",
    [(0.0, 0, "opcode must be int"), (0xE6, 0.0, "immediate must be int")],
)
def test_immediate_depths_wrong_type(opcode, immediate, message: str) -> None:
    with raises(TypeError, message):
        immediate_depths(opcode, immediate)


class _Index:
    # Not an int, but convertible through `__index__`, which the binding refuses.
    def __index__(self) -> int:
        return 0xE6


class _Int(int):
    pass


def test_immediate_depths_rejects_index_objects() -> None:
    # The calls pass the wrong type on purpose, to check the runtime error.
    with raises(TypeError, "opcode must be int"):
        immediate_depths(_Index(), 0)  # ty: ignore[invalid-argument-type]
    with raises(TypeError, "immediate must be int"):
        immediate_depths(0xE6, _Index())  # ty: ignore[invalid-argument-type]


def test_immediate_depths_accepts_bool_and_int_subclasses() -> None:
    assert immediate_depths(0xE6, True) == immediate_depths(0xE6, 1)
    assert immediate_depths(_Int(0xE6), _Int(0)) == immediate_depths(0xE6, 0)


def test_immediate_depths_opcode_255_reaches_lean() -> None:
    # 255 is the largest byte, so Lean decides it rather than the range check of the binding.
    with raises(EvmError, "byte 0 encodes no depth of opcode 255"):
        immediate_depths(0xFF, 0)


@pytest.mark.parametrize(
    "size, cost",
    [
        # One word costs 3, and 1024 words cost 3 * 1024 + 1024^2 / 512 = 5120.
        (32, 3),
        (32 * 1024, 5120),
    ],
)
def test_memory_gas_cost(size: int, cost: int) -> None:
    assert memory_gas_cost(size) == cost


@pytest.mark.parametrize(
    "current, ranges, result",
    [
        # An empty memory grows by one word, at the price of one word.
        (0, [(0, 32)], (3, 32)),
        # One byte past a word grows memory by a whole word.
        (32, [(32, 1)], (3, 32)),
    ],
)
def test_extend_memory(current: int, ranges: list, result: tuple) -> None:
    assert extend_memory(current, ranges) == result


def test_ranges_out_of_their_type() -> None:
    # Each range is a tuple of two words, and the size of the memory is not negative.
    with raises(EvmError, f"expected an int below {2**256}, got {2**256}") as info:
        extend_memory(0, [(2**256, 1)])
    assert info.value.code == 0
    with raises(EvmError, "expected a tuple") as info:
        extend_memory(0, [0, 32])  # ty: ignore[invalid-argument-type]
    assert info.value.code == 0
    # A range given as a list reads as a tuple.
    assert extend_memory(0, [[0, 32]]) == (3, 32)  # ty: ignore[invalid-argument-type]
    with raises(ValueError, "cannot pass a negative int to Lean"):
        extend_memory(-1, [])


def test_at_most_three_operands() -> None:
    # The count is checked before the opcode, so JUMP with four operands fails on the count.
    for opcode in (0x01, 0x56):
        with raises(EvmError, "an instruction takes at most 3 operands") as info:
            word_op(opcode, 1, 2, 3, 4)
        assert info.value.code == 0


def test_no_ranges() -> None:
    # No range means no growth.
    assert extend_memory(0, []) == (0, 0)
