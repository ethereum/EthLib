"""The words of EVM stack instructions, the price of EVM memory and created addresses."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native


def immediate_depths(opcode: int, immediate: int) -> tuple[int, ...]:
    """The depths that the immediate byte of DUPN, SWAPN or EXCHANGE encodes, by EIP-8024."""
    return tuple(_native.evm_immediate_depths(opcode, immediate))


def word_op(opcode: int, *operands: int) -> int:
    """The word that an opcode pushes, at a fork that has it, for operands missing ones as 0."""
    return _native.evm_word_op(opcode, list(operands))


def memory_gas_cost(size: int) -> int:
    """The price of a memory of `size` bytes."""
    return _native.evm_memory_gas_cost(size)


def extend_memory(current_size: int, ranges: list[tuple[int, int]]) -> tuple[int, int]:
    """The price of growing a memory for the ranges `(start, size)`, and the bytes it grows by."""
    return _native.evm_extend_memory(current_size, ranges)


def create_address(sender: bytes, nonce: int) -> bytes:
    """The address of the contract that `sender` creates with CREATE at `nonce`."""
    return _native.evm_create_address(sender, nonce)


def create2_address(sender: bytes, salt: bytes, init_code: bytes) -> bytes:
    """The address of the contract that `sender` creates with CREATE2."""
    return _native.evm_create2_address(sender, salt, init_code)


__all__ = [
    "immediate_depths",
    "word_op",
    "memory_gas_cost",
    "extend_memory",
    "create_address",
    "create2_address",
]
