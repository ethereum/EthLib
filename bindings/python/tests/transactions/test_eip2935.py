"""Compare the EIP-2935 history contract's lookup with its Python model."""

from collections.abc import Iterator
from random import Random

from .evm_harness import Call, Outcome, check_bytecode

HISTORY_ADDRESS = bytes.fromhex("0000f90827f1c53a10cb7a02335b175320002935")
HISTORY_WINDOW = 8191

# The deployment input of "Block hash history contract", "Deployment", in EIP-2935.
#
# File: EIPS/eip-2935.md
# Repository: ethereum/EIPs
# Commit: b055feec322fbc37e9d77a393a50b3ff56b31c92
# Licence: CC0-1.0
HISTORY_DEPLOYMENT = bytes.fromhex(
    "60538060095f395ff33373fffffffffffffffffffffffffffffffffffffffe1460465760"
    "2036036042575f35600143038111604257611fff81430311604257611fff9006545f5260"
    "205ff35b5f5ffd5b5f35611fff60014303065500"
)
# The nine bytes of the constructor copy the 0x53 bytes of the runtime that follow them.
CONSTRUCTOR = bytes.fromhex("60538060095f395ff3")
HISTORY_CODE = HISTORY_DEPLOYMENT[len(CONSTRUCTOR) :]


def _lookup(call: Call) -> Outcome:
    """Model the `get` and `Bytecode` sections of EIP-2935 for an ordinary caller."""
    if len(call.calldata) != 32:
        return Outcome("revert", b"")
    number = int.from_bytes(call.calldata, "big")
    if number < call.block_number - HISTORY_WINDOW or number >= call.block_number:
        return Outcome("revert", b"")
    return Outcome("success", call.storage.get(number % HISTORY_WINDOW, bytes(32)))


def _cases(rng: Random) -> Iterator[Call]:
    """Yield the range and length boundaries, then calls at random blocks with random hashes."""
    # At block 8192, the previous block is in slot 0 and the oldest valid block is in slot 1.
    block = HISTORY_WINDOW + 1
    storage = {0: b"\x00" + b"\x11" * 31, 1: b"\x22" * 32}
    # Block 0 collides with the parent slot and block 8192 collides with the oldest slot.
    # Block 2 looks up a slot that has never been written.
    for number in (0, 1, 2, block - 1, block, 2**256 - 1):
        yield Call(number.to_bytes(32, "big"), block, storage)
    # Read whole or padded to one word, each of these names block 31 or 7936, both in range.
    # So only the calldata length makes them revert.
    yield Call(bytes(30) + b"\x1f", block, storage)
    yield Call(bytes(31) + b"\x1f\x00", block, storage)
    # Block 1 can look up genesis, even before the ring has filled.
    yield Call(bytes(32), 1, storage)
    # Empty calldata reads as genesis, which is in range at block 1.
    yield Call(b"", 1, storage)

    for _ in range(16):
        block = rng.randrange(1, 2**40)
        number = rng.randrange(max(0, block - HISTORY_WINDOW), block)
        storage = {number % HISTORY_WINDOW: rng.randbytes(32)}
        yield Call(number.to_bytes(32, "big"), block, storage)
        future = rng.randrange(block, block + HISTORY_WINDOW)
        yield Call(future.to_bytes(32, "big"), block, storage)
        yield Call(rng.randbytes(rng.choice((1, 31, 33, 64))), block, storage)


def test_deployment_input_holds_the_runtime() -> None:
    """The constructor prefix and the runtime length match the deployment input."""
    assert HISTORY_DEPLOYMENT.startswith(CONSTRUCTOR)
    assert len(HISTORY_CODE) == 0x53


def test_history_lookup() -> None:
    """An ordinary caller gets the stored hash inside the window and a revert elsewhere."""
    check_bytecode(HISTORY_CODE, _cases, _lookup, seed=0x2935, to=HISTORY_ADDRESS)
