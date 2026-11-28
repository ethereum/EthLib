"""Two runs of a transaction that implementations pin and the official fixtures leave out."""

import json

import pytest

from ethlib.cryptography.keccak import keccak256
from ethlib.cryptography.secp256k1 import address, sign
from ethlib.execution import transactions
from ethlib.serialization import rlp

from .expected_errors import FORKS
from .test_set_code_nonce import KEY, OTHER, _int
from .test_typed import ENV

SENDER = address(KEY)


def _legacy(gas: int) -> bytes:
    """A signed legacy call of no value to the other account, at 10 wei per gas, before EIP-155."""
    fields = [b"", _int(10), _int(gas), OTHER, b"", b""]
    signature = sign(KEY, keccak256(rlp.encode(fields)))
    r, s, v = signature[:32], signature[32:64], signature[64]
    return rlp.encode(fields + [_int(27 + v), r.lstrip(b"\0"), s.lstrip(b"\0")])


def _state(*accounts: tuple[bytes, int, bytes]) -> bytes:
    """The sender with 1 ether, then each account by its address, balance and code."""
    entries = [[SENDER, b"", _int(10**18), b"", []]]
    entries += [[at, b"", _int(balance), code, []] for at, balance, code in accounts]
    return rlp.encode(entries)


# The init code of the CREATE2 case, at offsets 0 to 15.
#
# Sent with no value, it writes 1 at slot 0, then reverts.
# Sent with value, it jumps to offset 14 and stops, which deploys no code.
INIT = bytes.fromhex(
    # CALLVALUE, PUSH1 14, JUMPI.
    "34600e57"
    # PUSH1 1, PUSH1 0, SSTORE.
    "6001600055"
    # PUSH1 0, PUSH1 0, REVERT.
    "60006000fd"
    # JUMPDEST, STOP.
    "5b00"
)

# The creator stores the init code in memory, at offsets 16 to 31.
# It then runs CREATE2 twice with salt 0: with no value, then with 1 wei.
CREATOR = bytes.fromhex(
    # PUSH16 the init code, then PUSH1 0, MSTORE.
    "6f" + INIT.hex() + "600052"
    # The operands from the last popped: salt 0, size 16, offset 16, value 0, then CREATE2, POP.
    "6000601060106000f550"
    # The same with value 1, then CREATE2, STOP.
    "6000601060106001f500"
)

# The address of both creations, by EIP-1014.
CREATED = keccak256(b"\xff" + OTHER + bytes(32) + keccak256(INIT))[12:]

# The forks from Constantinople, which adds CREATE2 by EIP-1014.
CREATE2_FORKS = FORKS[FORKS.index("constantinople") :]


@pytest.mark.parametrize("fork", CREATE2_FORKS)
def test_create2_prefunded_reverted_then_repeated(fork: str) -> None:
    # The new address holds 5 wei before the transaction, and nothing else.
    state = _state((OTHER, 1, CREATOR), (CREATED, 5, b""))
    tx = _legacy(1_000_000)
    run = transactions.run(fork, 1, tx, state, ENV)
    assert run.succeeded
    # The first init code writes slot 0, then reverts, in the frame at depth 2.
    steps = [json.loads(line) for line in transactions.trace_eip3155(fork, 1, tx, state, ENV)[:-1]]
    ops = [step["op"] for step in steps if step["depth"] == 2 and "error" not in step]
    assert ops.index(0x55) < ops.index(0xFD)
    accounts = {entry[0]: entry for entry in run.accounts}
    # The first creation reverts, so its write to slot 0 goes with it.
    # The second creates the account with nonce 1, the old balance plus 1 wei, no code, no storage.
    assert accounts[CREATED] == (CREATED, 1, 6, b"", [])


# A contract that calls itself with all the gas it may forward, and sends no value.
#
# PUSH1 0 five times for the return area, the input and the value, then ADDRESS, GAS and CALL.
RECURSE = bytes.fromhex("60006000600060006000" + "305af1")

# The gas of the instructions before CALL: five PUSH1 at 3, ADDRESS and GAS at 2.
BEFORE_CALL = 5 * 3 + 2 + 2

# The access of an address already warm, by EIP-2929: the address of a frame is warm.
WARM_ACCESS = 100

# The gas limit of a transaction from Fusaka, by EIP-7825.
TX_GAS_CAP = 2**24

# The intrinsic gas of a call with no data.
TX_BASE = 21_000


def deepest_frame(gas: int) -> int:
    """The depth of the deepest frame of the recursion, from the gas of the first frame.

    A frame that lacks the gas of the instructions before CALL, or of CALL, fails there.
    Otherwise it forwards all but one 64th of the gas left after the price of CALL, by EIP-150.
    """
    depth = 1
    while gas >= BEFORE_CALL + WARM_ACCESS:
        left = gas - BEFORE_CALL - WARM_ACCESS
        gas = left - left // 64
        depth += 1
    return depth


# The forks of the cap of EIP-7825 with the prices of EIP-2929, from Fusaka to Glamsterdam.
# From Glamsterdam, the state gas of EIP-8037 changes the gas of a call.
DEPTH_FORKS = FORKS[FORKS.index("fusaka") : FORKS.index("glamsterdam")]


@pytest.mark.parametrize("fork", DEPTH_FORKS)
def test_recursion_ends_before_the_depth_limit(fork: str) -> None:
    lines = transactions.trace_eip3155(
        fork, 1, _legacy(TX_GAS_CAP), _state((OTHER, 0, RECURSE)), ENV
    )
    *steps, summary = (json.loads(line) for line in lines)
    expected = deepest_frame(TX_GAS_CAP - TX_BASE)
    # The limit of 1024 frames is far: the gas runs out at depth 491.
    assert expected == 491
    assert max(step["depth"] for step in steps) == expected
    # The deepest frame fails, and each caller goes on, so the transaction succeeds.
    assert summary["pass"]
