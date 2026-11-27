"""Compare EVM bytecode with a Python reference on seeded inputs."""

import json
from collections.abc import Callable, Iterable, Mapping
from random import Random
from types import MappingProxyType
from typing import Literal, NamedTuple

from ethlib.execution import transactions
from ethlib.serialization import rlp

from .test_amsterdam import CHAIN_ID, OTHER, SENDER, _fee_market, _int


class Call(NamedTuple):
    """The calldata, block number and initial storage of a call, whose values are 32-byte words."""

    calldata: bytes
    block_number: int = 1
    storage: Mapping[int, bytes] = MappingProxyType({})


class Outcome(NamedTuple):
    """The top-level execution status and return bytes, including revert data."""

    status: Literal["success", "revert", "failure"]
    output: bytes


def run_bytecode(code: bytes, call: Call, *, fork: str = "pectra", to: bytes = OTHER) -> Outcome:
    """Run the given runtime code in a fresh state with a zero-value transaction.

    The fork must support type 2 transactions.
    Use a 20-byte destination outside the fork's precompiles and distinct from the sender.
    """
    storage = [
        [slot.to_bytes(32, "big"), value.lstrip(b"\0")] for slot, value in call.storage.items()
    ]
    state = rlp.encode([[SENDER, b"", _int(10**18), b"", []], [to, b"\x01", b"", code, storage]])
    # The block environment, in the order of the fields that the transaction export reads.
    env = rlp.encode(
        [
            # Coinbase.
            bytes(20),
            # Gas limit.
            _int(30_000_000),
            # Number.
            _int(call.block_number),
            # Timestamp.
            b"\x01",
            # Difficulty.
            b"",
            # Base fee.
            b"\x01",
            # Previous RANDAO mix.
            bytes(32),
            # Excess blob gas.
            b"",
            # Block hashes.
            [],
            # Slot number.
            b"",
        ]
    )
    tx = _fee_market(to, data=call.calldata)
    *steps, summary_line = transactions.trace_eip3155(fork, CHAIN_ID, tx, state, env)
    summary = json.loads(summary_line)
    output = bytes.fromhex(summary["output"][2:])
    if summary["pass"]:
        return Outcome("success", output)
    # A normal REVERT has no step error and the top-level frame has depth one.
    last_step = json.loads(steps[-1]) if steps else {}
    if (
        last_step.get("opName") == "REVERT"
        and last_step.get("depth") == 1
        and "error" not in last_step
    ):
        return Outcome("revert", output)
    return Outcome("failure", output)


def check_bytecode(
    code: bytes,
    cases: Callable[[Random], Iterable[Call]],
    reference: Callable[[Call], Outcome],
    *,
    seed: int,
    fork: str = "pectra",
    to: bytes = OTHER,
) -> None:
    """Check the generated calls and report the seed and input of the first mismatch."""
    for index, call in enumerate(cases(Random(seed))):
        expected = reference(call)
        actual = run_bytecode(code, call, fork=fork, to=to)
        assert actual == expected, (
            f"EVM mismatch for seed {seed:#x}, case {index}\n"
            f"Input {call!r}\nExpected {expected!r}\nActual {actual!r}"
        )
