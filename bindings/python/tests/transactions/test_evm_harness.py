"""Check seeded replay, EVM outcomes and mismatch reporting."""

from collections.abc import Iterator
from random import Random

import pytest

from raising import raises

from .evm_harness import Call, Outcome, check_bytecode, run_bytecode

# Copy calldata to memory and return those bytes.
ECHO = bytes.fromhex("365f5f37365ff3")


@pytest.mark.parametrize(
    ("code", "expected"),
    [
        pytest.param(ECHO, Outcome("success", b"hello"), id="return"),
        pytest.param(bytes.fromhex("5f5ffd"), Outcome("revert", b""), id="revert"),
        pytest.param(
            bytes.fromhex("365f5f37365ffd"), Outcome("revert", b"hello"), id="revert-data"
        ),
        pytest.param(b"\xfd", Outcome("failure", b""), id="revert-stack-underflow"),
        pytest.param(b"\xfe", Outcome("failure", b""), id="invalid-opcode"),
    ],
)
def test_outcome(code: bytes, expected: Outcome) -> None:
    assert run_bytecode(code, Call(b"hello")) == expected


def test_seed_replays_the_same_calls() -> None:
    seen: list[bytes] = []

    def cases(rng: Random) -> Iterator[Call]:
        for _ in range(3):
            yield Call(rng.randbytes(2))

    def reference(call: Call) -> Outcome:
        seen.append(call.calldata)
        return Outcome("success", call.calldata)

    check_bytecode(ECHO, cases, reference, seed=42)
    assert len(set(seen)) == 3
    check_bytecode(ECHO, cases, reference, seed=42)
    assert seen[:3] == seen[3:6]
    check_bytecode(ECHO, cases, reference, seed=43)
    assert seen[:3] != seen[6:]


def test_mismatch_reports_the_replay_input() -> None:
    call = Call(b"x")
    expected = Outcome("success", b"y")
    actual = Outcome("success", b"x")
    message = (
        f"EVM mismatch for seed 0x2a, case 0\n"
        f"Input {call!r}\nExpected {expected!r}\nActual {actual!r}"
    )
    with raises(AssertionError, message):
        check_bytecode(ECHO, lambda _: [call], lambda _: expected, seed=42)
