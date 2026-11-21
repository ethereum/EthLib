"""The trace of a transaction in the lines of EIP-3155."""

import json

from ethlib.cryptography.keccak import keccak256
from ethlib.cryptography.secp256k1 import address, sign
from ethlib.execution import transactions
from ethlib.serialization import rlp
from raising import raises

from .test_check_order import KEY, OTHER, _fee_market, _int
from .test_typed import ENV

# The sender holds 1 ether, and the account it calls runs PUSH1 0x40.
STATE = rlp.encode(
    [[address(KEY), b"", _int(10**18), b"", []], [OTHER, b"", b"", bytes.fromhex("6040"), []]]
)

# A transfer of 1 wei with a gas limit of 100000, so the frame starts with 79000 gas.
TX = _fee_market(1, 100_000)

NONCE_TOO_HIGH = 206


def _nonce_one() -> bytes:
    """The transfer of the trace, with nonce 1 where the sender has nonce 0."""
    fields = [_int(1), _int(1), _int(1), _int(10), _int(100_000), OTHER, _int(1), b"", []]
    signature = sign(KEY, keccak256(b"\x02" + rlp.encode(fields)))
    r, s, v = signature[:32], signature[32:64], signature[64]
    return b"\x02" + rlp.encode(fields + [_int(v), r.lstrip(b"\0"), s.lstrip(b"\0")])


def test_push_then_stop() -> None:
    """PUSH1 gives one line, the STOP past the end of the code another, then the summary."""
    lines = transactions.trace_eip3155("pectra", 1, TX, STATE, ENV)
    run = transactions.run("pectra", 1, TX, STATE, ENV)
    assert lines == [
        '{"pc":0,"op":96,"gas":"0x13498","gasCost":"0x3","memSize":0,"stack":[],"depth":1,'
        '"returnData":"0x","refund":0,"opName":"PUSH1"}',
        '{"pc":2,"op":0,"gas":"0x13495","gasCost":"0x0","memSize":0,"stack":["0x40"],"depth":1,'
        '"returnData":"0x","refund":0,"opName":"STOP"}',
        '{"stateRoot":"0x'
        + run.state_root.hex()
        + '","output":"0x","gasUsed":"'
        + hex(run.gas_used)
        + '","pass":true,"fork":"pectra"}',
    ]


def test_lines_are_json() -> None:
    """Each line is one JSON object, and the summary reports the success."""
    lines = transactions.trace_eip3155("pectra", 1, TX, STATE, ENV)
    objects = [json.loads(line) for line in lines]
    keys = ["pc", "op", "gas", "gasCost", "memSize", "stack", "depth", "returnData", "refund"]
    assert [list(o) for o in objects[:-1]] == [[*keys, "opName"]] * 2
    assert list(objects[-1]) == ["stateRoot", "output", "gasUsed", "pass", "fork"]
    assert objects[-1]["pass"] is True


def test_nonce_too_high_refused() -> None:
    """A transaction that may not enter the block gets no trace, but the error of the block."""
    with raises(transactions.TransactionError, "nonceTooHigh (expected := 0) (nonce := 1)") as e:
        transactions.trace_eip3155("pectra", 1, _nonce_one(), STATE, ENV)
    assert e.value.code == NONCE_TOO_HIGH


def test_transfer_has_only_summary() -> None:
    """A transfer to an account without code runs no step, so only the summary remains."""
    tx = _fee_market(1, 21_000)
    plain = rlp.encode([[address(KEY), b"", _int(10**18), b"", []]])
    lines = transactions.trace_eip3155("pectra", 1, tx, plain, ENV)
    assert len(lines) == 1
    assert json.loads(lines[0])["gasUsed"] == hex(21_000)
