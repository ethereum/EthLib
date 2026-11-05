"""Receipts and the logs Bloom filter against the blockchain tests of execution-specs."""

import json
from pathlib import Path

import pytest

from ethlib.execution import blocks
from raising import raises

from .test_blocks import FORK_OF_NETWORK

_REPO = Path(__file__).resolve().parents[4]
_CASES_FILE = _REPO / "tests" / "execution" / "blocks" / "receipts.json"
CASES = json.loads(_CASES_FILE.read_text())


def _case_id(case) -> str:
    return f"{case['network']}-type{case['type']}-logs{case['logs']}-{case['test'][-40:]}"


@pytest.mark.parametrize("case", CASES, ids=[_case_id(c) for c in CASES])
def test_fixture_receipt(case) -> None:
    fork = FORK_OF_NETWORK[case["network"]]
    receipt = bytes.fromhex(case["rlp"])
    # The decoder accepts the receipt, and its encoding gives back the same bytes.
    assert blocks.receipt_reencode(fork, receipt) == receipt
    # The filter of its logs is the filter of the fixture.
    assert blocks.receipt_logs_bloom(fork, receipt) == bytes.fromhex(case["bloom"])


def _first(network: str, type_: str) -> bytes:
    case = next(c for c in CASES if c["network"] == network and c["type"] == type_)
    return bytes.fromhex(case["rlp"])


def test_typed_receipt_rejected_before_its_fork() -> None:
    # Type 4 transactions start at Pectra, so Dencun has no such receipt.
    with raises(
        ValueError, "receipt rejected: EthLib.Execution.Blocks.ReceiptError.unsupportedType 4"
    ):
        blocks.receipt_reencode("dencun", _first("Amsterdam", "0x04"))


def test_state_root_receipt_rejected_from_byzantium() -> None:
    # From Byzantium the outcome is a status, and a 32-byte state root is no status.
    with raises(
        ValueError,
        (
            "receipt rejected: EthLib.Execution.Blocks.ReceiptError.decoding\n  "
            "(EthLib.Serialization.Rlp.RlpError.inField\n    0\n    "
            "(EthLib.Serialization.Rlp.RlpError.scalarTooLarge\n      "
            "36275914291122208996321553314393517492983287139762320008492702682652323682353\n      "
            "1))"
        ),
    ):
        blocks.receipt_reencode("byzantium", _first("Frontier", "0x00"))


def test_status_receipt_rejected_before_byzantium() -> None:
    # Before Byzantium the outcome is a 32-byte state root, and a status is no root.
    with raises(
        ValueError,
        (
            "receipt rejected: EthLib.Execution.Blocks.ReceiptError.decoding\n  "
            "(EthLib.Serialization.Rlp.RlpError.inField 0 "
            "(EthLib.Serialization.Rlp.RlpError.wrongLength 32 1))"
        ),
    ):
        blocks.receipt_reencode("frontier", _first("Byzantium", "0x00"))


def test_empty_receipt_rejected() -> None:
    with raises(ValueError, "receipt rejected: EthLib.Execution.Blocks.ReceiptError.emptyReceipt"):
        blocks.receipt_reencode("fusaka", b"")
