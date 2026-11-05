"""The receipts of each block of the release blockchain tests, made from its results."""

import json
from pathlib import Path

import pytest

from ethlib.execution import blocks
from ethlib.serialization import rlp

from transactions.test_transactions import FORK_OF_NETWORK

ARCHIVE = "execution-specs/tests@v21.0.2/fixtures"

_ROOT = "fixtures/blockchain_tests"
_FORKS = [
    "frontier",
    "homestead",
    "tangerinewhistle",
    "spuriousdragon",
    "byzantium",
    "constantinoplefix",
    "istanbul",
    "berlin",
    "london",
    "paris",
    "shanghai",
    "cancun",
    "prague",
    "osaka",
]

# Logs before and after Byzantium, failed transactions, and every transaction type.
SOURCES = [
    *(f"{_ROOT}/for_{fork}/frontier/opcodes" for fork in _FORKS),
    f"{_ROOT}/for_berlin/berlin",
    f"{_ROOT}/for_london/london",
    *(f"{_ROOT}/for_cancun/ported_static/{test}" for test in ("stLogTests", "stRevertTest")),
    f"{_ROOT}/for_cancun/cancun/eip4844_blobs/blob_txs",
    f"{_ROOT}/for_prague/prague/eip7702_set_code_tx",
]

pytestmark = pytest.mark.archive(ARCHIVE, *SOURCES)


def _bytes(value: str) -> bytes:
    return bytes.fromhex(value.removeprefix("0x"))


def _scalar(value: int) -> bytes:
    return value.to_bytes((value.bit_length() + 7) // 8, "big")


def _log(log: dict) -> list:
    return [_bytes(log["address"]), [_bytes(t) for t in log["topics"]], _bytes(log["data"])]


def _results(receipts: list[dict]) -> bytes:
    """The results of the transactions: type, outcome, gas used, logs.

    The gas used is the step of the cumulative gas of the receipts.
    """
    results, cumulative = [], 0
    for receipt in receipts:
        if "postState" in receipt:
            outcome = _bytes(receipt["postState"])
        else:
            outcome = b"\x01" if receipt["status"] else b""
        gas = int(receipt["cumulativeGasUsed"], 16)
        results.append(
            [
                _scalar(int(receipt["type"], 16)),
                outcome,
                _scalar(gas - cumulative),
                [_log(log) for log in receipt["logs"]],
            ]
        )
        cumulative = gas
    return rlp.encode(results)


def _files(archive: Path, source: str) -> list[Path]:
    return sorted((archive / source).rglob("*.json"))


@pytest.mark.parametrize("source", SOURCES, ids=lambda s: s.removeprefix(f"{_ROOT}/"))
def test_make_receipts(archive, source) -> None:
    made = 0
    for path in _files(archive, source):
        for fixture in json.loads(path.read_text()).values():
            if fixture["network"] not in FORK_OF_NETWORK:
                continue
            fork = FORK_OF_NETWORK[fixture["network"]]
            for block in fixture["blocks"]:
                if "receipts" not in block:
                    continue
                root, receipts = blocks.make_receipts(fork, _results(block["receipts"]))
                # The receipts are those of the release, and so is the root of the header.
                assert receipts == [_bytes(r["rlp"]) for r in block["receipts"]]
                assert root == _bytes(block["blockHeader"]["receiptTrie"])
                made += len(receipts)
    assert made > 0
