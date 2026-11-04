"""The vendored blocks and receipts against the release archive of execution-specs."""

import json
from functools import cache
from pathlib import Path

import pytest

ARCHIVE = "execution-specs/tests@v21.0.2/fixtures"

_CASES = Path(__file__).resolve().parents[4] / "tests" / "execution" / "blocks"
BLOCKS = json.loads((_CASES / "blockchain_tests.json").read_text())
RECEIPTS = json.loads((_CASES / "receipts.json").read_text())

_SOURCES = sorted({case["source"] for case in BLOCKS + RECEIPTS})

pytestmark = pytest.mark.archive(ARCHIVE, *_SOURCES)


@cache
def _fixture(root: Path, source: str, test: str) -> dict:
    return json.loads((root / source).read_text())[test]


def _hex(value: str) -> str:
    return value.removeprefix("0x")


@pytest.mark.parametrize("case", BLOCKS, ids=lambda c: f"{c['source']}-{c['block']}")
def test_block(archive, case) -> None:
    fixture = _fixture(archive, case["source"], case["test"])
    assert case["network"] == fixture["network"]
    if case["block"] == "genesis":
        rlp, header = fixture["genesisRLP"], fixture["genesisBlockHeader"]
    else:
        block = fixture["blocks"][case["block"]]
        rlp, header = block["rlp"], block["blockHeader"]
    # The block and its header hash are those of the release.
    assert case["rlp"] == _hex(rlp)
    assert case["hash"] == _hex(header["hash"])


@pytest.mark.parametrize(
    "case", RECEIPTS, ids=lambda c: f"{c['source']}-{c['block']}-{c['receipt']}")
def test_receipt(archive, case) -> None:
    fixture = _fixture(archive, case["source"], case["test"])
    assert case["network"] == fixture["network"]
    receipt = fixture["blocks"][case["block"]]["receipts"][case["receipt"]]
    # The receipt, its type, its number of logs and its Bloom filter are those of the release.
    assert case["rlp"] == _hex(receipt["rlp"])
    assert case["type"] == receipt["type"]
    assert case["logs"] == len(receipt["logs"])
    assert case["bloom"] == _hex(receipt["bloom"])
