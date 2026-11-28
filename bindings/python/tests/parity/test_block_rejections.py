"""The rejection reasons the parity runners require for malformed blocks and missing parents."""

import json
from pathlib import Path

import pytest

from ethlib.execution import blocks
from ethlib.serialization import rlp
from raising import raises

from . import legacy, runners
from .catalogue import Case

# Blocks that do not decode, one for each kind of failure, with the error of the state transition.
MALFORMED = [
    # An empty list has none of the three parts a Frontier block must hold.
    ("0xc0", "block invalid: encoding (EthLib.Serialization.Rlp.RlpError.wrongFieldCount 3 0)"),
    # A list whose prefix announces one byte more than the input holds.
    ("0xc1", "block invalid: encoding (EthLib.Serialization.Rlp.RlpError.inputTooShort 1 0)"),
    # A header that is a string of 12 bytes, not a list.
    (
        "0xcf8c" + "30" * 12 + "c0c0",
        "block invalid: encoding (EthLib.Serialization.Rlp.RlpError.inField 0 "
        "(EthLib.Serialization.Rlp.RlpError.bytesAsList))",
    ),
    # An empty header, so the error names the 15 fields of a Frontier header.
    (
        "0xc3c0c0c0",
        "block invalid: encoding (EthLib.Serialization.Rlp.RlpError.inField 0 "
        "(EthLib.Serialization.Rlp.RlpError.wrongFieldCount 15 0))",
    ),
]

# The error of a block that decodes but has the timestamp of the genesis block.
OTHER_REASON = "block invalid: timestampNotAfterParent (timestamp := 0) (parentTimestamp := 0)"

LEGACY_ENCODING = "RLP_ExpectedAsList"
EXECUTION_ENCODING = "BlockException.RLP_STRUCTURES_ENCODING"


@pytest.fixture
def chain_fixture() -> dict:
    """A Frontier chain with an empty genesis state, no blocks, and the genesis as last block."""
    header = {
        "coinbase": "0x" + "00" * 20,
        "difficulty": "0x20000",
        "gasLimit": "0x1c9c380",
        "extraData": "0x",
        "mixHash": "0x" + "00" * 32,
        "nonce": "0x" + "00" * 8,
    }
    genesis = runners.genesis_of("frontier", header, {})
    return {
        "network": "Frontier",
        "config": {"chainid": "0x1"},
        "pre": {},
        "genesisRLP": "0x" + genesis.hex(),
        "genesisBlockHeader": header,
        "lastblockhash": "0x"
        + blocks.header_hash("frontier", rlp.encode(rlp.decode(genesis)[0])).hex(),
    }


def _write_fixture(root: Path, fixture: dict, entry: dict, suite: str, group: str) -> Case:
    (root / "chain.json").write_text(json.dumps({"chain": {**fixture, "blocks": [entry]}}))
    return Case(suite, "", "Frontier", group, "chain", "chain.json")


def _run_legacy(root: Path, fixture: dict, entry: dict) -> None:
    legacy.run_blockchain(
        root, _write_fixture(root, fixture, entry, "legacytests", "legacy_blockchain")
    )


def _run_execution(root: Path, fixture: dict, entry: dict) -> None:
    case = _write_fixture(root, fixture, entry, "execution-spec-tests", "blockchain_test")
    runners.FORMAT_RUNNERS["blockchain_test"](root, case)


def _child(fixture: dict, parent_hash: bytes) -> str:
    """A block at number 1 on the parent, with the timestamp and the fields of the genesis block."""
    header, transactions, ommers = rlp.decode(bytes.fromhex(fixture["genesisRLP"][2:]))
    header[runners.HEADER_FIELDS.index("parentHash")] = parent_hash
    header[runners.HEADER_FIELDS.index("number")] = b"\x01"
    return "0x" + rlp.encode([header, transactions, ommers]).hex()


def _genesis_child(fixture: dict) -> str:
    return _child(fixture, bytes.fromhex(fixture["lastblockhash"][2:]))


def _orphan(fixture: dict) -> str:
    return _child(fixture, b"\x01" + bytes(31))


@pytest.mark.parametrize("block", [block for block, _ in MALFORMED])
def test_legacy_malformed_block_passes_with_its_reason(tmp_path, chain_fixture, block) -> None:
    _run_legacy(tmp_path, chain_fixture, {"rlp": block, "expectException": LEGACY_ENCODING})


@pytest.mark.parametrize(("block", "message"), MALFORMED)
def test_legacy_malformed_block_fails_with_another_reason(
    tmp_path, chain_fixture, block, message
) -> None:
    expected = "InvalidStateRoot"
    with raises(AssertionError, str((expected, message))):
        _run_legacy(tmp_path, chain_fixture, {"rlp": block, "expectException": expected})


def test_legacy_encoding_reason_fails_on_another_rejection(tmp_path, chain_fixture) -> None:
    entry = {"rlp": _genesis_child(chain_fixture), "expectException": LEGACY_ENCODING}
    with raises(AssertionError, str((LEGACY_ENCODING, OTHER_REASON))):
        _run_legacy(tmp_path, chain_fixture, entry)


@pytest.mark.parametrize("block", [block for block, _ in MALFORMED])
def test_execution_malformed_block_passes_with_its_reason(tmp_path, chain_fixture, block) -> None:
    _run_execution(tmp_path, chain_fixture, {"rlp": block, "expectException": EXECUTION_ENCODING})


@pytest.mark.parametrize(("block", "message"), MALFORMED)
def test_execution_malformed_block_fails_with_another_reason(
    tmp_path, chain_fixture, block, message
) -> None:
    expected = "BlockException.INVALID_WITHDRAWALS_ROOT"
    with raises(AssertionError, str(([expected], message))):
        _run_execution(tmp_path, chain_fixture, {"rlp": block, "expectException": expected})


def test_execution_encoding_reason_fails_on_another_rejection(tmp_path, chain_fixture) -> None:
    entry = {"rlp": _genesis_child(chain_fixture), "expectException": EXECUTION_ENCODING}
    with raises(AssertionError, str(([EXECUTION_ENCODING], OTHER_REASON))):
        _run_execution(tmp_path, chain_fixture, entry)


@pytest.mark.parametrize("run", [_run_legacy, _run_execution])
def test_malformed_block_must_expect_an_exception(tmp_path, chain_fixture, run) -> None:
    entry = {"rlp": MALFORMED[0][0]}
    with raises(AssertionError, str(entry)):
        run(tmp_path, chain_fixture, entry)


@pytest.mark.parametrize("expected", ["UnknownParent", "InvalidStateRoot|UnknownParent2"])
def test_legacy_missing_parent_passes_with_its_reason(tmp_path, chain_fixture, expected) -> None:
    _run_legacy(
        tmp_path, chain_fixture, {"rlp": _orphan(chain_fixture), "expectException": expected}
    )


def test_legacy_missing_parent_fails_with_another_reason(tmp_path, chain_fixture) -> None:
    entry = {"rlp": _orphan(chain_fixture), "expectException": "InvalidStateRoot"}
    with raises(AssertionError, str(entry)):
        _run_legacy(tmp_path, chain_fixture, entry)
