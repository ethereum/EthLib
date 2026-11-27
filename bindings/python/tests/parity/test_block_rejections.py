"""The rejection reasons the parity runners require for malformed blocks and missing parents."""

import json
from pathlib import Path

import pytest

from ethlib.cryptography.keccak import keccak256
from ethlib.serialization import rlp
from parity import legacy, runners
from parity.catalogue import Case
from raising import raises

# An empty list has none of the three parts a Frontier block must hold.
EMPTY_BLOCK = "0xc0"
ENCODING_ERROR = "block invalid: encoding (EthLib.Serialization.Rlp.RlpError.wrongFieldCount 3 0)"


@pytest.fixture
def chain_fixture() -> dict:
    """A Frontier chain with an empty genesis state."""
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
        "lastblockhash": "0x" + keccak256(rlp.encode(rlp.decode(genesis)[0])).hex(),
    }


def _write_fixture(root: Path, fixture: dict, entry: dict, suite: str) -> Case:
    (root / "chain.json").write_text(json.dumps({"chain": {**fixture, "blocks": [entry]}}))
    return Case(suite, "", "Frontier", "blockchain_test", "chain", "chain.json")


@pytest.mark.parametrize("matches", [True, False])
def test_legacy_malformed_block_checks_its_reason(tmp_path, chain_fixture, matches) -> None:
    expected = "RLP_ExpectedAsList" if matches else "InvalidStateRoot"
    case = _write_fixture(
        tmp_path,
        chain_fixture,
        {"rlp": EMPTY_BLOCK, "expectException": expected},
        "legacytests",
    )
    if matches:
        legacy.run_blockchain(tmp_path, case)
    else:
        with raises(AssertionError, str((expected, ENCODING_ERROR))):
            legacy.run_blockchain(tmp_path, case)


@pytest.mark.parametrize("matches", [True, False])
def test_execution_malformed_block_checks_its_reason(tmp_path, chain_fixture, matches) -> None:
    expected = "BlockException." + (
        "RLP_STRUCTURES_ENCODING" if matches else "INVALID_WITHDRAWALS_ROOT"
    )
    case = _write_fixture(
        tmp_path,
        chain_fixture,
        {"rlp": EMPTY_BLOCK, "expectException": expected},
        "execution-spec-tests",
    )
    run = runners.FORMAT_RUNNERS["blockchain_test"]
    if matches:
        run(tmp_path, case)
    else:
        with raises(AssertionError, str(([expected], ENCODING_ERROR))):
            run(tmp_path, case)


@pytest.mark.parametrize("expected", ["UnknownParent", "InvalidStateRoot"])
def test_legacy_missing_parent_checks_its_reason(tmp_path, chain_fixture, expected) -> None:
    header, txs, ommers = rlp.decode(bytes.fromhex(chain_fixture["genesisRLP"][2:]))
    header[0] = b"\x01" + bytes(31)
    header[8] = b"\x01"
    entry = {"rlp": "0x" + rlp.encode([header, txs, ommers]).hex(), "expectException": expected}
    case = _write_fixture(tmp_path, chain_fixture, entry, "legacytests")
    if expected == "UnknownParent":
        legacy.run_blockchain(tmp_path, case)
    else:
        with raises(AssertionError, str(entry)):
            legacy.run_blockchain(tmp_path, case)
