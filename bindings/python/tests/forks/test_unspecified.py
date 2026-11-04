"""Exports reject a fork whose rules EthLib does not hold yet."""

import json
from pathlib import Path

import pytest

from ethlib import consensus
from ethlib.errors import EthLibError
from ethlib.execution import blocks, fees, pow, transactions
from ethlib.networking import enr
from ethlib.precompiles import price, run
from ethlib.serialization import rlp
from ethlib.state import withdrawals_root

_REPO = Path(__file__).resolve().parents[4]
_FILE = _REPO / "tests" / "execution" / "blocks" / "blockchain_tests.json"
_CASES = json.loads(_FILE.read_text())

# The first Amsterdam block of the fixtures after a genesis block, and its header.
AMSTERDAM_BLOCK = next(
    bytes.fromhex(c["rlp"]) for c in _CASES if c["network"] == "Amsterdam" and c["block"] == 0)
HEADER = rlp.encode(rlp.decode(AMSTERDAM_BLOCK)[0])

# The first typed transaction of a Prague block, a form that Amsterdam keeps.
TRANSACTION = next(
    t for c in _CASES if c["network"] == "Prague"
    for t in rlp.decode(bytes.fromhex(c["rlp"]))[1] if isinstance(t, bytes))

# The empty state, as the list of its accounts.
EMPTY_STATE = rlp.encode([])

# The identity precompile.
IDENTITY = 4

# Each export that takes a fork, called at that fork.
EXPORTS = {
    "tx_type": lambda f: transactions.tx_type(f, TRANSACTION),
    "tx_hash": lambda f: transactions.tx_hash(f, TRANSACTION),
    "recover_sender": lambda f: transactions.recover_sender(f, TRANSACTION),
    "intrinsic_gas": lambda f: transactions.intrinsic_gas(f, TRANSACTION),
    "check": lambda f: transactions.check(f, 1, TRANSACTION),
    "network_check": lambda f: transactions.network_check(f, TRANSACTION),
    "header_hash": lambda f: blocks.header_hash(f, HEADER),
    "reencode": lambda f: blocks.reencode(f, AMSTERDAM_BLOCK),
    "transactions_root": lambda f: blocks.transactions_root(f, AMSTERDAM_BLOCK),
    "withdrawals_root": lambda f: blocks.withdrawals_root(f, AMSTERDAM_BLOCK),
    "validate_header": lambda f: blocks.validate_header(f, f, HEADER, HEADER),
    "validate_size": lambda f: blocks.validate_size(f, AMSTERDAM_BLOCK),
    "receipt_reencode": lambda f: blocks.receipt_reencode(f, b""),
    "receipt_logs_bloom": lambda f: blocks.receipt_logs_bloom(f, b""),
    "state_withdrawals_root": lambda f: withdrawals_root(f, EMPTY_STATE, AMSTERDAM_BLOCK),
    "base_fee_per_blob_gas": lambda f: fees.get_base_fee_per_blob_gas(f, 0),
    "excess_blob_gas": lambda f: fees.calc_excess_blob_gas(f, 0, 0, 1),
    "block_difficulty": lambda f: pow.block_difficulty(f, 1, 1, 0, 1, 0),
    "seal_hash": lambda f: pow.seal_hash(f, HEADER),
    "check_proof_of_work": lambda f: pow.check_proof_of_work(f, HEADER),
    "precompile_run": lambda f: run(f, IDENTITY, b"", 10**6),
    "precompile_price": lambda f: price(f, IDENTITY, b""),
    "consensus_entries": lambda f: enr.consensus_entries(f, b""),
    "consensus_parameters": lambda f: consensus.parameters("mainnet", f),
    "ssz_static": lambda f: consensus.ssz_static("mainnet", f, "Checkpoint", bytes(40)),
}

# The exports whose rules hold at Glamsterdam: the forms of transactions, blocks and receipts,
# the checks of a header, the blob schedule, proof of work and the precompiles.
AT_GLAMSTERDAM = {
    "tx_type", "tx_hash", "recover_sender", "header_hash", "reencode", "transactions_root",
    "withdrawals_root", "validate_header", "validate_size", "receipt_reencode",
    "receipt_logs_bloom", "state_withdrawals_root", "base_fee_per_blob_gas", "excess_blob_gas",
    "block_difficulty", "seal_hash", "check_proof_of_work", "precompile_run", "precompile_price",
}


def _rejects(export: str, fork: str) -> None:
    with pytest.raises(EthLibError, match=f"^fork {fork} not yet specified$") as error:
        EXPORTS[export](fork)
    assert error.value.code == 0


@pytest.mark.parametrize("export", sorted(EXPORTS))
def test_hegota_is_not_yet_specified(export: str) -> None:
    _rejects(export, "hegota")


@pytest.mark.parametrize("export", sorted(set(EXPORTS) - AT_GLAMSTERDAM))
def test_glamsterdam_is_not_yet_specified(export: str) -> None:
    # Glamsterdam changes these rules, and EthLib does not hold the changes yet.
    _rejects(export, "glamsterdam")


@pytest.mark.parametrize("export", sorted(AT_GLAMSTERDAM))
def test_glamsterdam_passes_the_fork_check(export: str) -> None:
    # The export reads the fork, then may reject the input for another reason.
    try:
        EXPORTS[export]("glamsterdam")
    except EthLibError as error:
        assert "not yet specified" not in error.message


def test_glamsterdam_transaction_and_header() -> None:
    # The Amsterdam transaction and header of the fixture decode at Glamsterdam.
    assert transactions.tx_type("glamsterdam", TRANSACTION) == TRANSACTION[0]
    assert len(blocks.header_hash("glamsterdam", HEADER)) == 32
    assert blocks.reencode("glamsterdam", AMSTERDAM_BLOCK) == AMSTERDAM_BLOCK


def test_bpo2_is_specified() -> None:
    # The last fork whose rules EthLib holds in full passes the fork check of every export.
    for export in EXPORTS:
        try:
            EXPORTS[export]("bpo2")
        except EthLibError as error:
            assert "not yet specified" not in error.message
