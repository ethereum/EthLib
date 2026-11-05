"""The checks of a transaction against its block and the state, on the release blockchain tests."""

import json
import re
from pathlib import Path

import pytest

from ethlib.execution import fees, transactions
from ethlib.serialization import rlp

from .test_settlement_archive import _address, _int, _price, _raw_transactions, runs_no_code
from .test_transactions import CHAIN_ID, FORK_OF_NETWORK, names

ARCHIVE = "execution-specs/tests@v21.0.2/fixtures"

_ROOT = "fixtures/blockchain_tests"
_FORKS = ["frontier", "homestead", "tangerinewhistle", "spuriousdragon", "byzantium",
          "constantinoplefix", "istanbul", "berlin", "london", "paris", "shanghai", "cancun",
          "prague", "osaka"]
SOURCES = [
    *(f"{_ROOT}/for_{fork}/frontier/validation" for fork in _FORKS),
    f"{_ROOT}/for_london/london/eip1559_fee_market_change",
    *(f"{_ROOT}/for_{fork}/ported_static/{test}" for fork in ("cancun", "prague", "osaka")
      for test in ("stEIP3607", "stTransactionTest")),
    *(f"{_ROOT}/for_{fork}/cancun/eip4844_blobs/blob_txs" for fork in ("cancun", "osaka")),
    f"{_ROOT}/for_prague/prague/eip7623_increase_calldata_cost/transaction_validity",
    f"{_ROOT}/for_prague/prague/eip7702_set_code_tx",
    f"{_ROOT}/for_osaka/osaka/eip7825_transaction_gas_limit_cap",
]

pytestmark = pytest.mark.archive(ARCHIVE, *SOURCES)

# The error of each fixture exception that the checks against the block and the state raise.
#
# The exceptions of a transaction alone keep the rules of the transaction tests.
_RULES = {
    "GAS_ALLOWANCE_EXCEEDED": r"gasAllowanceExceeded",
    "INSUFFICIENT_ACCOUNT_FUNDS": r"insufficientBalance",
    "NONCE_MISMATCH_TOO_HIGH": r"nonceTooHigh",
    "NONCE_MISMATCH_TOO_LOW": r"nonceTooLow",
    "NONCE_IS_MAX": r"nonceOverflow",
    "SENDER_NOT_EOA": r"senderNotEoa",
    "INSUFFICIENT_MAX_FEE_PER_GAS": r"insufficientMaxFeePerGas",
    "INSUFFICIENT_MAX_FEE_PER_BLOB_GAS": r"insufficientMaxFeePerBlobGas",
    "TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED": r"blobGasLimitExceeded",
    "TYPE_3_TX_BLOB_COUNT_EXCEEDED": r"blobCountExceeded",
    "TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH": r"invalidBlobVersionedHash",
    "TYPE_3_TX_ZERO_BLOBS": r"noBlobData",
    "INTRINSIC_GAS_TOO_LOW": r"insufficientGas",
    "INTRINSIC_GAS_BELOW_FLOOR_GAS_COST": r"insufficientGas",
    "GAS_LIMIT_EXCEEDS_MAXIMUM": r"gasLimitExceeded",
    "PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS": r"priorityFeeGreaterThanMaxFee",
    # A type 3 or type 4 transaction without a recipient does not decode.
    "TYPE_3_TX_CONTRACT_CREATION": r"decoding: ",
    "TYPE_4_TX_CONTRACT_CREATION": r"decoding: ",
}


def _names(exception: str, message: str) -> bool:
    kind, _, name = exception.partition(".")
    if kind != "TransactionException":
        return False
    if name in _RULES:
        return re.search(_RULES[name], message) is not None
    return names(exception, message)


def _scalar(value: int) -> bytes:
    return value.to_bytes((value.bit_length() + 7) // 8, "big")


def _state(accounts: dict) -> bytes:
    """The state in the form of the state root export: address, nonce, balance, code, storage."""
    return rlp.encode([
        [address, _scalar(a["nonce"]), _scalar(a["balance"]), a["code"],
         [[_int(k).to_bytes(32, "big"), _scalar(_int(v))] for k, v in a["storage"].items()]]
        for address, a in accounts.items()])


def _accounts(fixture: dict) -> dict:
    return {_address(address): {"nonce": _int(a["nonce"]), "balance": _int(a["balance"]),
                                "code": _address(a["code"]), "storage": a["storage"]}
            for address, a in fixture["pre"].items()}


def _account(accounts: dict, address: bytes) -> dict:
    return accounts.setdefault(address, {"nonce": 0, "balance": 0, "code": b"", "storage": {}})


def _run_block(fixture: dict) -> tuple[int, str | None]:
    """Check the transactions of the first block in order, while none of them runs code.

    It returns the number of checked transactions and the message of the first rejection.
    """
    block = fixture["blocks"][0]
    # An invalid block keeps its fields under `rlp_decoded`.
    decoded = block.get("rlp_decoded", block)
    fork = FORK_OF_NETWORK[fixture["network"]]
    header = decoded["blockHeader"]
    coinbase = _address(header["coinbase"])
    base_fee = _int(header.get("baseFeePerGas", "0x0"))
    accounts = _accounts(fixture)
    raw = _raw_transactions(bytes.fromhex(block["rlp"].removeprefix("0x")))
    excess = _int(header.get("excessBlobGas", "0x0"))
    gas_used = blob_gas_used = 0
    for index, (tx, data) in enumerate(zip(decoded["transactions"], raw, strict=True)):
        try:
            included = transactions.check_in_block(
                fork, CHAIN_ID, data, _state(accounts), gas_limit=_int(header["gasLimit"]),
                gas_used=gas_used, blob_gas_used=blob_gas_used, base_fee=base_fee,
                excess_blob_gas=excess)
        except ValueError as error:
            return index, str(error)
        assert included.sender == _address(tx["sender"])
        assert included.gas_price == _price(tx, base_fee)
        if index + 1 == len(raw) or not runs_no_code(fixture, tx):
            # The next transactions, if any, read the state after a run of code.
            return index + 1, None
        # A transaction that runs no code leaves gas, nonces and balances that we can follow.
        gas = _int(tx["gasLimit"])
        settled = transactions.settle(fork, data, base_fee,
                                      gas - transactions.intrinsic_gas(fork, data), 0)
        gas_used += settled.gas_used
        blob_gas_used += included.blob_gas_used
        sender = _account(accounts, included.sender)
        sender["nonce"] += 1
        sender["balance"] += settled.sender_refund - gas * included.gas_price - _int(tx["value"])
        if included.blob_gas_used:
            sender["balance"] -= fees.calculate_data_fee(fork, excess, data)
        _account(accounts, _address(tx["to"]))["balance"] += _int(tx["value"])
        _account(accounts, coinbase)["balance"] += settled.priority_fee
    return len(raw), None


def _files(archive: Path, source: str) -> list[Path]:
    return sorted((archive / source).rglob("*.json"))


@pytest.mark.parametrize("source", SOURCES, ids=lambda s: s.removeprefix(f"{_ROOT}/"))
def test_inclusion(archive, source) -> None:
    rejected = accepted = 0
    for path in _files(archive, source):
        for name, fixture in json.loads(path.read_text()).items():
            if fixture["network"] not in FORK_OF_NETWORK:
                continue
            block = fixture["blocks"][0]
            expected = block.get("expectException")
            if "rlp_decoded" not in block and "blockHeader" not in block:
                # The block itself does not decode, so no transaction reaches the checks.
                assert "BlockException.RLP_STRUCTURES_ENCODING" in expected.split("|")
                continue
            checked, error = _run_block(fixture)
            if error is not None:
                # The first rejection is the exception of the fixture.
                assert expected, (name, error)
                assert any(_names(e, error) for e in expected.split("|")), (name, expected, error)
                rejected += 1
            elif checked == len(block.get("rlp_decoded", block)["transactions"]) and expected:
                # Every transaction passes, so the block fails for a reason of its own.
                assert any(e.startswith("BlockException.") for e in expected.split("|")), \
                    (name, expected)
                accepted += 1
            else:
                accepted += 1
    assert rejected + accepted > 0
