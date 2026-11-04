"""The settlement of the gas against the blockchain tests of the release archive."""

import json
from pathlib import Path

import pytest

from ethlib.execution import fees, transactions
from ethlib.serialization import rlp

from .test_transactions import FORK_OF_NETWORK

ARCHIVE = "execution-specs/tests@v21.0.2/fixtures"

# A block qualifies when no transaction runs code, so the gas left is the gas limit minus the
# intrinsic gas, and the refund counter is 0.
#
# These directories hold such blocks: plain transfers, the call data floor of EIP-7623, and the
# blob fees of EIP-4844.
_ROOT = "fixtures/blockchain_tests"
_EARLY = ["frontier", "homestead", "tangerinewhistle", "spuriousdragon", "byzantium",
          "constantinoplefix", "istanbul", "berlin", "london", "paris", "shanghai"]
SOURCES = [
    *(f"{_ROOT}/for_{fork}/frontier/{test}" for fork in _EARLY
      for test in ("validation", "eip2681_limit_account_nonce")),
    *(f"{_ROOT}/for_{fork}/frontier/validation" for fork in ("cancun", "prague", "osaka")),
    *(f"{_ROOT}/for_{fork}/ported_static/stTransactionTest" for fork in ("cancun", "prague")),
    *(f"{_ROOT}/for_{fork}/cancun/eip4844_blobs" for fork in ("cancun", "prague", "osaka")),
    *(f"{_ROOT}/for_{fork}/prague/eip7623_increase_calldata_cost" for fork in ("prague", "osaka")),
]

pytestmark = pytest.mark.archive(ARCHIVE, *SOURCES)

# The precompiles up to Osaka, which run code without having any.
_PRECOMPILES = {i.to_bytes(20, "big") for i in [*range(1, 0x12), 0x100]}

# The block reward in wei before Paris, which the beneficiary also receives.
#
# It is 5 ether in the Yellow Paper, 3 from Byzantium by EIP-649, and 2 from Constantinople by
# EIP-1234.
# EIP-3675 ends it at Paris.
_REWARD = {
    "Frontier": 5, "Homestead": 5, "TangerineWhistle": 5, "SpuriousDragon": 5, "Byzantium": 3,
    "ConstantinopleFix": 2, "Istanbul": 2, "Berlin": 2, "London": 2,
}


def _int(value: str) -> int:
    return int(value, 16)


def _address(value: str) -> bytes:
    return bytes.fromhex(value.removeprefix("0x"))


def _plain(fixture: dict, block: dict) -> bool:
    """Whether a valid block of one block has transactions, and none of them runs code."""
    if "expectException" in block or not block["transactions"]:
        return False
    code = {_address(a): account["code"] for a, account in fixture["pre"].items()}
    for tx in block["transactions"]:
        to = _address(tx.get("to") or "0x")
        if not to or _int(tx["type"]) == 4 or to in _PRECOMPILES:
            return False
        if code.get(to, "0x") not in ("", "0x"):
            return False
    return True


def _price(tx: dict, base_fee: int) -> int:
    """The price per gas of EIP-1559: the gas price, or the base fee plus the capped tip."""
    if "gasPrice" in tx:
        return _int(tx["gasPrice"])
    max_fee = _int(tx["maxFeePerGas"])
    return min(_int(tx["maxPriorityFeePerGas"]), max_fee - base_fee) + base_fee


def _raw_transactions(block: bytes) -> list[bytes]:
    """The bytes of each transaction of a block: a typed one as is, a legacy one encoded."""
    return [t if isinstance(t, bytes) else rlp.encode(t) for t in rlp.decode(block)[1]]


def _check_block(fixture: dict) -> int:
    block = fixture["blocks"][0]
    network = fixture["network"]
    fork = FORK_OF_NETWORK[network]
    header = block["blockHeader"]
    coinbase = _address(header["coinbase"])
    base_fee = _int(header.get("baseFeePerGas", "0x0"))
    excess = _int(header.get("excessBlobGas", "0x0"))
    balances = {_address(a): _int(account["balance"]) for a, account in fixture["pre"].items()}
    cumulative = 0
    raw = _raw_transactions(bytes.fromhex(block["rlp"].removeprefix("0x")))
    for tx, data, receipt in zip(block["transactions"], raw, block["receipts"], strict=True):
        gas = _int(tx["gasLimit"])
        gas_left = gas - transactions.intrinsic_gas(fork, data)
        settled = transactions.settle(fork, data, base_fee, gas_left, 0)
        # The gas used is the step of the cumulative gas of the receipts.
        assert settled.gas_used == _int(receipt["cumulativeGasUsed"]) - cumulative
        cumulative += settled.gas_used
        # The wei of the gas limit split exactly, at the price of EIP-1559.
        price = _price(tx, base_fee)
        assert settled.sender_refund + settled.priority_fee + settled.burned == gas * price
        assert settled.burned == settled.gas_used * base_fee
        sender, to = _address(tx["sender"]), _address(tx["to"])
        blob_fee = fees.calculate_data_fee(fork, excess, data) if _int(tx["type"]) == 3 else 0
        value = _int(tx["value"])
        balances[sender] = balances.get(sender, 0) - gas * price - blob_fee - value
        balances[to] = balances.get(to, 0) + value
        balances[sender] += settled.sender_refund
        balances[coinbase] = balances.get(coinbase, 0) + settled.priority_fee
    assert cumulative == _int(header["gasUsed"])
    # No block here has an ommer, whose reward would change the beneficiary's balance.
    assert not block["uncleHeaders"]
    balances[coinbase] = balances.get(coinbase, 0) + _REWARD.get(network, 0) * 10 ** 18
    for withdrawal in block.get("withdrawals", []):
        address = _address(withdrawal["address"])
        balances[address] = balances.get(address, 0) + _int(withdrawal["amount"]) * 10 ** 9
    post = {_address(a): _int(account["balance"]) for a, account in fixture["postState"].items()}
    for address in {coinbase, *(_address(tx["sender"]) for tx in block["transactions"]),
                    *(_address(tx["to"]) for tx in block["transactions"])}:
        # An account that leaves the state holds nothing.
        assert post.get(address, 0) == balances.get(address, 0), address.hex()
    return len(block["transactions"])


def _files(archive: Path, source: str) -> list[Path]:
    return sorted((archive / source).rglob("*.json"))


@pytest.mark.parametrize("source", SOURCES, ids=lambda s: s.removeprefix(f"{_ROOT}/"))
def test_settlement(archive, source) -> None:
    checked = 0
    for path in _files(archive, source):
        for fixture in json.loads(path.read_text()).values():
            if fixture["network"] not in FORK_OF_NETWORK or len(fixture["blocks"]) != 1:
                continue
            if _plain(fixture, fixture["blocks"][0]):
                checked += _check_block(fixture)
    # Every directory holds at least one such block.
    assert checked > 0


def test_settle_rejects(archive) -> None:
    source = f"{_ROOT}/for_prague/prague/eip7623_increase_calldata_cost"
    fixture = next(iter(json.loads((archive / source / "eip_mainnet/eip_7623.json").read_text())
                        .values()))
    block = fixture["blocks"][0]
    tx = _raw_transactions(bytes.fromhex(block["rlp"].removeprefix("0x")))[0]
    gas, max_fee = _int(block["transactions"][0]["gasLimit"]), _price(block["transactions"][0], 0)
    # A maximum fee below the base fee, more gas left than the gas limit, and a base fee before
    # London are inputs that no block accepts.
    for fork, base_fee, gas_left in [("pectra", max_fee + 1, 0), ("pectra", 0, gas + 1),
                                     ("berlin", 1, 0)]:
        with pytest.raises(transactions.TransactionError) as error:
            transactions.settle(fork, tx, base_fee, gas_left, 0)
        assert error.value.code == 0
