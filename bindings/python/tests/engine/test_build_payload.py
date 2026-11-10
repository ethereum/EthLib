"""The payload build, against the first block of a blockchain test at each fork from Paris."""

import json

import pytest

import archives
from ethlib import engine
from ethlib.cryptography.keccak import keccak256
from ethlib.errors import EngineError
from ethlib.execution import blocks
from ethlib.serialization import rlp
from parity.runners import genesis_of, pre_state
from raising import raises

from .cases import FORK_OF_NETWORK, config

_BLOCKS = archives.REPO / "tests" / "execution" / "blocks"
GENESES = {case["network"]: case for case in json.loads((_BLOCKS / "genesis.json").read_text())}
VECTORS = json.loads((_BLOCKS / "blockchain_tests.json").read_text())

# The version of engine_forkchoiceUpdated that takes the attributes of each network.
METHODS = {
    "Paris": "engine_forkchoiceUpdatedV1",
    "Shanghai": "engine_forkchoiceUpdatedV2",
    "Cancun": "engine_forkchoiceUpdatedV3",
    "Prague": "engine_forkchoiceUpdatedV3",
    "Osaka": "engine_forkchoiceUpdatedV3",
    "Amsterdam": "engine_forkchoiceUpdatedV4",
}

# The positions of the fields of a header, in its RLP list.
COINBASE, NUMBER, GAS_LIMIT, TIMESTAMP, EXTRA_DATA, MIX_HASH = 2, 8, 9, 11, 12, 13
BEACON_ROOT, SLOT_NUMBER = 19, 22


def _quantity(raw: bytes) -> str:
    return hex(int.from_bytes(raw, "big"))


def _data(raw: bytes) -> str:
    return "0x" + raw.hex()


def _first_block(network: str) -> dict:
    """The first block after the genesis of the test that gives the genesis of the network."""
    test = GENESES[network]["test"]
    return next(v for v in VECTORS if v["test"] == test and v["block"] == 0)


def _chain(network: str) -> tuple[dict, bytes, list]:
    """The configuration, the state and the recent blocks of the genesis of a network."""
    genesis = GENESES[network]
    fork = FORK_OF_NETWORK[network]
    block = genesis_of(fork, genesis["genesisBlockHeader"], genesis["pre"])
    header = rlp.encode(rlp.decode(block)[0])
    return config(network), pre_state(genesis["pre"]), [(fork, header, [])]


def _attributes(header: list, withdrawals: list | None) -> dict[str, object]:
    """The payload attributes that a header and its withdrawals give, at the fork of the header."""
    attributes: dict[str, object] = {
        "timestamp": _quantity(header[TIMESTAMP]),
        "prevRandao": _data(header[MIX_HASH]),
        "suggestedFeeRecipient": _data(header[COINBASE]),
    }
    if withdrawals is not None:
        attributes["withdrawals"] = [
            {
                "index": _quantity(index),
                "validatorIndex": _quantity(validator),
                "address": _data(address),
                "amount": _quantity(amount),
            }
            for index, validator, address, amount in withdrawals
        ]
    if len(header) > BEACON_ROOT:
        attributes["parentBeaconBlockRoot"] = _data(header[BEACON_ROOT])
    if len(header) > SLOT_NUMBER:
        attributes["slotNumber"] = _quantity(header[SLOT_NUMBER])
        attributes["targetGasLimit"] = _quantity(header[GAS_LIMIT])
    return attributes


def _balances(accounts: bytes) -> dict[bytes, int]:
    """The balance of each account of a state in the form of the state root export."""
    return {entry[0]: int.from_bytes(entry[2], "big") for entry in rlp.decode(accounts)}


@pytest.mark.parametrize("network", list(METHODS))
def test_builds_the_block_of_the_fixture(network: str) -> None:
    """The inputs of the first block of a fixture build that block, with the same header hash."""
    vector = _first_block(network)
    items = rlp.decode(bytes.fromhex(vector["rlp"].removeprefix("0x")))
    header, transactions = items[0], items[1]
    withdrawals = items[3] if len(items) > 3 else None
    chain_config, state, recent = _chain(network)
    built, accounts, requests, value = engine.build_payload(
        chain_config,
        state,
        recent,
        METHODS[network],
        _attributes(header, withdrawals),
        header[COINBASE],
        header[EXTRA_DATA],
        int.from_bytes(header[GAS_LIMIT], "big"),
        [rlp.encode(tx) for tx in transactions],
    )
    built_header = rlp.decode(built)[0]
    assert keccak256(rlp.encode(built_header)).hex() == vector["hash"]
    assert rlp.decode(built)[1] == transactions
    # The block passes the state transition, which gives the accounts of the build.
    root, after = blocks.state_transition(chain_config, state, recent, recent[0][0], built, False)
    assert root == built_header[3]
    assert rlp.encode(after) == accounts
    # The value is what the fee recipient gained: the block pays it only the priority fees.
    coinbase = header[COINBASE]
    gained = _balances(accounts).get(coinbase, 0) - _balances(state).get(coinbase, 0)
    assert value == gained
    # Each of these blocks has a transaction that pays a priority fee, so the value is not 0.
    assert transactions
    assert value > 0
    assert requests == []


def test_attributes_not_above_the_parent() -> None:
    """Attributes whose timestamp is not above the parent's are invalid, as for the update."""
    chain_config, state, recent = _chain("Paris")
    attributes = {
        "timestamp": "0x0",
        "prevRandao": _data(bytes(32)),
        "suggestedFeeRecipient": _data(bytes(20)),
    }
    with raises(
        EngineError, "engine error: EthLib.Engine.EngineError.invalidPayloadAttributes"
    ) as error:
        engine.build_payload(
            chain_config,
            state,
            recent,
            "engine_forkchoiceUpdatedV1",
            attributes,
            bytes(20),
            b"",
            30_000_000,
            [],
        )
    assert error.value.code == 38003
