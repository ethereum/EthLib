"""The payload build, against the first block of a blockchain test at each fork from Paris."""

import json

import pytest

import archives
from ethlib import engine
from ethlib.cryptography.keccak import keccak256
from ethlib.errors import EngineError
from ethlib.execution import blocks
from ethlib.execution.blocks import RecentBlock
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
COINBASE, GAS_LIMIT, TIMESTAMP, EXTRA_DATA, MIX_HASH = 2, 9, 11, 12, 13
BEACON_ROOT, SLOT_NUMBER = 19, 22


def _quantity(raw: bytes) -> str:
    """The Engine API quantity of a big-endian number."""
    return hex(int.from_bytes(raw, "big"))


def _data(raw: bytes) -> str:
    """The Engine API data of bytes."""
    return "0x" + raw.hex()


def _first_block(network: str) -> dict:
    """The first block after the genesis of the test that gives the genesis of the network."""
    test = GENESES[network]["test"]
    return next(v for v in VECTORS if v["test"] == test and v["block"] == 0)


def _chain(network: str) -> tuple[dict, bytes, list[RecentBlock]]:
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
        fee_recipient=header[COINBASE],
        extra_data=header[EXTRA_DATA],
        target_gas_limit=int.from_bytes(header[GAS_LIMIT], "big"),
        transactions=[rlp.encode(tx) for tx in transactions],
    )
    built_header = rlp.decode(built)[0]
    assert keccak256(rlp.encode(built_header)).hex() == vector["hash"]
    assert rlp.decode(built)[1] == transactions
    # The block passes the state transition, which gives the accounts of the build.
    root, after = blocks.state_transition(
        chain_config, state, recent, recent[0][0], built, check_seal=False
    )
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


# The genesis gas limit of every network, and one step of the header check from it.
GENESIS_GAS_LIMIT = 120_000_000
STEP = GENESIS_GAS_LIMIT // 1024 - 1
SUGGESTED, CHOSEN = bytes([0x66]) * 20, bytes([0x55]) * 20

# Attributes on the genesis of Paris and of Amsterdam, with a fee recipient the builder overrides.
PARIS: dict[str, object] = {
    "timestamp": "0xc",
    "prevRandao": _data(bytes(32)),
    "suggestedFeeRecipient": _data(SUGGESTED),
}
AMSTERDAM = PARIS | {
    "withdrawals": [],
    "parentBeaconBlockRoot": _data(bytes(32)),
    "slotNumber": "0x1",
}


def _build(
    network: str,
    attributes: dict[str, object],
    *,
    method: str | None = None,
    extra_data: bytes = b"",
    target: int = GENESIS_GAS_LIMIT,
    transactions: list[bytes] | None = None,
    recent: list[RecentBlock] | None = None,
) -> list:
    """The header that a build gives on the genesis of a network, with no transaction by default."""
    chain_config, state, genesis = _chain(network)
    built, _, _, _ = engine.build_payload(
        chain_config,
        state,
        genesis if recent is None else recent,
        method or METHODS[network],
        attributes,
        fee_recipient=CHOSEN,
        extra_data=extra_data,
        target_gas_limit=target,
        transactions=transactions or [],
    )
    return rlp.decode(built)[0]


@pytest.mark.parametrize(
    ("target", "gas_limit"),
    [
        pytest.param(GENESIS_GAS_LIMIT * 2, GENESIS_GAS_LIMIT + STEP, id="up"),
        pytest.param(GENESIS_GAS_LIMIT // 2, GENESIS_GAS_LIMIT - STEP, id="down"),
        pytest.param(GENESIS_GAS_LIMIT + 7, GENESIS_GAS_LIMIT + 7, id="within"),
    ],
)
def test_gas_limit_moves_toward_the_target(target: int, gas_limit: int) -> None:
    """Before Amsterdam the gas limit moves toward the builder's target, by one step at most."""
    header = _build("Paris", PARIS, target=target)
    assert int.from_bytes(header[GAS_LIMIT], "big") == gas_limit


def test_target_of_the_attributes_from_amsterdam() -> None:
    """From Amsterdam the target of the attributes counts, and the builder's does not."""
    attributes = AMSTERDAM | {"targetGasLimit": hex(GENESIS_GAS_LIMIT * 2)}
    header = _build("Amsterdam", attributes, target=GENESIS_GAS_LIMIT // 2)
    assert int.from_bytes(header[GAS_LIMIT], "big") == GENESIS_GAS_LIMIT + STEP


def test_builder_chooses_the_fee_recipient() -> None:
    """The coinbase is the fee recipient that the builder chose, not the suggested one."""
    assert _build("Paris", PARIS)[COINBASE] == CHOSEN


@pytest.mark.parametrize("size", [0, 32])
def test_extra_data_up_to_32_bytes(size: int) -> None:
    """Extra data of at most 32 bytes goes into the header as given."""
    assert _build("Paris", PARIS, extra_data=bytes([7]) * size)[EXTRA_DATA] == bytes([7]) * size


def test_extra_data_above_32_bytes() -> None:
    """Extra data of 33 bytes fails the header check, with its block error."""
    with raises(EngineError, "block invalid: extraDataTooLong") as error:
        _build("Paris", PARIS, extra_data=bytes(33))
    assert error.value.code == 208


def test_transaction_that_does_not_decode() -> None:
    """A transaction that does not decode at the fork fails with its block error."""
    with raises(EngineError, "transaction 0 does not decode: emptyTransaction") as error:
        _build("Paris", PARIS, transactions=[rlp.encode(b"")])
    assert error.value.code == 254


def test_unknown_method() -> None:
    """A method that is not a version of engine_forkchoiceUpdated has code 0."""
    with raises(EngineError, "no method engine_forkchoiceUpdatedV9") as error:
        _build("Paris", PARIS, method="engine_forkchoiceUpdatedV9")
    assert error.value.code == 0


def test_no_recent_block() -> None:
    """A chain without a recent block has no parent to build on, and has code 0."""
    with raises(EngineError, "recent: no block") as error:
        _build("Paris", PARIS, recent=[])
    assert error.value.code == 0


def test_attributes_not_above_the_parent() -> None:
    """Attributes whose timestamp is not above the parent's are invalid, as for the update."""
    with raises(
        EngineError, "engine error: EthLib.Engine.EngineError.invalidPayloadAttributes"
    ) as error:
        _build("Paris", PARIS | {"timestamp": "0x0"})
    assert error.value.code == 38003
