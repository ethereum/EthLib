"""The Beacon API event of the payload attributes, against the forkchoice update of a proposer."""

import json
import re
from typing import Any

import pytest

from consensus.test_beacon_api_events import EXAMPLES
from ethlib import consensus, engine
from raising import raises

from .test_prepare_payload import (
    AFTER_CAPELLA,
    FEE_RECIPIENT,
    FINALIZED,
    HEADER,
    SAFE,
    SLOT,
    TTD,
    _hash,
    merged_bellatrix,
    pow_block,
    prepare,
    state_at,
)
from .test_prepare_payload_gloas import (
    EMPTY,
    FEE_RECIPIENT as GLOAS_FEE_RECIPIENT,
    FULL,
    GAS_LIMIT,
    NAMES,
    SAFE as GLOAS_SAFE,
    SECONDS_PER_SLOT,
    _read,
    block_root,
    payload_hashes,
    prepare as prepare_gloas,
    proposer_state,
    steps,
)

# The consensus version of each fork, by its name in EthLib.
VERSIONS = {
    "bellatrix": "bellatrix",
    "shapella": "capella",
    "dencun": "deneb",
    "pectra": "electra",
    "fusaka": "fulu",
    "glamsterdam": "gloas",
}

# The fields of the attributes that hold an integer, by their names in the Engine API.
QUANTITIES = {"timestamp", "index", "validatorIndex", "amount", "slotNumber", "targetGasLimit"}

TERMINAL_NUMBER = 77
PARENT_NUMBER = 1234


def _snake(name: str) -> str:
    return re.sub("[A-Z]", lambda upper: "_" + upper[0].lower(), name)


def _api(value: Any, name: str = "") -> Any:
    """An Engine API value as the Beacon API writes it: snake case keys and decimal integers."""
    if isinstance(value, dict):
        return {_snake(key): _api(item, key) for key, item in value.items()}
    if isinstance(value, list):
        return [_api(item) for item in value]
    return str(int(value, 16)) if name in QUANTITIES else value


def _proposer(name: str, fork: str, state: bytes) -> int:
    """The index of the first validator that proposes at the slot of a state."""
    index = next((i for i in range(1024) if consensus.is_proposer(name, fork, state, i)), None)
    assert index is not None
    return index


def _event(record: tuple[str, str]) -> dict[str, Any]:
    """An event of the stream, its topic and its data, read back from the text of its data."""
    topic, data = record
    return {"event": topic, "data": json.loads(data)}


def event(fork: str, state: bytes, pow_chain: list[bytes]) -> dict[str, Any] | None:
    record = engine.payload_attributes_event(
        "mainnet",
        fork,
        state,
        SAFE,
        FINALIZED,
        FEE_RECIPIENT,
        pow_chain,
        terminal_number=TERMINAL_NUMBER,
    )
    return None if record is None else _event(record)


def expected(
    fork: str, state: bytes, update: dict[str, Any], number: int, slot: int = SLOT
) -> dict[str, Any]:
    """The event that the update of a proposer and the state call for."""
    parent_root, _ = consensus.ssz_static("mainnet", fork, "BeaconBlockHeader", HEADER)
    return {
        "event": "payload_attributes",
        "data": {
            "version": VERSIONS[fork],
            "data": {
                "proposer_index": str(_proposer("mainnet", fork, state)),
                "proposal_slot": str(slot),
                "parent_block_number": str(number),
                "parent_block_root": "0x" + parent_root.hex(),
                "parent_block_hash": update["forkchoiceState"]["headBlockHash"],
                "payload_attributes": _api(update["payloadAttributes"]),
            },
        },
    }


def test_before_the_merge_the_parent_is_the_terminal_block() -> None:
    state = state_at("bellatrix")
    chain = [pow_block(_hash(2), _hash(1), TTD), pow_block(_hash(1), _hash(0), TTD - 1)]
    got = event("bellatrix", state, chain)
    assert got == expected("bellatrix", state, prepare("bellatrix", state, chain), TERMINAL_NUMBER)
    assert got["data"]["data"]["parent_block_hash"] == "0x" + _hash(2).hex()


def test_no_event_when_the_proposer_asks_nothing() -> None:
    assert event("bellatrix", state_at("bellatrix"), []) is None


def test_after_the_merge_the_number_is_that_of_the_latest_payload() -> None:
    # The latest payload header of the state, its last 536 bytes, has a block hash and a number.
    # The number follows six fields of 32, 20, 32, 32, 256 and 32 bytes.
    state = bytearray(merged_bellatrix(_hash(9)))
    start = len(state) - 536 + 404
    state[start : start + 8] = PARENT_NUMBER.to_bytes(8, "little")
    got = event("bellatrix", bytes(state), [])
    update = prepare("bellatrix", bytes(state), [])
    assert got == expected("bellatrix", bytes(state), update, PARENT_NUMBER)


@pytest.mark.parametrize("fork", AFTER_CAPELLA)
def test_withdrawals_and_parent_root(fork: str) -> None:
    state = state_at(fork)
    chain = [pow_block(_hash(1), bytes(32), TTD)]
    got = event(fork, state, chain)
    assert got == expected(fork, state, prepare(fork, state, chain), 0)
    # The withdrawal of validator 0 is written with decimal integers.
    (withdrawal,) = got["data"]["data"]["payload_attributes"]["withdrawals"]
    assert withdrawal["validator_index"] == "0"


@pytest.mark.parametrize("fork", ["phase0", "altair", "glamsterdam", "hegota"])
def test_fork_without_this_event(fork: str) -> None:
    with raises(engine.ProposerError, f"no payload preparation at {fork}") as info:
        event(fork, state_at("bellatrix"), [])
    assert info.value.code == 0


def test_state_that_does_not_decode() -> None:
    with raises(
        engine.ProposerError, "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 2736633 0"
    ) as info:
        event("bellatrix", b"", [])
    assert info.value.code == 0


def gloas_event(status: int, state: bytes | None = None) -> dict[str, Any]:
    record = engine.payload_attributes_event_gloas(
        "minimal",
        NAMES["gloas"],
        _read("gloas", "anchor_state"),
        _read("gloas", "anchor_block"),
        steps("gloas"),
        bytes.fromhex(block_root("gloas")[2:]),
        status,
        proposer_state("gloas") if state is None else state,
        GLOAS_SAFE,
        GLOAS_FEE_RECIPIENT,
        GAS_LIMIT,
    )
    return _event(record)


@pytest.mark.parametrize("status", [FULL, EMPTY])
def test_gloas(status: int) -> None:
    parent_hash, block_hash = payload_hashes("gloas")
    update = prepare_gloas("gloas", status)
    state = proposer_state("gloas")
    got = gloas_event(status)
    assert got == {
        "event": "payload_attributes",
        "data": {
            "version": VERSIONS["glamsterdam"],
            "data": {
                "proposer_index": str(_proposer("minimal", "glamsterdam", state)),
                "proposal_slot": "2",
                "parent_block_root": block_root("gloas"),
                "parent_block_hash": "0x" + (block_hash if status == FULL else parent_hash).hex(),
                "safe_block_hash": "0x" + GLOAS_SAFE.hex(),
                "finalized_block_hash": update["forkchoiceState"]["finalizedBlockHash"],
                "payload_attributes": _api(update["payloadAttributes"]),
            },
        },
    }
    # The event has the fields of the example of the source, which is a Gloas event.
    topic, example = EXAMPLES["payload_attributes"]
    assert got["event"] == topic
    assert set(got["data"]["data"]) == set(example["data"])
    # The timestamp is the time of slot 2.
    genesis_time = int.from_bytes(_read("gloas", "anchor_state")[:8], "little")
    attributes = got["data"]["data"]["payload_attributes"]
    assert attributes["timestamp"] == str(genesis_time + 2 * SECONDS_PER_SLOT)


@pytest.mark.parametrize("fork", ["bellatrix", "fusaka", "heze"])
def test_fork_without_this_event_on_a_store(fork: str) -> None:
    name = NAMES.get(fork, fork)
    with raises(engine.ProposerError, f"no payload attributes event on a store at {name}") as info:
        engine.payload_attributes_event_gloas(
            "minimal", name, b"", b"", [], bytes(32), EMPTY, b"", GLOAS_SAFE, GLOAS_FEE_RECIPIENT, 0
        )
    assert info.value.code == 0


def test_state_that_does_not_decode_on_a_store() -> None:
    with raises(
        engine.ProposerError, "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 14405 0"
    ) as info:
        gloas_event(EMPTY, state=b"")
    assert info.value.code == 0
