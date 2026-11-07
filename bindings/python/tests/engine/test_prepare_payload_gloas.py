"""The forkchoice update of an honest proposer from Gloas, on the store of a fork choice case."""

from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus, engine
from ethlib.networking import snappy
from raising import raises

PROPOSER_ERROR = engine.ProposerError

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "fork_choice" / "minimal"

# The case holds a block of slot 1 and its payload, both valid.
CASE = "fork_choice/on_execution_payload_envelope/pyspec_tests/on_execution_payload_envelope_valid"

# A minimal slot lasts 6 seconds.
SECONDS_PER_SLOT = 6

SAFE = bytes([0x0A]) * 32
FINALIZED = bytes([0x0B]) * 32
FEE_RECIPIENT = bytes([0xFE]) * 20
GAS_LIMIT = 60_000_000

EMPTY, FULL, PENDING = 0, 1, 2

# The name of each fork in EthLib, by its name in the cases.
NAMES = {"gloas": "glamsterdam", "heze": "hegota"}


def _read(fork: str, name: str) -> bytes:
    """The bytes of an SSZ file of the case, without the Snappy framing."""
    return snappy.decompress((FILES / fork / CASE / f"{name}.ssz_snappy").read_bytes())


def _file(fork: str, kind: str) -> str:
    """The name of the one file of a kind in the case, which ends with the root of its content."""
    (path,) = (FILES / fork / CASE).glob(f"{kind}_0x*.ssz_snappy")
    return path.name.removesuffix(".ssz_snappy")


def block_root(fork: str) -> str:
    return _file(fork, "block").removeprefix("block_")


def _offset(data: bytes, at: int) -> int:
    return int.from_bytes(data[at : at + 4], "little")


def payload_hashes(fork: str) -> tuple[bytes, bytes]:
    """The parent hash and the block hash of the payload of the case."""
    signed = _read(fork, _file(fork, "execution_payload_envelope"))
    # The signed envelope opens with the offset of the envelope.
    # The envelope opens with the offset of the payload.
    message = _offset(signed, 0)
    payload = message + _offset(signed, message)
    # The parent hash opens the payload.
    # The block hash follows 13 fields: 4 hashes, an address, a bloom, 4 numbers, an offset, a fee.
    block_hash = payload + 32 + 20 + 32 + 32 + 256 + 32 + 4 * 8 + 4 + 32
    return signed[payload : payload + 32], signed[block_hash : block_hash + 32]


def steps(fork: str, envelope: bool = True, tick: int = 2 * SECONDS_PER_SLOT) -> list:
    """The block of slot 1, its payload if asked, then a tick to a later slot."""
    taken = [
        ("tick", SECONDS_PER_SLOT),
        ("block", _read(fork, _file(fork, "block"))),
    ]
    if envelope:
        taken.append(("execution_payload", _read(fork, _file(fork, "execution_payload_envelope"))))
    return [*taken, ("tick", tick)]


def proposer_state(fork: str, slot: int = 2) -> bytes:
    """The state after the block of slot 1, moved on to the slot of the proposal."""
    anchor = _read(fork, "anchor_state")
    after = consensus.state_transition(
        "minimal", NAMES[fork], anchor, _read(fork, _file(fork, "block"))
    )
    return consensus.process_slots("minimal", NAMES[fork], after, slot - 1)


def prepare(
    fork: str, status: int, state: bytes | None = None, taken: list | None = None, root=None
):
    return engine.prepare_execution_payload_gloas(
        "minimal",
        NAMES[fork],
        _read(fork, "anchor_state"),
        _read(fork, "anchor_block"),
        steps(fork) if taken is None else taken,
        bytes.fromhex(block_root(fork)[2:]) if root is None else root,
        status,
        proposer_state(fork) if state is None else state,
        SAFE,
        FINALIZED,
        FEE_RECIPIENT,
        GAS_LIMIT,
    )


def _hex(data: bytes) -> str:
    return "0x" + data.hex()


def check_update(fork: str, update: dict, head: bytes) -> None:
    """Compare an update with the values that the guide gives for the case."""
    genesis_time = int.from_bytes(_read(fork, "anchor_state")[:8], "little")
    assert update["forkchoiceState"] == {
        "headBlockHash": _hex(head),
        "safeBlockHash": _hex(SAFE),
        "finalizedBlockHash": _hex(FINALIZED),
    }
    attributes = update["payloadAttributes"]
    assert attributes["timestamp"] == hex(genesis_time + 2 * SECONDS_PER_SLOT)
    assert len(bytes.fromhex(attributes["prevRandao"][2:])) == 32
    assert attributes["suggestedFeeRecipient"] == _hex(FEE_RECIPIENT)
    # No validator and no builder of the case can withdraw.
    assert attributes["withdrawals"] == []
    # The latest block header of the state is the block of slot 1.
    assert attributes["parentBeaconBlockRoot"] == block_root(fork)
    assert attributes["slotNumber"] == hex(2)
    assert attributes["targetGasLimit"] == hex(GAS_LIMIT)
    assert update["custodyColumns"] is None


@pytest.mark.parametrize("fork", ["gloas", "heze"])
def test_full_parent(fork: str):
    # The payload of the block of the previous slot is verified, and no member voted against it.
    _, block_hash = payload_hashes(fork)
    check_update(fork, prepare(fork, FULL), block_hash)


@pytest.mark.parametrize("fork", ["gloas", "heze"])
def test_empty_parent(fork: str):
    parent_hash, _ = payload_hashes(fork)
    check_update(fork, prepare(fork, EMPTY), parent_hash)


def test_inclusion_lists_from_heze():
    # The node received no inclusion list.
    assert prepare("heze", FULL)["inclusionListTransactions"] == []
    assert "inclusionListTransactions" not in prepare("gloas", FULL)


def test_pending_head():
    with raises(PROPOSER_ERROR, "proposer step failed with code 15") as info:
        prepare("gloas", PENDING)
    assert info.value.code == 15


def test_unknown_head():
    with raises(PROPOSER_ERROR, "proposer step failed with code 15") as info:
        prepare("gloas", FULL, root=bytes(32))
    assert info.value.code == 15


def test_full_head_without_its_payload():
    # Two slots later, a full head is followed whatever the committee says, but the store lacks it.
    with raises(PROPOSER_ERROR, "proposer step failed with code 15") as info:
        prepare(
            "gloas", FULL, proposer_state("gloas", 3), steps("gloas", False, 3 * SECONDS_PER_SLOT)
        )
    assert info.value.code == 15


def test_inclusion_lists_at_slot_0():
    # The proposer builds on the anchor, at slot 0, which has no slot before it.
    checks = YAML(typ="safe").load((FILES / "heze" / CASE / "steps.yaml").read_text())[1]["checks"]
    anchor_root = bytes.fromhex(checks["head"]["root"][2:])
    with raises(PROPOSER_ERROR, "proposer step failed with code 16") as info:
        prepare("heze", EMPTY, _read("heze", "anchor_state"), [], anchor_root)
    assert info.value.code == 16


@pytest.mark.parametrize("fork", ["bellatrix", "fusaka"])
def test_fork_without_this_preparation(fork: str):
    with raises(PROPOSER_ERROR, f"no payload preparation on a store at {fork}") as info:
        engine.prepare_execution_payload_gloas(
            "minimal", fork, b"", b"", [], bytes(32), EMPTY, b"", SAFE, FINALIZED, FEE_RECIPIENT, 0
        )
    assert info.value.code == 0


def test_unknown_payload_status():
    with raises(PROPOSER_ERROR, "a payload status is 0, 1 or 2") as info:
        prepare("gloas", 3)
    assert info.value.code == 0


@pytest.mark.parametrize(
    ("root", "safe", "finalized", "fee", "message"),
    [
        (bytes(31), SAFE, FINALIZED, FEE_RECIPIENT, "Err.scope 32 31"),
        (bytes(32), SAFE[:31], FINALIZED, FEE_RECIPIENT, "Err.scope 32 31"),
        (bytes(32), SAFE, FINALIZED[:31], FEE_RECIPIENT, "Err.scope 32 31"),
        (bytes(32), SAFE, FINALIZED, FEE_RECIPIENT[:19], "Err.scope 20 19"),
    ],
    ids=["head", "safe", "finalized", "fee recipient"],
)
def test_input_of_the_wrong_length(root, safe, finalized, fee, message: str):
    with raises(PROPOSER_ERROR, f"input rejected: EthLib.Serialization.Ssz.{message}") as info:
        engine.prepare_execution_payload_gloas(
            "minimal",
            "glamsterdam",
            _read("gloas", "anchor_state"),
            _read("gloas", "anchor_block"),
            [],
            root,
            EMPTY,
            proposer_state("gloas"),
            safe,
            finalized,
            fee,
            GAS_LIMIT,
        )
    assert info.value.code == 0


def test_state_that_does_not_decode():
    with raises(
        PROPOSER_ERROR, "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 14405 0"
    ) as info:
        prepare("gloas", EMPTY, b"")
    assert info.value.code == 0
