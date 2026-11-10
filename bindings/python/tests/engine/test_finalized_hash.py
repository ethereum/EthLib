"""The finalized block hash of a forkchoice update, on the store of a fork choice case."""

from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus, engine
from ethlib.networking import snappy
from raising import raises

FILES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "fork_choice" / "minimal"

# The case finalizes epoch 3, on a block that the case holds, at each of these forks.
CASE = "fork_choice/withholding/pyspec_tests/withholding_attack"

# The name of each fork in EthLib, by its name in the cases.
NAMES = {
    "bellatrix": "bellatrix",
    "capella": "shapella",
    "deneb": "dencun",
    "gloas": "glamsterdam",
}

_YAML = YAML(typ="safe")


def _read(fork: str, name: str) -> bytes:
    """The bytes of an SSZ file of the case, without the Snappy framing."""
    return snappy.decompress((FILES / fork / CASE / f"{name}.ssz_snappy").read_bytes())


def _offset(data: bytes, at: int) -> int:
    return int.from_bytes(data[at : at + 4], "little")


def _steps(fork: str) -> tuple[list, bytes]:
    """The ticks, blocks and attestations of the case, and its last finalized root."""
    steps = []
    finalized = b""
    for step in _YAML.load((FILES / fork / CASE / "steps.yaml").read_text()):
        if "tick" in step:
            steps.append(("tick", step["tick"]))
        elif "checks" in step:
            if "finalized_checkpoint" in step["checks"]:
                root = step["checks"]["finalized_checkpoint"]["root"]
                finalized = bytes.fromhex(root.removeprefix("0x"))
        else:
            # A block step also says that the block is valid, which every one of them is.
            (kind,) = step.keys() - {"valid"}
            steps.append((kind, _read(fork, step[kind])))
    return steps, finalized


def _hash_in_block(fork: str, signed: bytes) -> bytes:
    """Read the hash that the update names out of a signed block, by the offsets of its SSZ."""
    # A signed block opens with the offset of the block.
    # The body follows the slot, the proposer index, two roots and its own offset.
    body = _offset(signed, 0) + _offset(signed, _offset(signed, 0) + 8 + 8 + 32 + 32)
    # Before the variable part of the body come its fixed fields and offsets.
    # They are the RANDAO reveal, the Eth1 data, the graffiti, 5 offsets and the sync aggregate.
    # The minimal sync committee has 32 members, so its bits take 4 bytes.
    fixed = 96 + 72 + 32 + 5 * 4 + 4 + 96
    if fork == "gloas":
        # The offset of the changes of withdrawal credentials comes first, then that of the bid.
        bid = body + _offset(signed, body + fixed + 4)
        # The signed bid opens with the offset of the bid, whose parent block hash comes first.
        message = bid + _offset(signed, bid)
        return signed[message : message + 32]
    payload = body + _offset(signed, body + fixed)
    # The block hash follows 12 fields of the payload.
    # They are 4 of 32 bytes, an address, a bloom, 4 numbers, an offset and a fee.
    block_hash = payload + 32 + 20 + 32 + 32 + 256 + 32 + 4 * 8 + 4 + 32
    return signed[block_hash : block_hash + 32]


def finalized_hash(fork: str, steps: list) -> bytes:
    """The finalized block hash of the store after the steps of the case."""
    return engine.finalized_execution_block_hash(
        "minimal", NAMES[fork], _read(fork, "anchor_state"), _read(fork, "anchor_block"), steps
    )


@pytest.mark.parametrize("fork", sorted(NAMES))
def test_finalized_block(fork: str) -> None:
    # Before Gloas the hash is that of the payload of the finalized block.
    # From Gloas it is the parent block hash in the bid of the finalized block.
    steps, root = _steps(fork)
    want = _hash_in_block(fork, _read(fork, f"block_0x{root.hex()}"))
    assert want != bytes(32)
    assert finalized_hash(fork, steps) == want


def test_anchor_before_any_block() -> None:
    # The store finalizes its anchor block, whose payload is empty in this case.
    assert finalized_hash("bellatrix", []) == bytes(32)


@pytest.mark.parametrize("fork", ["phase0", "altair"])
def test_fork_before_bellatrix(fork: str) -> None:
    with raises(consensus.ForkChoiceError, f"no execution block hash at {fork}") as info:
        engine.finalized_execution_block_hash("minimal", fork, b"", b"", [])
    assert info.value.code == 0
