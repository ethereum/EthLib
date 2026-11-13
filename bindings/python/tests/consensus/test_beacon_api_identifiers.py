"""The identifiers of the Beacon API, resolved against the store of a fork choice case."""

import functools
from pathlib import Path
from typing import Any

import pytest

from ethlib import consensus

from .containers import FORKS
from .test_fork_choice import _hex, _inputs, _load, _read

# A Capella case whose store finalizes epoch 3 and justifies epoch 4, with its head at slot 43.
CASE = (
    Path(__file__).resolve().parents[4]
    / "tests/consensus/fork_choice/minimal/capella/fork_choice/withholding/pyspec_tests"
    / "withholding_attack"
)
FORK = FORKS["capella"]


@functools.cache
def _checks() -> dict[str, Any]:
    """The checks of the last step of the case: its head and its checkpoints."""
    return _load(CASE / "steps.yaml")[-1]["checks"]


def _resolve(*queries: consensus.ApiQuery) -> list:
    """The answer to each query, against the store after every step of the case."""
    steps = [step for raw in _load(CASE / "steps.yaml") for step in _inputs(CASE, raw)]
    return consensus.api_resolve(
        "minimal",
        FORK,
        _read(CASE, "anchor_state"),
        _read(CASE, "anchor_block"),
        steps,
        list(queries),
    )


def _found(*queries: consensus.ApiQuery) -> list:
    """What each query names, which must be found or be None."""
    answers = _resolve(*queries)
    assert all(answer[0] == "found" for answer in answers), answers
    return [answer[1] for answer in answers]


def _named(root: bytes, slot: int, finalized: bool, index: int | None = None) -> dict[str, Any]:
    """The answer for a block, or for the state after it."""
    return {"root": root, "slot": slot, "finalized": finalized, "index": index}


@functools.cache
def _anchor() -> dict[str, Any]:
    """The JSON of the anchor block and of the anchor state."""
    block = consensus.api_json("minimal", FORK, "BeaconBlock", _read(CASE, "anchor_block"))
    state = consensus.api_json("minimal", FORK, "BeaconState", _read(CASE, "anchor_state"))
    return {"block": block, "state": state}


def test_words_and_slots():
    checks = _checks()
    head = _hex(checks["head"]["root"])
    slot = checks["head"]["slot"]
    finalized = _hex(checks["finalized_checkpoint"]["root"])
    justified = _hex(checks["justified_checkpoint"]["root"])
    answers = _found(
        ("block", "head"),
        ("block", str(slot)),
        ("block", "0x" + head.hex().upper()),
        ("state", "head"),
        ("block", "finalized"),
        ("state", "justified"),
    )
    assert answers[:4] == [_named(head, slot, False)] * 4
    # The finalized block is reported finalized, and the justified one, after it, is not.
    assert answers[4]["root"] == finalized
    assert answers[4]["finalized"] is True
    assert answers[5]["root"] == justified
    assert answers[5]["finalized"] is False


def test_genesis():
    # The anchor of the case is the genesis block, an ancestor of the finalized block.
    anchor = _anchor()["block"]
    assert anchor["slot"] == "0"
    genesis, by_slot, by_state_root = _found(
        ("block", "genesis"), ("block", "0"), ("state", anchor["state_root"])
    )
    assert genesis["slot"] == 0
    assert genesis["finalized"] is True
    assert by_slot == genesis
    assert by_state_root == genesis


def test_validators():
    pubkey = _anchor()["state"]["validators"][3]["pubkey"]
    count = len(_anchor()["state"]["validators"])
    answers = _found(
        ("validator", "head", "0"),
        ("validator", "head", pubkey),
        ("validator", "head", str(count - 1)),
        ("validator", "head", str(count)),
        ("validator", "head", "0x" + "00" * 48),
    )
    assert [answer and answer["index"] for answer in answers] == [0, 3, count - 1, None, None]


def test_names_of_nothing():
    # Each identifier is well formed, and the store holds nothing that it names.
    assert _found(
        ("block", "0x" + "00" * 32),
        ("state", "0x" + "00" * 32),
        ("block", "18446744073709551615"),
    ) == [None, None, None]


@pytest.mark.parametrize(
    "query, message",
    [
        pytest.param(("state", "current"), "Invalid state ID: current", id="state-word"),
        pytest.param(("block", "justified"), "Invalid block ID: justified", id="block-justified"),
        pytest.param(("block", "01"), "Invalid block ID: 01", id="leading-zero"),
        pytest.param(("block", "-1"), "Invalid block ID: -1", id="sign"),
        pytest.param(
            ("block", "18446744073709551616"),
            "Invalid block ID: 18446744073709551616",
            id="slot-overflow",
        ),
        pytest.param(("block", "0x" + "00" * 31), "Invalid block ID: 0x" + "00" * 31, id="short"),
        pytest.param(("block", "0X" + "00" * 32), "Invalid block ID: 0X" + "00" * 32, id="0X"),
        pytest.param(
            ("validator", "head", "0x" + "00" * 32),
            "Invalid validator ID: 0x" + "00" * 32,
            id="validator-root",
        ),
        pytest.param(("validator", "now", "0"), "Invalid state ID: now", id="validator-state"),
    ],
)
def test_texts_that_name_nothing(query, message):
    assert _resolve(query) == [("refused", 400, message)]
