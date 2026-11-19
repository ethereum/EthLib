"""The Beacon API events of the fork choice, against the checks of pinned fork choice cases."""

import copy
import json
from collections.abc import Sequence
from functools import cache
from itertools import pairwise
from pathlib import Path
from typing import Any, NamedTuple

import pytest

from ethlib import consensus
from raising import raises

from .containers import FORKS
from .test_data_column import replacements
from .test_fork_choice import _hex, _inputs, _load, _read

FILES = Path(__file__).resolve().parents[4] / "tests/consensus/fork_choice/minimal"

# The minimal preset: slots in an epoch, and seconds in a slot.
SLOTS_PER_EPOCH = 8
SECONDS_PER_SLOT = 6

# The number of reads of the head up to which a case checks every pair of reads.
SHORT = 20

# The API names of the payload statuses that a Gloas check records by code.
PAYLOAD_STATUS = {0: "empty", 1: "full", 2: "pending"}

# A case whose head moves to another branch between two checks.
REORG = "current_slot_head_correct_after_reorg"

# Each case: its fork, and its path under the fork choice cases of that fork.
CHAIN_CASES = [
    ("capella", "fork_choice/ex_ante/pyspec_tests/ex_ante_vanilla"),
    ("electra", "fork_choice/reorg/pyspec_tests/delayed_justification_previous_epoch"),
    ("fulu", f"fast_confirmation/variables/pyspec_tests/{REORG}"),
    ("gloas", "fork_choice/ex_ante/pyspec_tests/ex_ante_vanilla"),
    (
        "gloas",
        "fork_choice/on_execution_payload_envelope/pyspec_tests/"
        "on_execution_payload_envelope_valid",
    ),
]
CONFIRMATION_CASES = [
    ("altair", "fast_confirmation/basic/pyspec_tests/fast_confirm_an_epoch"),
    ("deneb", "fast_confirmation/basic/pyspec_tests/fast_confirm_an_epoch"),
    ("fulu", f"fast_confirmation/variables/pyspec_tests/{REORG}"),
]

# The slot, the parent root and the state root of a block.
Header = tuple[int, str, str]
Check = dict[str, Any]


class Case(NamedTuple):
    """A fork choice case, as the exports take it and as the tests read it."""

    store: tuple[str, str, bytes, bytes]
    steps: list[consensus.ForkChoiceStep]
    options: dict[str, Any]
    # Each check, with the number of steps that run before its read.
    checks: list[tuple[int, Check]]
    headers: dict[str, Header]

    @property
    def genesis(self) -> str:
        """The root of the anchor, which is the genesis block in these cases."""
        return self.checks[0][1]["head"]["root"]

    def reads(self) -> list[tuple[int, Check]]:
        """The checks that read the head, with their steps."""
        return [(end, check) for end, check in self.checks if "head" in check]

    def events(self, first: int, end: int, optimistic: Sequence[str] = ()) -> list[dict[str, Any]]:
        """The events between the stores after the first steps and after the first `end`."""
        records = consensus.api_chain_events(
            *self.store,
            self.steps[:end],
            first=first,
            genesis_root=_hex(self.genesis),
            optimistic_roots=[_hex(root) for root in optimistic],
            **self.options,
        )
        return [_event(record) for record in records]


def _event(record: tuple[str, str]) -> dict[str, Any]:
    """An event of the stream, its topic and its data, read back from the text of its data."""
    topic, data = record
    return {"event": topic, "data": json.loads(data)}


def _header(data: bytes, *, signed: bool) -> Header:
    """The slot, the parent root and the state root of a block, read from its SSZ bytes."""
    # A signed block is the offset of its message, then the signature of 96 bytes.
    if signed:
        assert data[:4] == (100).to_bytes(4, "little")
        data = data[100:]
    # A block starts with its slot, its proposer index, its parent root and its state root.
    return int.from_bytes(data[:8], "little"), "0x" + data[16:48].hex(), "0x" + data[48:80].hex()


@cache
def _case(fork: str, path: str) -> Case:
    case = FILES / fork / path
    steps: list[consensus.ForkChoiceStep] = []
    checks: list[tuple[int, Check]] = []
    headers: dict[str, Header] = {}
    for step in _load(case / "steps.yaml"):
        steps += _inputs(case, step)
        if "checks" in step:
            checks.append((len(steps), step["checks"]))
        if "block" in step and step.get("valid", True):
            root = "0x" + step["block"].removeprefix("block_0x")
            headers[root] = _header(_read(case, step["block"]), signed=True)
    anchor = _read(case, "anchor_block")
    headers[checks[0][1]["head"]["root"]] = _header(anchor, signed=False)
    # The anchor is the genesis block, so every chain reaches back to slot 0.
    assert headers[checks[0][1]["head"]["root"]][0] == 0
    config_file = case / "config.yaml"
    config = replacements(_load(config_file), "minimal") if config_file.exists() else None
    meta = _load(case / "meta.yaml") if (case / "meta.yaml").exists() else {}
    # Setting 2 marks placeholder signatures, which the case must not check.
    verify = (meta or {}).get("bls_setting", 0) != 2
    store = ("minimal", FORKS[fork], _read(case, "anchor_state"), anchor)
    return Case(store, steps, {"config": config, "verify": verify}, checks, headers)


def _ancestors(headers: dict[str, Header], root: str) -> list[str]:
    """A block and its known ancestors, from the block back to the anchor."""
    chain = [root]
    while headers[chain[-1]][1] in headers:
        chain.append(headers[chain[-1]][1])
    return chain


def _root_at_slot(headers: dict[str, Header], head: str, slot: int, genesis: str) -> str:
    """The root of the latest block of the chain of a head at or before a slot."""
    if slot < 0:
        return genesis
    return next(root for root in _ancestors(headers, head) if headers[root][0] <= slot)


def _head_changed(old: Check, new: Check) -> bool:
    """Whether a head event follows: a new head block, or its payload from empty to full."""
    return old["root"] != new["root"] or (
        old.get("payload_status") == 0 and new.get("payload_status") == 1
    )


def _expected(fork: str, case: Case, before: Check, after: Check) -> list[dict[str, Any]]:
    """The events that the checks of two stores call for, with their data."""
    headers, genesis = case.headers, case.genesis
    events: list[dict[str, Any]] = []
    old, new = before["head"], after["head"]
    if _head_changed(old, new):
        slot = new["slot"]
        epoch = slot // SLOTS_PER_EPOCH
        status = PAYLOAD_STATUS[new["payload_status"]] if "payload_status" in new else "full"
        start = epoch * SLOTS_PER_EPOCH
        data = {
            "slot": str(slot),
            "block": new["root"],
            "state": headers[new["root"]][2],
            "payload_status": status,
            "epoch_transition": old["slot"] // SLOTS_PER_EPOCH != epoch,
            "current_epoch_dependent_root": _root_at_slot(
                headers, new["root"], start - SLOTS_PER_EPOCH - 1, genesis
            ),
            "next_epoch_dependent_root": _root_at_slot(headers, new["root"], start - 1, genesis),
            "execution_optimistic": False,
        }
        events.append({"event": "head_v2", "data": {"version": fork, "data": data}})
        ancestors = _ancestors(headers, new["root"])
        if old["root"] not in ancestors:
            common = next(root for root in _ancestors(headers, old["root"]) if root in ancestors)
            events.append(
                {
                    "event": "chain_reorg",
                    "data": {
                        "slot": str(slot),
                        "depth": str(old["slot"] - headers[common][0]),
                        "old_head_block": old["root"],
                        "new_head_block": new["root"],
                        "old_head_state": headers[old["root"]][2],
                        "new_head_state": headers[new["root"]][2],
                        "epoch": str(epoch),
                        "execution_optimistic": False,
                    },
                }
            )
    checkpoint = after["finalized_checkpoint"]
    if before["finalized_checkpoint"] != checkpoint:
        events.append(
            {
                "event": "finalized_checkpoint",
                "data": {
                    "block": checkpoint["root"],
                    "state": headers[checkpoint["root"]][2],
                    "epoch": str(checkpoint["epoch"]),
                    "execution_optimistic": False,
                },
            }
        )
    return events


@pytest.mark.parametrize(("fork", "path"), CHAIN_CASES)
def test_chain_events(fork: str, path: str) -> None:
    case = _case(fork, path)
    seen: set[str] = set()
    quiet_after_events = False
    for (first, before), (end, after) in pairwise(case.reads()):
        expected = _expected(fork, case, before, after)
        # Each call replays the case twice, so a long case checks the pairs with events.
        # It also checks the first pair without events after them.
        if not expected and len(case.reads()) > SHORT and not quiet_after_events:
            continue
        quiet_after_events = bool(expected)
        assert case.events(first, end) == expected
        seen.update(event["event"] for event in expected)
    # A case that gives no event would check nothing.
    assert "head_v2" in seen


def test_chain_cases_cover_each_event() -> None:
    # This guards the list of cases, not the export.
    topics: set[str] = set()
    payload_arrives = False
    for fork, path in CHAIN_CASES:
        case = _case(fork, path)
        for (_, before), (_, after) in pairwise(case.reads()):
            topics.update(e["event"] for e in _expected(fork, case, before, after))
            old, new = before["head"], after["head"]
            payload_arrives |= old["root"] == new["root"] and _head_changed(old, new)
    assert topics == {"head_v2", "chain_reorg", "finalized_checkpoint"}
    assert payload_arrives


def _reorg_pair(fork: str, case: Case) -> tuple[int, int, list[dict[str, Any]]]:
    """The steps of the first pair of reads with a reorganization, and its events."""
    for (first, before), (end, after) in pairwise(case.reads()):
        expected = _expected(fork, case, before, after)
        if any(event["event"] == "chain_reorg" for event in expected):
            return first, end, expected
    raise LookupError("the case has no reorganization")


def test_chain_events_optimistic() -> None:
    case = _case("fulu", f"fast_confirmation/variables/pyspec_tests/{REORG}")
    first, end, expected = _reorg_pair("fulu", case)
    new_head = expected[0]["data"]["data"]["block"]
    # The head and the reorganization both read the flag of the new head.
    optimistic = copy.deepcopy(expected)
    optimistic[0]["data"]["data"]["execution_optimistic"] = True
    optimistic[1]["data"]["execution_optimistic"] = True
    assert case.events(first, end, [new_head]) == optimistic
    # The old head and the anchor are not read.
    old_head = expected[1]["data"]["old_head_block"]
    assert case.events(first, end, [old_head, case.genesis]) == expected


def test_chain_events_unknown_fork() -> None:
    case = _case(*CHAIN_CASES[0])
    with raises(consensus.ForkChoiceError, "no fork named altairx"):
        consensus.api_chain_events(
            "minimal", "altairx", *case.store[2:], [], first=0, genesis_root=bytes(32)
        )


@pytest.mark.parametrize(("fork", "path"), CONFIRMATION_CASES)
def test_fast_confirmation_event(fork: str, path: str) -> None:
    case = _case(fork, path)
    runs = [(end, check) for end, check in case.checks if "confirmed_root" in check]
    assert runs
    for end, check in runs:
        # The run of the rule comes just before the read of its checks.
        assert case.steps[end - 2] == ("fast_confirmation", None)
        # A tick after the run does not move the clock of its event.
        later: consensus.ForkChoiceStep = ("tick", check["time"] + 10 * SECONDS_PER_SLOT)
        taken = [*case.steps[:end], later]
        event = _event(consensus.api_fast_confirmation_event(*case.store, taken, **case.options))
        root = check["confirmed_root"]
        # The genesis time of the cases is 0, so the time of a check gives its slot.
        assert event == {
            "event": "fast_confirmation",
            "data": {
                "block": root,
                "slot": str(case.headers[root][0]),
                "current_slot": str(check["time"] // SECONDS_PER_SLOT),
            },
        }


def test_fast_confirmation_event_without_a_run() -> None:
    case = _case(*CONFIRMATION_CASES[0])
    with raises(consensus.ForkChoiceError, "no run of the fast confirmation rule passed"):
        consensus.api_fast_confirmation_event(*case.store, [], **case.options)
