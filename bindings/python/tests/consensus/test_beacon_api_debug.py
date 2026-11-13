"""The Beacon API views of the fork choice tree, on the stores of pinned fork choice cases."""

from collections.abc import Sequence
from functools import cache
from pathlib import Path
from typing import Any

import pytest

from ethlib import consensus

from .containers import FORKS
from .test_data_column import replacements
from .test_fork_choice import _hex, _inputs, _load, _read

CASES = Path(__file__).resolve().parents[4] / "tests/consensus/fork_choice/minimal"

# The size of the payload timeliness committee of the minimal preset.
PTC_SIZE = 16

# Each case: its fork, and its path under the fork choice cases of that fork.
PRE_GLOAS = [
    ("capella", "withholding/pyspec_tests/withholding_attack"),
    ("deneb", "ex_ante/pyspec_tests/ex_ante_vanilla"),
]
ENVELOPE = (
    "gloas",
    "on_execution_payload_envelope/pyspec_tests/on_execution_payload_envelope_valid",
)
# The cases whose checks record the votes of the payload committee for a block.
VOTES = [
    (
        "gloas",
        "on_payload_attestation_message/pyspec_tests/on_payload_attestation_message_from_block",
    ),
    ("gloas", "payload_timeliness/pyspec_tests/payload_timeliness_above_threshold_returns_true"),
    (
        "gloas",
        "payload_data_availability/pyspec_tests/"
        "payload_data_availability_above_threshold_returns_true",
    ),
]
GLOAS = [
    ENVELOPE,
    *VOTES,
    (
        "gloas",
        "filter_node_tree_variants/pyspec_tests/"
        "get_filtered_node_tree_contains_both_viable_childless_variants",
    ),
]

StoreCase = tuple[str, str, bytes, bytes, list[consensus.ForkChoiceStep]]


def _case(fork: str, path: str) -> Path:
    return CASES / fork / "fork_choice" / path


@cache
def _store_case(fork: str, path: str) -> tuple[StoreCase, dict[str, Any] | None]:
    """The arguments that build the store after every step of a case, and its own config."""
    case = _case(fork, path)
    steps = [step for raw in _load(case / "steps.yaml") for step in _inputs(case, raw)]
    config_file = case / "config.yaml"
    config = replacements(_load(config_file), "minimal") if config_file.exists() else None
    anchor = _read(case, "anchor_state"), _read(case, "anchor_block")
    return ("minimal", FORKS[fork], *anchor, steps), config


def _last_check(fork: str, path: str, key: str, *, first: bool = False) -> Any:
    """The value at the last check of a case that records a key, or at the first one."""
    steps = _load(_case(fork, path) / "steps.yaml")
    values = [step["checks"][key] for step in steps if key in step.get("checks", {})]
    return values[0] if first else values[-1]


def _fork_choice(fork: str, path: str, optimistic: Sequence[bytes] = ()) -> dict[str, Any]:
    case, config = _store_case(fork, path)
    return consensus.api_fork_choice(*case, optimistic_roots=optimistic, config=config)["data"]


def _heads(fork: str, path: str, optimistic: Sequence[bytes] = ()) -> list[dict[str, Any]]:
    case, config = _store_case(fork, path)
    return consensus.api_chain_heads(*case, optimistic_roots=optimistic, config=config)["data"]


def _blocks(fork: str, path: str) -> dict[str, tuple[int, str]]:
    """The slot and the parent root of the anchor and of each valid block of a case, by root."""
    case = _case(fork, path)
    anchor = _last_check(fork, path, "head", first=True)["root"]
    found = {anchor: _message_slot_and_parent(_read(case, "anchor_block"), signed=False)}
    for step in _load(case / "steps.yaml"):
        if "block" in step and step.get("valid", True):
            root = "0x" + step["block"].removeprefix("block_0x")
            found[root] = _message_slot_and_parent(_read(case, step["block"]), signed=True)
    return found


def _message_slot_and_parent(data: bytes, *, signed: bool) -> tuple[int, str]:
    """The slot and the parent root of a block, read from its SSZ bytes."""
    # A signed block is the offset of its message, then the signature of 96 bytes.
    if signed:
        assert data[:4] == (100).to_bytes(4, "little")
        data = data[100:]
    # A block starts with its slot, its proposer index and its parent root.
    return int.from_bytes(data[:8], "little"), "0x" + data[16:48].hex()


def _key(node: dict[str, Any]) -> tuple[str, str]:
    return node["block_root"], node["payload_status"]


def _counts(node: dict[str, Any]) -> tuple[int, int, int]:
    return (
        int(node["payload_attester_count"]),
        int(node["payload_availability_yes_count"]),
        int(node["payload_data_availability_yes_count"]),
    )


@pytest.mark.parametrize(("fork", "path"), PRE_GLOAS + GLOAS)
def test_checkpoints_and_parents(fork: str, path: str) -> None:
    data = _fork_choice(fork, path)
    for name in ("justified_checkpoint", "finalized_checkpoint"):
        checkpoint = _last_check(fork, path, name)
        assert data[name] == {"epoch": str(checkpoint["epoch"]), "root": checkpoint["root"]}
    nodes = {_key(node): node for node in data["fork_choice_nodes"]}
    assert len(nodes) == len(data["fork_choice_nodes"])
    for node in nodes.values():
        assert node["extra_data"] == {}
        assert node["validity"] == "valid"
        parent = node["parent_payload_status"]
        # A parent that a view names is a node of the tree.
        if parent is not None:
            assert (node["parent_root"], parent) in nodes
        if fork == "gloas" and node["payload_status"] != "pending":
            assert (node["parent_root"], parent) == (node["block_root"], "pending")
    # Only the pending node of the anchor block has no parent in the tree.
    assert sum(node["parent_payload_status"] is None for node in nodes.values()) == 1


@pytest.mark.parametrize(("fork", "path"), PRE_GLOAS + GLOAS)
def test_blocks_of_the_case(fork: str, path: str) -> None:
    blocks = _blocks(fork, path)
    nodes = _fork_choice(fork, path)["fork_choice_nodes"]
    assert {node["block_root"] for node in nodes} == set(blocks)
    anchor = _last_check(fork, path, "head", first=True)["root"]
    for node in nodes:
        slot, parent = blocks[node["block_root"]]
        assert node["slot"] == str(slot)
        if fork != "gloas" or node["payload_status"] == "pending":
            assert node["parent_root"] == parent
            # Only the anchor has a parent outside the store.
            assert (node["parent_payload_status"] is None) == (node["block_root"] == anchor)


@pytest.mark.parametrize(("fork", "path"), PRE_GLOAS)
def test_heads_are_the_blocks_without_children_before_gloas(fork: str, path: str) -> None:
    blocks = _blocks(fork, path)
    parents = {parent for _, parent in blocks.values()}
    assert {entry["root"] for entry in _heads(fork, path)} == set(blocks) - parents


def test_weights_lead_to_the_head() -> None:
    # Before Gloas the head is the heaviest child at each step, ties broken by the greater root.
    fork, path = PRE_GLOAS[0]
    nodes = _fork_choice(fork, path)["fork_choice_nodes"]
    node = _last_check(fork, path, "justified_checkpoint")["root"]
    while children := [child for child in nodes if child["parent_root"] == node]:
        node = max(children, key=lambda child: (int(child["weight"]), child["block_root"]))[
            "block_root"
        ]
    assert node == _last_check(fork, path, "head")["root"]
    # The votes of the case weigh some nodes, so the walk does not follow the roots alone.
    assert any(int(child["weight"]) > 0 for child in nodes)


@pytest.mark.parametrize(("fork", "path"), PRE_GLOAS)
def test_one_full_node_per_block_before_gloas(fork: str, path: str) -> None:
    nodes = _fork_choice(fork, path)["fork_choice_nodes"]
    roots = [node["block_root"] for node in nodes]
    assert len(set(roots)) == len(roots)
    assert {node["payload_status"] for node in nodes} == {"full"}
    assert {node["parent_payload_status"] for node in nodes} == {"full", None}
    assert {_counts(node) for node in nodes} == {(0, 0, 0)}


@pytest.mark.parametrize(("fork", "path"), GLOAS)
def test_nodes_of_a_gloas_block(fork: str, path: str) -> None:
    nodes = _fork_choice(fork, path)["fork_choice_nodes"]
    by_block: dict[str, list[dict[str, Any]]] = {}
    for node in nodes:
        by_block.setdefault(node["block_root"], []).append(node)
    # A block has a full node exactly when its payload arrived in a valid step.
    steps = _load(_case(fork, path) / "steps.yaml")
    payloads = sum("execution_payload" in step and step.get("valid", True) for step in steps)
    assert sum(node["payload_status"] == "full" for node in nodes) == payloads
    for views in by_block.values():
        statuses = sorted(view["payload_status"] for view in views)
        assert statuses in (["empty", "pending"], ["empty", "full", "pending"])
        # The counts are those of the block, the same for each of its nodes.
        counts = {_counts(view) for view in views}
        assert len(counts) == 1
        attesters, timely, available = counts.pop()
        assert timely <= attesters <= PTC_SIZE
        assert available <= PTC_SIZE


@pytest.mark.parametrize(("fork", "path"), VOTES)
def test_counts_of_the_recorded_votes(fork: str, path: str) -> None:
    timeliness = _last_check(fork, path, "payload_timeliness_vote")
    availability = _last_check(fork, path, "payload_data_availability_vote")
    assert timeliness["block_root"] == availability["block_root"]
    assert len(timeliness["votes"]) == len(availability["votes"]) == PTC_SIZE
    expected = (
        sum(vote is not None for vote in timeliness["votes"]),
        sum(vote is True for vote in timeliness["votes"]),
        sum(vote is True for vote in availability["votes"]),
    )
    assert expected[0] > 0
    nodes = _fork_choice(fork, path)["fork_choice_nodes"]
    views = [node for node in nodes if node["block_root"] == timeliness["block_root"]]
    assert len(views) >= 2
    assert {_counts(view) for view in views} == {expected}


def test_full_node_after_its_payload() -> None:
    fork, path = ENVELOPE
    head = _last_check(fork, path, "head")
    nodes = {_key(node): node for node in _fork_choice(fork, path)["fork_choice_nodes"]}
    full, empty, pending = (nodes[head["root"], status] for status in ("full", "empty", "pending"))
    assert full["slot"] == empty["slot"] == pending["slot"] == str(head["slot"])
    # The full node ends at the payload of the block, the others at the payload it builds on.
    assert empty["execution_block_hash"] == pending["execution_block_hash"]
    assert full["execution_block_hash"] != pending["execution_block_hash"]


@pytest.mark.parametrize(("fork", "path"), PRE_GLOAS + GLOAS)
def test_head_is_a_chain_head(fork: str, path: str) -> None:
    head = _last_check(fork, path, "head")
    heads = _heads(fork, path)
    roots = [entry["root"] for entry in heads]
    assert len(set(roots)) == len(roots)
    assert {"root": head["root"], "slot": str(head["slot"]), "execution_optimistic": False} in heads


def test_gloas_heads_are_blocks_with_a_leaf() -> None:
    # The anchor is built on through its empty node, and the block after it has two leaves.
    fork, path = ENVELOPE
    head = _last_check(fork, path, "head")
    assert _heads(fork, path) == [
        {"root": head["root"], "slot": str(head["slot"]), "execution_optimistic": False}
    ]


@pytest.mark.parametrize(("fork", "path"), [*PRE_GLOAS, ENVELOPE])
def test_optimistic_head(fork: str, path: str) -> None:
    head = _last_check(fork, path, "head")
    optimistic = [_hex(head["root"])]
    heads = _heads(fork, path, optimistic)
    flags = [entry["execution_optimistic"] for entry in heads if entry["root"] == head["root"]]
    assert flags == [True]
    nodes = _fork_choice(fork, path, optimistic)["fork_choice_nodes"]
    # Only the node that ends at the payload of the head block is optimistic.
    assert {_key(node) for node in nodes if node["validity"] == "optimistic"} == {
        (head["root"], "full")
    }
