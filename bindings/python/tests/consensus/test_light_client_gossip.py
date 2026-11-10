"""Gossip validation of light client updates, on the updates of a consensus-specs sync case."""

from pathlib import Path

import pytest

from ethlib import consensus
from raising import raises

from .test_light_client_sync import _YAML, FILES, _hex, _read, case_config

# An Altair sync case whose updates finalize, then attest, ever later slots.
CASE = FILES / "minimal" / "altair" / "light_client" / "sync" / "pyspec_tests" / "light_client_sync"

FINALITY = "light_client_finality_update"
OPTIMISTIC = "light_client_optimistic_update"

# Minimal slots last 6000 ms, and sync messages are due 3333 basis points in, at 1999 ms.
SLOT_MS = 6000
DUE_MS = 1999
DISPARITY_MS = 500

# The offset of the sync committee bits in an Altair update of the minimal preset.
# The attested header, the next committee and its branch come first.
# The finalized header and its branch of six roots follow; 32 members take 4 bytes.
BITS_OFFSET = 112 + (32 * 48 + 48) + 5 * 32 + 112 + 6 * 32
COMMITTEE_SIZE = 32

VALID = ("valid", None)
NOT_NEWER = ("ignore", "finality update is not newer than a forwarded one")
EARLY = ("ignore", "finality update arrived before the sync messages were due")
DIFFERS = ("ignore", "finality update differs from the local one")
OPTIMISTIC_NOT_NEWER = ("ignore", "optimistic update is not newer than a forwarded one")


def on_time(slot: int) -> int:
    """The first time in ms at which the sync messages of a slot are due, with the disparity."""
    return slot * SLOT_MS + DUE_MS - DISPARITY_MS


def with_signers(update: bytes, count: int) -> bytes:
    """An update whose sync committee bits mark the first members, as many as the count."""
    bits = ((1 << count) - 1).to_bytes(COMMITTEE_SIZE // 8, "little")
    return update[:BITS_OFFSET] + bits + update[BITS_OFFSET + len(bits) :]


def finality(update: bytes) -> bytes:
    """The finality update that a light client update gives."""
    return consensus.light_client_update_as(
        "minimal", "altair", "LightClientFinalityUpdate", update
    )


def optimistic(update: bytes) -> bytes:
    """The optimistic update that a light client update gives."""
    return consensus.light_client_update_as(
        "minimal", "altair", "LightClientOptimisticUpdate", update
    )


class Case:
    """The bootstrap, the roots and the updates of the sync case, with the slot of each."""

    def __init__(self, case: Path) -> None:
        meta = _YAML.load((case / "meta.yaml").read_text())
        steps = _YAML.load((case / "steps.yaml").read_text())
        _, self.config = case_config(case, "minimal")
        self.trusted = _hex(meta["trusted_block_root"])
        self.root = _hex(meta["genesis_validators_root"])
        self.bootstrap = _read(case, "bootstrap")
        processed = [step["process_update"] for step in steps if "process_update" in step]
        self.updates = [_read(case, step["update"]) for step in processed]
        self.slots = [step["current_slot"] for step in processed]

    def time(self, index: int) -> int:
        """A time in the slot at which the case processes an update, once sync messages are due."""
        return on_time(self.slots[index])

    def full_node(
        self, messages: list[tuple[str, int, bytes, bytes | None]]
    ) -> list[consensus.GossipOutcome]:
        """The outcomes of messages at a full node."""
        return consensus.light_client_gossip_full_node(
            "minimal", "altair", 0, messages, self.config
        )

    def light_client(self, messages: list[tuple[str, int, bytes]]) -> list[consensus.GossipOutcome]:
        """The outcomes of messages at a light client that starts from the bootstrap."""
        return consensus.light_client_gossip_light_client(
            "minimal",
            "altair",
            0,
            self.trusted,
            self.root,
            self.bootstrap,
            messages,
            config=self.config,
        )


@pytest.fixture(scope="module")
def case() -> Case:
    return Case(CASE)


def test_case_layout(case):
    # The tests read the first two updates, which finalize two different slots.
    first, second = case.updates[:2]
    assert len(finality(first)) == 112 + 112 + 6 * 32 + COMMITTEE_SIZE // 8 + 96 + 8
    assert finality(first) != finality(second)
    # The bits sit where the tests rewrite them: all 32 members of the first update signed.
    assert with_signers(first, COMMITTEE_SIZE) == first


def test_full_node_forwards_only_the_update_of_its_latest_update(case):
    first, second = case.updates[:2]
    time = case.time(1)
    assert case.full_node(
        [
            (FINALITY, time, finality(first), first),
            (FINALITY, time, finality(first), first),
            (FINALITY, time, finality(second), first),
            (FINALITY, time, finality(second), None),
            (FINALITY, time, finality(second), second),
        ]
    ) == [VALID, NOT_NEWER, DIFFERS, DIFFERS, VALID]


def test_full_node_waits_for_the_sync_message_deadline(case):
    first = case.updates[0]
    slot = case.slots[0]
    assert case.full_node(
        [
            (FINALITY, on_time(slot) - 1, finality(first), first),
            (FINALITY, on_time(slot), finality(first), first),
        ]
    ) == [EARLY, VALID]


def test_full_node_supermajority_at_the_same_finalized_slot(case):
    # 21 of 32 members is not more than two thirds, and 22 is.
    time = case.time(0)
    low, other, high, full = (with_signers(case.updates[0], n) for n in (20, 21, 22, 32))
    assert case.full_node(
        [(FINALITY, time, finality(best), best) for best in (low, other, high, full)]
    ) == [VALID, NOT_NEWER, VALID, NOT_NEWER]


def test_full_node_optimistic_updates(case):
    first, second = case.updates[:2]
    time = case.time(1)
    assert case.full_node(
        [
            (OPTIMISTIC, time, optimistic(first), first),
            (OPTIMISTIC, time, optimistic(first), first),
            (OPTIMISTIC, time, optimistic(second), first),
            (OPTIMISTIC, case.slots[1] * SLOT_MS, optimistic(second), second),
            (OPTIMISTIC, time, optimistic(second), second),
        ]
    ) == [
        VALID,
        OPTIMISTIC_NOT_NEWER,
        ("ignore", "optimistic update differs from the local one"),
        ("ignore", "optimistic update arrived before the sync messages were due"),
        VALID,
    ]


def test_light_client_rejects_an_update_that_its_store_refuses(case):
    first = finality(case.updates[0])
    # The last byte of the aggregate signature flips, just before the 8 bytes of the slot.
    end = len(first) - 8
    forged = first[: end - 1] + bytes([first[end - 1] ^ 1]) + first[end:]
    assert case.light_client(
        [
            (FINALITY, case.time(0), forged),
            (FINALITY, case.time(0), first),
            (FINALITY, case.time(0), first),
        ]
    ) == [("reject", "finality update is invalid"), VALID, NOT_NEWER]


def test_light_client_rejects_an_update_of_an_unknown_period(case):
    # The second update is signed in the next period, whose committee the store does not know.
    assert case.light_client([(FINALITY, case.time(1), finality(case.updates[1]))]) == [
        ("reject", "finality update is invalid")
    ]


def test_light_client_optimistic_updates(case):
    first = optimistic(case.updates[0])
    assert case.light_client(
        [(OPTIMISTIC, case.time(0), first), (OPTIMISTIC, case.time(0), first)]
    ) == [VALID, OPTIMISTIC_NOT_NEWER]


def test_light_client_optimistic_update_repeats_the_finality_update(case):
    # Processing the finality update moves the optimistic header to its attested header.
    # The optimistic update then advances nothing, but it repeats the forwarded finality update.
    first = case.updates[0]
    assert case.light_client(
        [(FINALITY, case.time(0), finality(first)), (OPTIMISTIC, case.time(0), optimistic(first))]
    ) == [VALID, VALID]


def test_light_client_optimistic_update_that_advances_nothing(case):
    # The early finality update is ignored, so nothing is forwarded.
    # The store still processes it, so the optimistic update then advances nothing.
    first = case.updates[0]
    assert case.light_client(
        [
            (FINALITY, case.time(0) - 1, finality(first)),
            (OPTIMISTIC, case.time(0), optimistic(first)),
        ]
    ) == [
        EARLY,
        (
            "ignore",
            "optimistic update neither repeats the finality update nor advances the optimistic"
            " header",
        ),
    ]


def test_light_client_ignores_a_finality_update_that_finalizes_nothing_new(case):
    # The store processes the early update, so the same update on time finalizes nothing new.
    first = finality(case.updates[0])
    assert case.light_client(
        [(FINALITY, case.time(0) - 1, first), (FINALITY, case.time(0), first)]
    ) == [EARLY, ("ignore", "finality update does not advance the finalized header")]


def test_unknown_topic(case):
    with raises(consensus.LightClientError, "no light client topic is named beacon_block"):
        case.full_node([("beacon_block", 0, b"", None)])
