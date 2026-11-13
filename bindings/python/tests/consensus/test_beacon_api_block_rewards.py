"""The Beacon API block rewards, on the blocks of the pinned random, finality and sanity vectors."""

from functools import cache
from math import isqrt
from pathlib import Path
from typing import Any

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS
from .test_transition import FILES

# The groups whose cases hold blocks of one fork.
GROUPS = ("random/random", "finality/finality", "sanity/blocks")

# The forks whose blocks carry their withdrawals, so a test sees what the proposer withdrew.
# From Gloas the withdrawals come from the state, and the balance check stops there.
BALANCE_FORKS = ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu")

# The Altair incentive weights: the sync reward and the proposer share of each signature.
SYNC_REWARD_WEIGHT = 2
PROPOSER_WEIGHT = 8
WEIGHT_DENOMINATOR = 64

PARTS = ("attestations", "sync_aggregate", "proposer_slashings", "attester_slashings")


def _cases() -> list:
    """Every vendored case of the groups that has a post state, as its fork and directory."""
    return [
        pytest.param(post.parent.relative_to(FILES).parts[1], post.parent, id=str(post.parent))
        for group in GROUPS
        for post in sorted(FILES.glob(f"minimal/*/{group}/pyspec_tests/*/post.ssz_snappy"))
    ]


def _read(path: Path) -> bytes:
    return snappy.decompress(path.read_bytes())


def _json(fork: str, kind: str, data: bytes) -> dict[str, Any]:
    return consensus.api_json("minimal", FORKS[fork], kind, data)


def _participant_reward(state: dict[str, Any]) -> int:
    """The sync participant reward of a slot, computed from the active balance of a state."""
    preset = consensus.preset("minimal")
    increment = preset["EFFECTIVE_BALANCE_INCREMENT"]
    epoch = int(state["slot"]) // preset["SLOTS_PER_EPOCH"]
    active = sum(
        int(validator["effective_balance"])
        for validator in state["validators"]
        if int(validator["activation_epoch"]) <= epoch < int(validator["exit_epoch"])
    )
    total = max(increment, active)
    per_increment = increment * preset["BASE_REWARD_FACTOR"] // isqrt(total)
    weighted = per_increment * (total // increment) * SYNC_REWARD_WEIGHT // WEIGHT_DENOMINATOR
    return weighted // preset["SLOTS_PER_EPOCH"] // preset["SYNC_COMMITTEE_SIZE"]


def _credited(fork: str, state: dict[str, Any], body: dict[str, Any], proposer: int) -> bool:
    """Whether a block may change the proposer's balance other than by its rewards."""
    pubkey = state["validators"][proposer]["pubkey"]
    slashed = {
        int(slashing["signed_header_1"]["message"]["proposer_index"])
        for slashing in body["proposer_slashings"]
    } | {
        int(index)
        for slashing in body["attester_slashings"]
        for index in slashing["attestation_1"]["attesting_indices"]
        if index in slashing["attestation_2"]["attesting_indices"]
    }
    requests = body.get("execution_requests", {})
    seated = fork != "phase0" and pubkey in state["current_sync_committee"]["pubkeys"]
    return bool(
        proposer in slashed
        or any(deposit["data"]["pubkey"] == pubkey for deposit in body["deposits"])
        or any(request["source_pubkey"] == pubkey for request in requests.get("consolidations", []))
        or seated
    )


@cache
def _blocks(fork: str, case: Path) -> list[tuple[bytes, bytes, dict[str, Any], bytes]]:
    """Each block of a case: the state at its slot, the block, its rewards and the state after."""
    meta = YAML(typ="safe").load((case / "meta.yaml").read_text())
    verify = meta.get("bls_setting", 0) != 2
    state = _read(case / "pre.ssz_snappy")
    blocks = []
    for index in range(meta["blocks_count"]):
        block = _read(case / f"blocks_{index}.ssz_snappy")
        slot = int(_json(fork, "SignedBeaconBlock", block)["message"]["slot"])
        gap = slot - int(_json(fork, "BeaconState", state)["slot"])
        at_slot = consensus.process_slots("minimal", FORKS[fork], state, gap) if gap else state
        rewards = consensus.api_block_rewards("minimal", FORKS[fork], at_slot, block)["data"]
        state = consensus.state_transition("minimal", FORKS[fork], state, block, verify)
        blocks.append((at_slot, block, rewards, state))
    return blocks


@pytest.mark.parametrize("fork, case", _cases())
def test_rewards_of_each_block(fork, case):
    for at_slot, block, rewards, after in _blocks(fork, case):
        message = _json(fork, "SignedBeaconBlock", block)["message"]
        state = _json(fork, "BeaconState", at_slot)
        proposer = int(message["proposer_index"])
        assert int(rewards["proposer_index"]) == proposer
        assert int(rewards["total"]) == sum(int(rewards[part]) for part in PARTS)
        if fork == "phase0":
            # Before Altair the attestations pay their proposer at the end of the epoch.
            assert rewards["attestations"] == rewards["sync_aggregate"] == "0"
        else:
            bits = bytes.fromhex(message["body"]["sync_aggregate"]["sync_committee_bits"][2:])
            signatures = sum(bin(byte).count("1") for byte in bits)
            share = _participant_reward(state) * PROPOSER_WEIGHT
            share //= WEIGHT_DENOMINATOR - PROPOSER_WEIGHT
            assert int(rewards["sync_aggregate"]) == share * signatures
        if fork in BALANCE_FORKS and not _credited(fork, state, message["body"], proposer):
            payload = message["body"].get("execution_payload", {})
            withdrawn = sum(
                int(withdrawal["amount"])
                for withdrawal in payload.get("withdrawals", [])
                if int(withdrawal["validator_index"]) == proposer
            )
            before = int(state["balances"][proposer])
            later = int(_json(fork, "BeaconState", after)["balances"][proposer])
            # Only the rewards and the withdrawals of the block move the proposer's balance.
            assert later - before == int(rewards["total"]) - withdrawn


def test_balance_checked_with_rewards():
    # Some blocks that the balance check covers pay their proposer for attestations and signatures.
    checked = [
        rewards
        for fork, case in (param.values for param in _cases())
        if fork in BALANCE_FORKS
        for at_slot, block, rewards, _ in _blocks(fork, case)
        if not _credited(
            fork,
            _json(fork, "BeaconState", at_slot),
            _json(fork, "SignedBeaconBlock", block)["message"]["body"],
            int(rewards["proposer_index"]),
        )
    ]
    assert any(int(rewards["attestations"]) > 0 for rewards in checked)
    assert any(int(rewards["sync_aggregate"]) > 0 for rewards in checked)


def test_block_of_another_slot():
    fork, case = _cases()[0].values
    block = _read(case / "blocks_0.ssz_snappy")
    state = _read(case / "pre.ssz_snappy")
    slot = int(_json(fork, "SignedBeaconBlock", block)["message"]["slot"])
    at_slot = consensus.process_slots(
        "minimal", FORKS[fork], state, slot + 1 - int(_json(fork, "BeaconState", state)["slot"])
    )
    # The block does not apply to a state past its slot, which gives code 500.
    with raises(
        consensus.ConsensusError,
        f"Internal error: EthLib.Consensus.TransitionError.slotMismatch {slot} {slot + 1}",
    ) as info:
        consensus.api_block_rewards("minimal", FORKS[fork], at_slot, block)
    assert info.value.code == 500


@pytest.mark.parametrize("fork, case", _cases())
def test_consensus_block_value(fork, case):
    # The block production endpoints give the proposer's rewards of the block in Wei.
    for at_slot, block, rewards, _ in _blocks(fork, case):
        value = consensus.api_consensus_block_value("minimal", FORKS[fork], at_slot, block)
        assert value == int(rewards["total"]) * 10**9
