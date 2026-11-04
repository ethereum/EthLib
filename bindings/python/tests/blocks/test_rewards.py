"""Mining rewards against the blockchain tests of execution-specs, from Frontier to Paris."""

import json
from pathlib import Path

import pytest

from ethlib.serialization import rlp
from ethlib.state import rewards_root, state_root

from .test_blocks import FORK_OF_NETWORK
from .test_withdrawals import _state

_CASES_FILE = Path(__file__).resolve().parents[4] / "tests" / "execution" / "blocks" / "rewards.json"
CASES = json.loads(_CASES_FILE.read_text())


@pytest.mark.parametrize("case", CASES, ids=[f"{c['network']}-{c['test'][-60:]}" for c in CASES])
def test_reward_post_state(case) -> None:
    state = _state(case["pre"])
    # The state before the block has the root of the genesis header.
    assert state_root(state) == bytes.fromhex(case["preStateRoot"])
    # A block with no transaction changes only its miner's balance, by the reward.
    fork = FORK_OF_NETWORK[case["network"]]
    root = rewards_root(fork, state, bytes.fromhex(case["rlp"]))
    assert root == bytes.fromhex(case["postStateRoot"])


def test_cases_cover_every_fork_and_reward() -> None:
    # Each reward of 5, 3, 2 and 0 ether appears, through the forks from Frontier to Paris.
    networks = {c["network"] for c in CASES}
    assert {"Frontier", "Byzantium", "ConstantinopleFix", "Paris"} <= networks
    assert len(networks) == 10


def test_paris_pays_no_reward() -> None:
    case = next(c for c in CASES if c["network"] == "Paris")
    state = _state(case["pre"])
    assert rewards_root("paris", state, bytes.fromhex(case["rlp"])) == state_root(state)


def test_reward_depends_on_the_fork() -> None:
    # The same Frontier block pays 5 ether at Frontier, and 3 at Byzantium.
    case = next(c for c in CASES if c["network"] == "Frontier")
    state = _state(case["pre"])
    block = bytes.fromhex(case["rlp"])
    assert rewards_root("frontier", state, block) != rewards_root("byzantium", state, block)
    assert len(rlp.decode(block)[2]) == 0
