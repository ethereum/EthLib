"""The difficulty before Paris against the difficulty tests of ethereum/tests."""

import json
from pathlib import Path

import pytest

from ethlib.errors import BlockError
from ethlib.execution.pow import block_difficulty

# The vendored files sit next to this module.
_DIR = Path(__file__).resolve().parent / "difficulty"

# The fork name of each file's top-level key, as EthLib spells it.
#
# The files of EIP-2384 run its delay at Berlin, which keeps the delay of Muir Glacier.
_FORKS = {
    "Frontier": "frontier",
    "Homestead": "homestead",
    "Byzantium": "byzantium",
    "Constantinople": "constantinople",
    "Berlin": "berlin",
    "ArrowGlacier": "arrowGlacier",
    "GrayGlacier": "grayGlacier",
}


def _cases() -> list[tuple[str, str, dict]]:
    """The (case id, fork, case) triples of every file."""
    cases = []
    for path in sorted(_DIR.glob("*.json")):
        for group in json.loads(path.read_text()).values():
            for key, tests in group.items():
                if key == "_info":
                    continue
                for name, case in tests.items():
                    cases.append((f"{path.stem}/{name}", _FORKS[key], case))
    return cases


_CASES = _cases()

# Invariant: the 17 files of the pinned commit hold 18,598 cases.
assert len(_CASES) == 18598, len(_CASES)


@pytest.mark.parametrize(
    "fork, case", [(f, c) for _, f, c in _CASES], ids=[i for i, _, _ in _CASES]
)
def test_difficulty(fork: str, case: dict) -> None:
    def n(key: str) -> int:
        return int(case[key], 16)

    difficulty = block_difficulty(
        fork,
        n("currentBlockNumber"),
        n("currentTimestamp"),
        n("parentTimestamp"),
        n("parentDifficulty"),
        n("parentUncles"),
    )
    assert difficulty == n("currentDifficulty")


def test_paris_is_zero() -> None:
    # From Paris on, EIP-3675 sets the difficulty to 0, whatever the parent.
    assert block_difficulty("paris", 15_537_394, 1_663_224_179, 1_663_224_162, 10**16, 0) == 0


def test_unknown_fork() -> None:
    # A name that is not a fork of the timeline fails before any arithmetic.
    with pytest.raises(BlockError):
        block_difficulty("ropsten", 1, 2, 1, 131072, 0)


def test_negative_quantity() -> None:
    with pytest.raises(OverflowError):
        block_difficulty("homestead", -1, 2, 1, 131072, 0)
