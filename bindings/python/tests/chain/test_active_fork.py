"""The active fork of a configured chain, on small configurations whose answers follow by hand."""

import pytest

from ethlib.chain import ChainError, active_fork
from raising import raises

# Frontier to Paris at block 0, then Shapella from time 100 and Dencun from time 200.
TIMED = {
    "chainId": 1,
    "activations": [
        ["frontier", "block", 0],
        ["london", "block", 0],
        ["paris", "block", 0],
        ["shapella", "time", 100],
        ["dencun", "time", 200],
    ],
}

# Byzantium at block 0, then Constantinople and Petersburg together at block 10.
SHARED = {
    "chainId": 1,
    "activations": [
        ["byzantium", "block", 0],
        ["constantinople", "block", 10],
        ["petersburg", "block", 10],
    ],
}


@pytest.mark.parametrize(
    "timestamp, fork",
    [(0, "paris"), (99, "paris"), (100, "shapella"), (199, "shapella"), (200, "dencun")],
)
def test_time_boundaries(timestamp: int, fork: str) -> None:
    """A fork by time is active from its timestamp on, and the one before it until then."""
    assert active_fork(TIMED, 1, timestamp) == fork


def test_two_forks_at_one_block() -> None:
    """Of two forks at one block, the later one in the timeline is active, as EIP-1716 asks."""
    assert active_fork(SHARED, 9, 0) == "byzantium"
    assert active_fork(SHARED, 10, 0) == "petersburg"


def test_no_activation_reached() -> None:
    """A block before every activation has no active fork."""
    config = {"chainId": 1, "activations": [["homestead", "block", 5]]}
    assert active_fork(config, 4, 0) is None


def test_unknown_activation_kind() -> None:
    """An activation that is neither by block nor by time is malformed, with code 0."""
    config = {"chainId": 1, "activations": [["paris", "slot", 0]]}
    with raises(ChainError, "no activation kind slot") as error:
        active_fork(config, 0, 0)
    assert error.value.code == 0


def test_activations_as_tuples() -> None:
    """An activation given as a tuple reads as one given as a list."""
    config = {"chainId": 1, "activations": [("frontier", "block", 0), ("homestead", "block", 5)]}
    assert active_fork(config, 5, 0) == "homestead"


@pytest.mark.parametrize("number, timestamp", [(2**64, 0), (0, 2**64)])
def test_number_out_of_range(number: int, timestamp: int) -> None:
    """A block number or a timestamp of 2^64 is not a 64-bit number, so it fails with code 0."""
    message = f"expected an int below {2**64}, got {2**64}"
    with raises(ChainError, message) as error:
        active_fork(TIMED, number, timestamp)
    assert error.value.code == 0


def test_negative_number() -> None:
    """A negative block number never reaches Lean."""
    with raises(ValueError, "cannot pass a negative int to Lean"):
        active_fork(TIMED, -1, 0)


def test_bool_is_not_a_number() -> None:
    """A bool is not read as a block number, and fails with code 0."""
    with raises(ChainError, "expected an int") as error:
        active_fork(TIMED, True, 0)
    assert error.value.code == 0
