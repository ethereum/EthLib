"""The order of forks by block and by time that EIP-6122 requires of a chain configuration."""

from ethlib.chain import ChainError, active_fork
from raising import raises


def test_block_fork_after_time_fork() -> None:
    """London by block after Berlin by time breaks EIP-6122, so the configuration is rejected."""
    config = {
        "chainId": 1,
        "depositContractAddress": bytes(20),
        "activations": [["berlin", "time", 0], ["london", "block", 0]],
    }
    with raises(ChainError, "config: a fork by block comes after a fork by time") as error:
        active_fork(config, 0, 0)
    assert error.value.code == 0


def test_time_fork_after_block_fork() -> None:
    """Shapella by time after Paris by block follows EIP-6122, and Shapella is active at time 0."""
    config = {
        "chainId": 1,
        "depositContractAddress": bytes(20),
        "activations": [["paris", "block", 0], ["shapella", "time", 0]],
    }
    assert active_fork(config, 0, 0) == "shapella"
