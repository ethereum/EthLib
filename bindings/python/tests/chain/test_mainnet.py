"""The active fork of mainnet at the boundaries that the meta EIPs give."""

import pytest

from ethlib.chain import mainnet_active_fork

# The first block of each fork by block number, with the fork before it.
# EIP-6953 "Proof-of-Work Network Upgrades" lists Homestead to Gray Glacier.
# EIP-1716 makes Petersburg active where Constantinople activates at the same block.
# Paris starts at the first block after the pre-merge history of EIP-7643 "Pre-PoS Root".
BLOCKS = [
    (1_150_000, "frontier", "homestead"),
    (1_920_000, "homestead", "daoFork"),
    (2_463_000, "daoFork", "tangerineWhistle"),
    (2_675_000, "tangerineWhistle", "spuriousDragon"),
    (4_370_000, "spuriousDragon", "byzantium"),
    (7_280_000, "byzantium", "petersburg"),
    (9_069_000, "petersburg", "istanbul"),
    (9_200_000, "istanbul", "muirGlacier"),
    (12_244_000, "muirGlacier", "berlin"),
    (12_965_000, "berlin", "london"),
    (13_773_000, "london", "arrowGlacier"),
    (15_050_000, "arrowGlacier", "grayGlacier"),
    (15_537_394, "grayGlacier", "paris"),
]

# The first timestamp of each fork by time, with the fork before it.
# EIP-6953 "Post-Merge Upgrades" gives Shapella, and the "Activation" table of each meta EIP the
# others: EIP-7569, EIP-7600, EIP-7607 (with BPO1 and BPO2), EIP-8134 and EIP-8135.
TIMES = [
    (1_681_338_455, "paris", "shapella"),
    (1_710_338_135, "shapella", "dencun"),
    (1_746_612_311, "dencun", "pectra"),
    (1_764_798_551, "pectra", "fusaka"),
    (1_765_290_071, "fusaka", "bpo1"),
    (1_767_747_671, "bpo1", "bpo2"),
]

# A block number past Paris, for the forks by time.
AFTER_PARIS = 20_000_000


def test_genesis_is_frontier() -> None:
    assert mainnet_active_fork(0, 0) == "frontier"


@pytest.mark.parametrize("number, before, fork", BLOCKS)
def test_block_boundary(number: int, before: str, fork: str) -> None:
    assert mainnet_active_fork(number - 1, 0) == before
    assert mainnet_active_fork(number, 0) == fork


@pytest.mark.parametrize("timestamp, before, fork", TIMES)
def test_time_boundary(timestamp: int, before: str, fork: str) -> None:
    assert mainnet_active_fork(AFTER_PARIS, timestamp - 1) == before
    assert mainnet_active_fork(AFTER_PARIS, timestamp) == fork


def test_constantinople_is_never_active() -> None:
    assert mainnet_active_fork(7_280_000, 0) == "petersburg"


def test_largest_inputs() -> None:
    assert mainnet_active_fork(2**64 - 1, 2**64 - 1) == "bpo2"


@pytest.mark.parametrize("number, timestamp", [(-1, 0), (0, 2**64)])
def test_out_of_range(number: int, timestamp: int) -> None:
    with pytest.raises(OverflowError):
        mainnet_active_fork(number, timestamp)
