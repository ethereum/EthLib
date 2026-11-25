"""The active fork of Hoodi at the boundaries that its genesis file and the meta EIPs give."""

import pytest

from ethlib.chain import ChainError, hoodi_active_fork
from raising import raises

# The genesis file activates every fork up to London at block 0.
# It activates Shapella and Dencun at time 0, so Hoodi starts at Dencun.
#
# File: metadata/genesis.json
# Repository: eth-clients/hoodi
# Commit: 2a7efb3c530cce7c71702cc98d0f965df2411c11
GENESIS_TIME = 1_742_212_800

# The first timestamp of each later fork, with the fork before it.
# The "Activation" tables of EIP-7600 and EIP-7607 give them.
# EIP-7607 gives BPO1 and BPO2 under "Blob Parameter Only Forks".
#
# Repository: ethereum/EIPs
# Commit: b055feec322fbc37e9d77a393a50b3ff56b31c92
TIMES = [
    (1_742_999_832, "dencun", "pectra"),
    (1_761_677_592, "pectra", "fusaka"),
    (1_762_365_720, "fusaka", "bpo1"),
    (1_762_955_544, "bpo1", "bpo2"),
]

# The start of epoch 132352, the Glamsterdam time that EIP-7773 once gave Hoodi.
# At the pinned commit, the Hoodi row of its "Activation" table is empty.
# The genesis file gives no Glamsterdam time either.
UNSCHEDULED_GLAMSTERDAM = 1_793_036_568


def test_genesis_is_dencun() -> None:
    assert hoodi_active_fork(0, GENESIS_TIME) == "dencun"
    assert hoodi_active_fork(0, 0) == "dencun"


@pytest.mark.parametrize("timestamp, before, fork", TIMES)
def test_time_boundary(timestamp: int, before: str, fork: str) -> None:
    assert hoodi_active_fork(1, timestamp - 1) == before
    assert hoodi_active_fork(1, timestamp) == fork


def test_bpo2_is_last() -> None:
    """No fork follows BPO2, at the old Glamsterdam time or after."""
    assert hoodi_active_fork(1, UNSCHEDULED_GLAMSTERDAM - 1) == "bpo2"
    assert hoodi_active_fork(1, UNSCHEDULED_GLAMSTERDAM) == "bpo2"
    assert hoodi_active_fork(1, 2**64 - 1) == "bpo2"


def test_timestamp_out_of_range() -> None:
    """A timestamp of 2^64 is not a 64-bit number, so it fails with code 0."""
    with raises(ChainError, f"expected an int below {2**64}, got {2**64}") as error:
        hoodi_active_fork(0, 2**64)
    assert error.value.code == 0
