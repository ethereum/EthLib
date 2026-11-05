"""The base fee and the blob base fee against values worked by hand from their EIPs."""

import pytest

from ethlib.errors import FeesError
from ethlib.execution.fees import (
    calc_excess_blob_gas,
    calculate_base_fee_per_gas,
    fake_exponential,
    get_base_fee_per_blob_gas,
)
from raising import raises


@pytest.mark.parametrize(
    "gas_limit, gas_used, base_fee, expected",
    [
        # A parent at its target of 15,000,000 keeps the base fee.
        (30_000_000, 15_000_000, 10**10, 10**10),
        # A full parent: 10^10 * 15000000 / 15000000 / 8 = 1250000000 more.
        (30_000_000, 30_000_000, 10**10, 11_250_000_000),
        # An empty parent: the same amount less.
        (30_000_000, 0, 10**10, 8_750_000_000),
        # 5,000,000 above the target: 10^10 * 5000000 / 15000000 = 3333333333,
        # and / 8 gives 416666666.
        (30_000_000, 20_000_000, 10**10, 10_416_666_666),
        # 5,000,000 below the target: the fall is the same 416666666.
        (30_000_000, 10_000_000, 10**10, 9_583_333_334),
        # One unit above the target, the rise rounds down to 0, and the minimum rise is 1.
        (30_000_000, 15_000_001, 7, 8),
        # One unit below the target, the fall rounds down to 0.
        (30_000_000, 14_999_999, 7, 7),
        # An odd gas limit: 120000000 * 15000001 / 15000000 / 8 = 15000001.
        (30_000_001, 30_000_001, 120_000_000, 135_000_001),
        # A target of 0 and x / 0 = 0 make the rise the minimum, 1.
        (1, 1, 100, 101),
    ],
)
def test_base_fee(gas_limit: int, gas_used: int, base_fee: int, expected: int) -> None:
    assert calculate_base_fee_per_gas(gas_limit, gas_used, base_fee) == expected


@pytest.mark.parametrize(
    "factor, numerator, denominator, expected",
    [
        # Each case lists the accumulators of the loop of EIP-4844, which add up to the output.
        (1, 0, 5007716, 1),  # 5007716, then 0
        (1, 1, 1, 2),  # 1, 1, then 0
        (1, 2, 1, 6),  # 1, 2, 2, 1, then 0
        (1, 3, 1, 16),  # 1, 3, 4, 4, 3, 1, then 0
        (1, 4, 2, 6),  # 2, 4, 4, 2, 1, then 0, and 13 // 2 = 6
        (10, 8, 2, 542),  # 20, 80, 160, 213, 213, 170, 113, 64, 32, 14, 5, 1, and 1085 // 2
    ],
)
def test_fake_exponential(factor: int, numerator: int, denominator: int, expected: int) -> None:
    assert fake_exponential(factor, numerator, denominator) == expected


@pytest.mark.parametrize(
    "fork, excess, expected",
    [
        # No excess gives the minimum, 1.
        ("dencun", 0, 1),
        # An excess equal to the update fraction gives about e, rounded down to 2.
        # The fraction is 3338477 at Dencun (EIP-4844), and 5007716 from Pectra (EIP-7691).
        ("dencun", 3338477, 2),
        ("fusaka", 5007716, 2),
    ],
)
def test_base_fee_per_blob_gas(fork: str, excess: int, expected: int) -> None:
    assert get_base_fee_per_blob_gas(fork, excess) == expected


@pytest.mark.parametrize(
    "excess, used, expected",
    [
        # 6 blobs of 2^17 gas, minus the Dencun target of 3 blobs.
        (0, 786432, 393216),
        # 1 blob is below the target.
        (0, 131072, 0),
    ],
)
def test_excess_blob_gas_dencun(excess: int, used: int, expected: int) -> None:
    # Before Fusaka, the parent's base fee plays no part.
    assert calc_excess_blob_gas("dencun", excess, used, 10**9) == expected


@pytest.mark.parametrize(
    "excess, used, base_fee, expected",
    [
        # The reserve price 2^13 * 17 is above the blob price 2^17, so the excess grows by
        # 786432 * (9 - 6) // 9 = 262144, where dividing first would give 262143.
        (0, 786432, 17, 262144),
        # 7 blobs: 917504 * 3 // 9 = 305834, rounded down.
        (0, 917504, 17, 305834),
        # 2^13 * 16 = 2^17 is not above the blob price, so the target is subtracted.
        (0, 786432, 16, 0),
        # Below the target, the excess is 0 whatever the prices.
        (0, 655360, 10**9, 0),
        (500000, 0, 10**9, 0),
        # At an excess of 5007716 the blob base fee is 2.
        # So the reserve binds above a base fee of 2^17 * 2 / 2^13 = 32.
        (5007716, 786432, 33, 5269860),
        (5007716, 786432, 32, 5007716),
    ],
)
def test_excess_blob_gas_fusaka(excess: int, used: int, base_fee: int, expected: int) -> None:
    # Fusaka keeps the schedule of Pectra: target 6, maximum 9.
    assert calc_excess_blob_gas("fusaka", excess, used, base_fee) == expected


@pytest.mark.parametrize(
    "fork, message",
    [
        ("shapella", "a fork before dencun has no blob schedule"),
        ("frontier", "a fork before dencun has no blob schedule"),
        ("noSuchFork", "no fork named noSuchFork"),
    ],
)
def test_fork_without_blobs(fork: str, message: str) -> None:
    # An unknown fork, or one before Dencun, has no blob schedule.
    with raises(FeesError, message) as info:
        get_base_fee_per_blob_gas(fork, 0)
    assert info.value.code == 0


def test_negative_quantity() -> None:
    with raises(OverflowError, "a fee quantity cannot be negative"):
        calculate_base_fee_per_gas(30_000_000, -1, 7)


def test_large_quantities() -> None:
    # Quantities above 2^64 cross the boundary whole.
    assert calculate_base_fee_per_gas(30_000_000, 15_000_000, 2**300) == 2**300


@pytest.mark.parametrize(
    "fork, fraction",
    [
        ("bpo1", 8346193),
        ("bpo2", 11684671),
        ("bpo3", 11684671),
        ("bpo4", 11684671),
        ("bpo5", 11684671),
    ],
)
def test_blob_parameter_only_forks(fork: str, fraction: int) -> None:
    # An excess equal to the update fraction of the fork gives about e, rounded down to 2.
    assert get_base_fee_per_blob_gas(fork, fraction) == 2


def test_excess_blob_gas_bpo2() -> None:
    # BPO2 has target 14 and maximum 21. A full parent below the reserve price grows the excess
    # by 21 * 2^17 * (21 - 14) // 21 = 917504.
    assert calc_excess_blob_gas("bpo2", 0, 21 * 2**17, 17) == 917504
