"""The choice between the local payload and a builder's bid in Beacon API block production."""

import struct
from collections.abc import Sequence
from typing import Any

import pytest

from ethlib import consensus
from ethlib.errors import ConsensusError, SszError
from raising import raises

# The boost factors that the source requires every server to support.
PREFER_LOCAL = 0
PROFIT = 100
PREFER_BUILDER = 2**64 - 1
UINT64_MAX = 2**64 - 1
GWEI = 10**9
ALICE = bytes([0xA1]) * 48
BOB = bytes([0xB0]) * 48


def _terms(
    *,
    pubkeys: Sequence[bytes] = (),
    cap: int = UINT64_MAX,
    min_bid: int = 0,
    boost: int = PROFIT,
) -> dict[str, Any]:
    """The terms of a bid, as the bindings write them."""
    return {
        "builder_pubkeys": list(pubkeys),
        "max_execution_payment": cap,
        "min_bid": min_bid,
        "builder_boost_factor": boost,
    }


def _bid(value: int, payment: int = 0, *, signer: bytes = ALICE, **terms: Any) -> dict[str, Any]:
    """A candidate bid in Gwei, signed by one key, under the given terms."""
    return {
        "signer": signer,
        "value": value,
        "execution_payment": payment,
        "terms": _terms(**terms),
    }


# The v3 rule, in Wei: the local payload wins when it pays at least the boosted builder value.
@pytest.mark.parametrize(
    ("local", "builder", "boost", "expected"),
    [
        # The example of the issue: 90 * (1.05e18 // 100) = 9.45e17 <= 1e18.
        (10**18, 105 * 10**16, 90, True),
        # Factor 0 keeps the local payload whatever the builder pays, even against nothing.
        (0, 10**30, PREFER_LOCAL, True),
        # Factor 100 is profit maximization: the larger value wins, and the local one wins a tie.
        (10**18, 10**18, PROFIT, True),
        (10**18, 10**18 + 100, PROFIT, False),
        # The builder value is rounded down to a hundredth before the factor applies.
        (10**18, 10**18 + 99, PROFIT, True),
        # Factor 2**64 - 1 on 100 Wei outweighs a local payload of 10**19 Wei.
        (10**19, 100, PREFER_BUILDER, False),
        # A builder value below 100 Wei rounds down to nothing, whatever the factor.
        (0, 99, PREFER_BUILDER, True),
    ],
)
def test_prefer_local_v3(local: int, builder: int, boost: int, expected: bool):
    assert consensus.api_prefer_local_v3(local, builder, boost) is expected


def test_prefer_local_v3_boost_out_of_range():
    with raises(ConsensusError, f"expected an int below {2**64}, got {2**64}") as info:
        consensus.api_prefer_local_v3(0, 0, 2**64)
    assert info.value.code == 0


@pytest.mark.parametrize(
    ("value", "payment", "cap", "expected"),
    [
        # The payment counts up to the cap, and adds nothing above it.
        (40_000_000, 5_000_000, 2_000_000, 42_000_000),
        (40_000_000, 1_000_000, 2_000_000, 41_000_000),
        (40_000_000, 0, 0, 40_000_000),
        # The sum saturates at 2**64 - 1 instead of wrapping.
        (UINT64_MAX, UINT64_MAX, UINT64_MAX, UINT64_MAX),
        (UINT64_MAX - 1, 1, 1, UINT64_MAX),
        (UINT64_MAX - 1, 2, 2, UINT64_MAX),
    ],
)
def test_capped_bid_value(value: int, payment: int, cap: int, expected: int):
    assert consensus.api_capped_bid_value(_bid(value, payment, cap=cap)) == expected


@pytest.mark.parametrize(
    ("bid", "expected"),
    [
        # The floor reads the capped value: 42e6 >= 30e6, and 45e6 < 50e6.
        (_bid(40_000_000, 5_000_000, cap=2_000_000, min_bid=30_000_000), True),
        (_bid(45_000_000, min_bid=50_000_000), False),
        # A payment above the cap does not lift a bid over the floor.
        (_bid(40_000_000, 10_000_000, cap=0, min_bid=40_000_001), False),
        (_bid(40_000_000, min_bid=40_000_000), True),
        # An empty key list accepts any signer; a non-empty one only its own keys.
        (_bid(1, signer=BOB), True),
        (_bid(1, signer=BOB, pubkeys=[ALICE]), False),
        (_bid(1, signer=BOB, pubkeys=[ALICE, BOB]), True),
    ],
)
def test_bid_accepted(bid: dict[str, Any], expected: bool):
    assert consensus.api_bid_accepted(bid) is expected


def test_select_payload_example():
    # The example of the issue, local values in Wei: bid A weighs 4.2e9, and bid B is refused.
    a = _bid(40_000_000, 5_000_000, cap=2_000_000, min_bid=30_000_000)
    b = _bid(45_000_000, min_bid=50_000_000)
    assert consensus.api_select_payload(41_000_000 * GWEI, [a, b]) == a
    # With a local build worth 42e6 Gwei the weights tie, and the local build wins.
    assert consensus.api_select_payload(42_000_000 * GWEI, [a, b]) is None
    # One Wei less and bid A wins again: the comparison is exact, in Wei.
    assert consensus.api_select_payload(42_000_000 * GWEI - 1, [a, b]) == a


def test_select_payload_no_bid():
    assert consensus.api_select_payload(0, []) is None
    assert consensus.api_select_payload(0, [_bid(10, min_bid=11)]) is None


def test_select_payload_boundary_factors():
    # Factor 0 weighs nothing, so the local payload wins even when it is worth nothing.
    assert consensus.api_select_payload(0, [_bid(UINT64_MAX, boost=PREFER_LOCAL)]) is None
    # Factor 2**64 - 1 on a 1 Gwei bid beats a local payload below (2**64 - 1) / 100 Gwei.
    favored = _bid(1, boost=PREFER_BUILDER)
    tie = UINT64_MAX * GWEI // 100
    assert consensus.api_select_payload(tie - 1, [favored]) == favored
    assert consensus.api_select_payload(tie, [favored]) is None
    # The weight of the largest bid fills 128 bits without overflow.
    largest = _bid(UINT64_MAX, UINT64_MAX, boost=PREFER_BUILDER)
    tie = UINT64_MAX * UINT64_MAX * GWEI // 100
    assert consensus.api_select_payload(tie - 1, [largest]) == largest
    assert consensus.api_select_payload(tie, [largest]) is None


def test_select_payload_heaviest_and_first():
    light = _bid(10, signer=ALICE)
    heavy = _bid(11, signer=BOB)
    # The heaviest bid wins, wherever it stands.
    assert consensus.api_select_payload(0, [light, heavy]) == heavy
    assert consensus.api_select_payload(0, [heavy, light]) == heavy
    # Between two bids of one weight, the first one in the list wins.
    twin = _bid(11, signer=ALICE)
    assert consensus.api_select_payload(0, [heavy, twin]) == heavy
    assert consensus.api_select_payload(0, [twin, heavy]) == twin
    # A refused bid never wins, however heavy.
    refused = _bid(1000, signer=BOB, pubkeys=[ALICE])
    assert consensus.api_select_payload(0, [refused, light]) == light


def test_select_payload_factor_weighs_value():
    # A boost of 200 doubles a bid's weight, so 6 Gwei at 200 beats 11 Gwei at 100.
    boosted = _bid(6, boost=200, signer=ALICE)
    plain = _bid(11, signer=BOB)
    assert consensus.api_select_payload(0, [plain, boosted]) == boosted


def test_select_payload_payment_above_cap():
    # Raising a payment that is already above its cap does not change the choice.
    capped = _bid(10, 5, cap=5, signer=ALICE)
    rival = _bid(15, signer=BOB)
    assert consensus.api_select_payload(0, [capped, rival]) == capped
    raised = _bid(10, UINT64_MAX, cap=5, signer=ALICE)
    assert consensus.api_select_payload(0, [raised, rival]) == raised


def test_select_payload_rejects_bad_amount():
    message = f"value: expected an int below {2**64}, got {2**64}"
    with raises(ConsensusError, message) as info:
        consensus.api_select_payload(0, [_bid(2**64)])
    assert info.value.code == 0


def _offsets(parts: Sequence[bytes]) -> bytes:
    """The SSZ encoding of a list of variable-size elements: their offsets, then their bytes."""
    head = 4 * len(parts)
    offsets = []
    for part in parts:
        offsets.append(struct.pack("<I", head))
        head += len(part)
    return b"".join(offsets) + b"".join(parts)


def _entry(url: bytes, pubkeys: Sequence[bytes], cap: int, min_bid: int, boost: int) -> bytes:
    """The SSZ encoding of a builder entry, with authentication data b'auth' for slot 7."""
    message = struct.pack("<IQ", 12, 7) + b"auth"
    auth = struct.pack("<I", 100) + bytes(96) + message
    fixed = 4 + 4 + 4 + 24
    keys = b"".join(pubkeys)
    return (
        struct.pack("<III", fixed, fixed + len(url), fixed + len(url) + len(auth))
        + struct.pack("<QQQ", cap, min_bid, boost)
        + url
        + auth
        + keys
    )


def _config(min_bid: int, boost: int, entries: Sequence[bytes]) -> bytes:
    """The SSZ encoding of a builder configuration."""
    return struct.pack("<QQI", min_bid, boost, 20) + _offsets(entries)


def test_builder_config_terms():
    entries = [
        _entry(b"https://a.example", [ALICE], 2_000_000, 30_000_000, PROFIT),
        _entry(b"https://b.example", [], 0, 0, PREFER_BUILDER),
    ]
    read = consensus.api_builder_config_terms(_config(10_000_000, PREFER_LOCAL, entries))
    assert read is not None
    gossip, terms = read
    # Bids received on gossip accept any builder, and count their whole execution payment.
    assert gossip == _terms(cap=UINT64_MAX, min_bid=10_000_000, boost=PREFER_LOCAL)
    assert terms == [
        _terms(pubkeys=[ALICE], cap=2_000_000, min_bid=30_000_000, boost=PROFIT),
        _terms(cap=0, min_bid=0, boost=PREFER_BUILDER),
    ]


def test_builder_config_terms_empty():
    read = consensus.api_builder_config_terms(_config(0, PROFIT, []))
    assert read is not None
    gossip, terms = read
    assert gossip == _terms(cap=UINT64_MAX, min_bid=0, boost=PROFIT)
    assert terms == []


def test_builder_config_empty_url_is_invalid():
    entries = [_entry(b"https://a.example", [], 0, 0, PROFIT), _entry(b"", [], 0, 0, PROFIT)]
    assert consensus.api_builder_config_terms(_config(0, PROFIT, entries)) is None


def test_builder_config_rejects_truncated_bytes():
    with pytest.raises(SszError) as info:
        consensus.api_builder_config_terms(_config(0, PROFIT, [])[:-1])
    assert info.value.code != 0
