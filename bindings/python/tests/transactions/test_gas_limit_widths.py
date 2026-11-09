"""Gas limits where a machine integer wraps or changes sign, against EIP-7825 and EIP-8037."""

import pytest

from ethlib.cryptography.keccak import keccak256
from ethlib.cryptography.secp256k1 import sign
from ethlib.execution import transactions
from ethlib.serialization import rlp
from raising import raises

CHAIN_ID = 1
KEY = bytes(31) + b"\x01"
OTHER = b"\x11" * 20

# The cap of EIP-7825 from Fusaka, and the cap of EIP-8037 from Glamsterdam.
FUSAKA_CAP = 2**24
GLAMSTERDAM_CAP = 2**32 - 1

# The gas limits where a check on a 32-bit or a 64-bit integer can go wrong, four for each width.
# They are the largest signed value, the next one, the largest unsigned value, and the next one.
# A signed integer reads the second as negative and the third as -1, both below every cap.
# A check that keeps only the low bits reads the fourth, 2^32 or 2^64, as 0.
# 2^128 and 2^256 - 1 follow, the last being the largest gas limit that a transaction holds.
WIDTHS = [2**31 - 1, 2**31, 2**32 - 1, 2**32, 2**63 - 1, 2**63, 2**64 - 1, 2**64]
WIDTHS += [2**128, 2**256 - 1]


def _int(n: int) -> bytes:
    """The minimal big-endian bytes of a natural number, as RLP encodes it."""
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _fee_market(gas: int) -> bytes:
    """A signed type 2 transaction on chain 1, with this gas limit, that sends nothing."""
    fields = [_int(CHAIN_ID), b"", _int(1), _int(10), _int(gas), OTHER, b"", b"", []]
    signature = sign(KEY, keccak256(b"\x02" + rlp.encode(fields)))
    r, s, v = signature[:32], signature[32:64], signature[64]
    return b"\x02" + rlp.encode(fields + [_int(v), r.lstrip(b"\0"), s.lstrip(b"\0")])


# The forks from EIP-7825 up to Glamsterdam: the first and the last.
CAPPED_AT_2_24 = ["fusaka", "bpo5"]

# The intrinsic gas of this call to another account, with no value and no data.
# It is 21000 before Glamsterdam, and 12000 + 3000 = 15000 from it by EIP-2780.
INTRINSIC = {"pectra": 21_000, "fusaka": 21_000, "bpo5": 21_000, "glamsterdam": 15_000}


@pytest.mark.parametrize("fork", CAPPED_AT_2_24)
@pytest.mark.parametrize("gas", WIDTHS)
def test_eip7825_rejects_every_width(fork: str, gas: int) -> None:
    with raises(transactions.TransactionError, f"gasLimitExceeded {gas}"):
        transactions.check(fork, CHAIN_ID, _fee_market(gas))


@pytest.mark.parametrize("gas", [gas for gas in WIDTHS if gas > GLAMSTERDAM_CAP])
def test_glamsterdam_rejects_every_width_above_its_cap(gas: int) -> None:
    with raises(transactions.TransactionError, f"gasLimitExceeded {gas}"):
        transactions.check("glamsterdam", CHAIN_ID, _fee_market(gas))


@pytest.mark.parametrize("gas", [gas for gas in WIDTHS if gas <= GLAMSTERDAM_CAP])
def test_glamsterdam_accepts_every_width_up_to_its_cap(gas: int) -> None:
    checked = transactions.check("glamsterdam", CHAIN_ID, _fee_market(gas))
    assert checked.intrinsic_gas == INTRINSIC["glamsterdam"]


@pytest.mark.parametrize(
    "fork, cap",
    [*((fork, FUSAKA_CAP) for fork in CAPPED_AT_2_24), ("glamsterdam", GLAMSTERDAM_CAP)],
)
def test_the_cap_itself_passes(fork: str, cap: int) -> None:
    # The same transaction at the cap passes, so each rejection comes from the gas limit alone.
    assert transactions.check(fork, CHAIN_ID, _fee_market(cap)).intrinsic_gas == INTRINSIC[fork]


@pytest.mark.parametrize("gas", WIDTHS)
def test_no_cap_before_fusaka(gas: int) -> None:
    # Before EIP-7825, a gas limit of any width passes the stateless checks.
    checked = transactions.check("pectra", CHAIN_ID, _fee_market(gas))
    assert checked.intrinsic_gas == INTRINSIC["pectra"]
