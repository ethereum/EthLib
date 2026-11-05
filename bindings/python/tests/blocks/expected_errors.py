"""The message of the header error that each exception name of a blockchain fixture maps to."""

from ethlib.serialization import rlp

INVALID = "header invalid: EthLib.Execution.Blocks.BlockError."

# EIP-1559, Specification: the elasticity multiplier and the base fee change denominator.
ELASTICITY_MULTIPLIER = 2
BASE_FEE_MAX_CHANGE_DENOMINATOR = 8

# EIP-4844, Parameters, and EIP-7918, Parameters.
GAS_PER_BLOB = 2**17
MIN_BASE_FEE_PER_BLOB_GAS = 1
BLOB_BASE_COST = 2**13

# The positions of the header fields that the checks read.
GAS_LIMIT, GAS_USED, TIMESTAMP, BASE_FEE, BLOB_GAS_USED, EXCESS_BLOB_GAS = 9, 10, 11, 15, 17, 18

# The forks with blobs, in order.
BLOB_FORKS = ["dencun", "pectra", "fusaka", "bpo1", "bpo2", "bpo3", "bpo4", "bpo5", "glamsterdam"]

# A blob schedule: its target, its maximum and its base fee update fraction.
Schedule = tuple[int, int, int]


def fork_schedule(fork: str) -> Schedule:
    """The mainnet blob schedule of a fork, from EIP-4844, EIP-7691, EIP-8134 and EIP-8135."""
    position = BLOB_FORKS.index(fork)
    if position >= BLOB_FORKS.index("bpo2"):
        return (14, 21, 11684671)
    if position >= BLOB_FORKS.index("bpo1"):
        return (10, 15, 8346193)
    # Fusaka keeps the schedule of Pectra.
    if position >= BLOB_FORKS.index("pectra"):
        return (6, 9, 5007716)
    return (3, 6, 3338477)


def has_reserve_price(fork: str) -> bool:
    """Whether the excess blob gas of a fork has the reserve price of EIP-7918, from Fusaka on."""
    return BLOB_FORKS.index(fork) >= BLOB_FORKS.index("fusaka")


def _scalar(field: bytes) -> int:
    return int.from_bytes(field, "big")


def fake_exponential(factor: int, numerator: int, denominator: int) -> int:
    """EIP-4844, Helpers: an integer approximation of factor * e ** (numerator / denominator)."""
    i, output, accumulator = 1, 0, factor * denominator
    while accumulator > 0:
        output += accumulator
        accumulator = accumulator * numerator // (denominator * i)
        i += 1
    return output // denominator


def base_fee(parent: list) -> int:
    """EIP-1559, Specification: the base fee per gas of the child of a parent with a base fee."""
    parent_base_fee = _scalar(parent[BASE_FEE])
    target = _scalar(parent[GAS_LIMIT]) // ELASTICITY_MULTIPLIER
    used = _scalar(parent[GAS_USED])
    if used == target:
        return parent_base_fee
    if used > target:
        delta = parent_base_fee * (used - target) // target // BASE_FEE_MAX_CHANGE_DENOMINATOR
        return parent_base_fee + max(delta, 1)
    delta = parent_base_fee * (target - used) // target // BASE_FEE_MAX_CHANGE_DENOMINATOR
    return parent_base_fee - delta


def excess_blob_gas(parent: list, schedule: Schedule, reserve: bool) -> int:
    """EIP-4844, Header extension, with the reserve price of EIP-7918 when `reserve` holds."""
    target, maximum, fraction = schedule
    excess, used = _scalar(parent[EXCESS_BLOB_GAS]), _scalar(parent[BLOB_GAS_USED])
    if excess + used < target * GAS_PER_BLOB:
        return 0
    blob_base_fee = fake_exponential(MIN_BASE_FEE_PER_BLOB_GAS, excess, fraction)
    if reserve and BLOB_BASE_COST * _scalar(parent[BASE_FEE]) > GAS_PER_BLOB * blob_base_fee:
        return excess + used * (maximum - target) // maximum
    return excess + used - target * GAS_PER_BLOB


def expected_message(
    exception: str, parent: bytes, header: bytes, schedule: Schedule | None, reserve: bool
) -> str:
    """The message of the header error for an exception name, from the parent and the header."""
    old, new = rlp.decode(parent), rlp.decode(header)
    if exception == "BlockException.INVALID_GASLIMIT":
        return INVALID + "invalidGasLimit"
    if exception == "BlockException.INVALID_BASEFEE_PER_GAS":
        return f"{INVALID}wrongBaseFee {base_fee(old)} {_scalar(new[BASE_FEE])}"
    if exception == "BlockException.INCORRECT_EXCESS_BLOB_GAS":
        assert schedule is not None, exception
        due = excess_blob_gas(old, schedule, reserve)
        return f"{INVALID}wrongExcessBlobGas {due} {_scalar(new[EXCESS_BLOB_GAS])}"
    raise KeyError(exception)
