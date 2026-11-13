"""The fee methods `eth_feeHistory` and `eth_baseFee`, answered by the view of the test chain."""

import json
import math
from typing import Any, Final

import pytest

from ethlib.serialization import rlp

from .chain import FIXTURES, read_fixture, replay_chain

GENESIS: Final = json.loads((FIXTURES / "genesis.json").read_text())["config"]

# The number of the London block of the test chain.
LONDON: Final[int] = GENESIS["londonBlock"]

# The time from which each blob schedule of the chain holds, by its name in the configuration.
SCHEDULE_TIMES: Final = {name: GENESIS[f"{name}Time"] for name in GENESIS["blobSchedule"]}

# The blob gas of one blob, from EIP-4844.
GAS_PER_BLOB: Final = 2**17


def _int(field: bytes) -> int:
    return int.from_bytes(field, "big")


def _head() -> int:
    return len(replay_chain().blocks) - 1


def _block(number: int) -> list[Any]:
    _, raw = replay_chain().blocks[number]
    return rlp.decode(raw)


def _header(number: int) -> tuple[int, int, int]:
    """The gas limit, the gas used and the base fee of a block, 0 before London."""
    header = _block(number)[0]
    # The base fee is the sixteenth field of the header, from London on.
    base_fee = _int(header[15]) if number >= LONDON else 0
    return _int(header[9]), _int(header[10]), base_fee


def _schedule(timestamp: int) -> dict[str, int] | None:
    """The blob schedule of the chain at a time, or None before Cancun."""
    reached = [name for name, time in SCHEDULE_TIMES.items() if time <= timestamp]
    return (
        GENESIS["blobSchedule"][max(reached, key=SCHEDULE_TIMES.__getitem__)] if reached else None
    )


def _fake_exponential(factor: int, numerator: int, denominator: int) -> int:
    """The approximation of `factor * e ** (numerator / denominator)` of EIP-4844."""
    i, output, accumulator = 1, 0, factor * denominator
    while accumulator > 0:
        output += accumulator
        accumulator = accumulator * numerator // (denominator * i)
        i += 1
    return output // denominator


def _blob_fields(number: int) -> tuple[int, float]:
    """The base fee per blob gas of a block and its blob gas ratio, both 0 before Cancun."""
    header = _block(number)[0]
    schedule = _schedule(_int(header[11]))
    if schedule is None:
        return 0, 0
    # From Cancun, the blob gas used and the excess blob gas are fields 17 and 18 of the header.
    fee = _fake_exponential(1, _int(header[18]), schedule["baseFeeUpdateFraction"])
    return fee, _int(header[17]) / (schedule["max"] * GAS_PER_BLOB)


def _tips(number: int) -> list[int]:
    """The tip per gas of each transaction of a block, from its decoded transactions."""
    base_fee = _header(number)[2]
    tips = []
    for item in _block(number)[1]:
        # A legacy transaction is a list, and its gas price is its second field.
        if isinstance(item, list):
            tips.append(_int(item[1]) - base_fee)
            continue
        fields = rlp.decode(item[1:])
        if item[0] == 1:
            tips.append(_int(fields[2]) - base_fee)
        else:
            priority, cap = _int(fields[2]), _int(fields[3])
            tips.append(min(priority, cap - base_fee))
    return tips


def _next_base_fee(gas_limit: int, gas_used: int, base_fee: int) -> int:
    """The base fee of a child of a London block, as EIP-1559 computes it."""
    target = gas_limit // 2
    if gas_used == target:
        return base_fee
    if gas_used > target:
        return base_fee + max(base_fee * (gas_used - target) // target // 8, 1)
    return base_fee - base_fee * (target - gas_used) // target // 8


def _serve_text(method: str, params: list[object]) -> str:
    request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
    (response,) = replay_chain().serve([json.dumps(request)])
    assert response is not None
    return response


def _serve(method: str, params: list[object]) -> dict[str, Any]:
    return json.loads(_serve_text(method, params))


def _result(method: str, params: list[object]) -> Any:
    answer = _serve(method, params)
    assert set(answer) == {"jsonrpc", "id", "result"}
    return answer["result"]


def test_fee_history_fixture() -> None:
    """The fee history fixture gets the values of block 27 and its child, and its checks pass."""
    fixture = read_fixture(FIXTURES / "eth_feeHistory/fee-history.io")
    (exchange,) = fixture.exchanges
    (response,) = replay_chain().serve([exchange.request])
    assert response is not None
    got = json.loads(response)["result"]
    # The fixture is marked speconly, so the expected values come from block 27 and EIP-1559.
    gas_limit, gas_used, base_fee = _header(LONDON)
    assert (gas_limit, gas_used, base_fee) == (200_000_000, 261_514, 10**9)
    (tip,) = set(_tips(LONDON))
    assert got == {
        "oldestBlock": hex(LONDON),
        "baseFeePerGas": [hex(base_fee), hex(_next_base_fee(gas_limit, gas_used, base_fee))],
        "baseFeePerBlobGas": ["0x0", "0x0"],
        "gasUsedRatio": [0.00130757],
        "blobGasUsedRatio": [0],
        "reward": [[hex(tip), hex(tip)]],
    }
    assert got["baseFeePerGas"] == ["0x3b9aca00", "0x342c6dad"]
    # The validation script of the fixture asks for one reward list, whose first tip is 1.
    assert len(got["reward"]) == 1
    assert got["reward"][0][0] == "0x1"


def test_base_fee_fixture() -> None:
    """The fixture of `eth_baseFee` gets the base fee that the head gives to its child."""
    fixture = read_fixture(FIXTURES / "eth_baseFee/get-current-basefee.io")
    (exchange,) = fixture.exchanges
    (response,) = replay_chain().serve([exchange.request])
    assert response is not None
    assert json.loads(response) == exchange.response
    assert exchange.response["result"] == hex(_next_base_fee(*_header(_head())))


def test_whole_history() -> None:
    """The history of the whole chain has the fees and ratios of each block, then the next fees."""
    head = _head()
    got = _result("eth_feeHistory", [hex(head + 1), "latest", []])
    assert got["oldestBlock"] == "0x0"
    assert "reward" not in got
    headers = [_header(number) for number in range(head + 1)]
    next_fee = hex(_next_base_fee(*headers[-1]))
    assert got["baseFeePerGas"] == [*(hex(fee) for _, _, fee in headers), next_fee]
    # Each gas ratio is exact here: it has at most 18 decimal places.
    assert got["gasUsedRatio"] == [used / limit for limit, used, _ in headers]
    blobs = [_blob_fields(number) for number in range(head + 1)]
    # The head is in a blob schedule, so its child has a blob base fee too.
    assert got["baseFeePerBlobGas"][:-1] == [hex(fee) for fee, _ in blobs]
    assert len(got["blobGasUsedRatio"]) == len(blobs)
    for ratio, (_, expected) in zip(got["blobGasUsedRatio"], blobs, strict=True):
        assert math.isclose(ratio, expected, rel_tol=1e-15)
    # The chain has blocks with one blob in four blob schedules, so each maximum is used.
    assert sum(1 for _, ratio in blobs if ratio) == 6


def test_ratio_digits() -> None:
    """A ratio is written with 18 decimal places, rounded down."""
    # Block 42 carries one blob under the Cancun schedule, whose most is six blobs.
    text = _serve_text("eth_feeHistory", ["0x1", "0x2a", []])
    assert '"blobGasUsedRatio":[0.166666666666666666]' in text


# The head of the test chain is block 60.
@pytest.mark.parametrize("number", range(LONDON, 60))
def test_next_base_fee(number: int) -> None:
    """The base fee that a history derives for the next block is the one in its header."""
    got = _result("eth_feeHistory", ["0x1", hex(number), []])
    assert got["baseFeePerGas"] == [hex(_header(number)[2]), hex(_header(number + 1)[2])]


def test_next_base_fee_before_london() -> None:
    """A block before London has no base fee, and the next block gets the initial one at London."""
    assert _result("eth_feeHistory", ["0x1", hex(LONDON - 2), []])["baseFeePerGas"] == [
        "0x0",
        "0x0",
    ]
    assert _result("eth_feeHistory", ["0x1", hex(LONDON - 1), []])["baseFeePerGas"] == [
        "0x0",
        hex(10**9),
    ]


def test_next_blob_base_fee_before_cancun() -> None:
    """The next block is taken one second after the newest, so a later Cancun time is not seen."""
    # Block 41 is the last before Cancun, and block 42 has a blob base fee of 1.
    got = _result("eth_feeHistory", ["0x1", "0x29", []])
    assert got["baseFeePerBlobGas"] == ["0x0", "0x0"]
    assert _blob_fields(42)[0] == 1


def test_rewards() -> None:
    """Each reward is a tip of the block, and the rewards do not decrease along the percentiles."""
    percentiles = [0, 2.5, 10, 50, 99.5, 100]
    got = _result("eth_feeHistory", [hex(_head() + 1), "latest", percentiles])
    for number, rewards in enumerate(got["reward"]):
        tips = _tips(number)
        assert len(rewards) == len(percentiles)
        values = [int(reward, 16) for reward in rewards]
        # An empty block has rewards of 0; the genesis block is one.
        if tips:
            assert set(values) <= set(tips)
        else:
            assert values == [0] * len(percentiles)
        assert values == sorted(values)
    assert _tips(0) == []


def test_empty_range() -> None:
    """A count of 0 gives no block, starts after the newest block, and keeps the next base fee."""
    head = _head()
    got = _result("eth_feeHistory", ["0x0", "latest", [50]])
    assert got == {
        "oldestBlock": hex(head + 1),
        "baseFeePerGas": [hex(_next_base_fee(*_header(head)))],
        "baseFeePerBlobGas": ["0x1"],
        "gasUsedRatio": [],
        "blobGasUsedRatio": [],
        "reward": [],
    }


# Each request whose range the chain clips or not, with its oldest block and its block count.
RANGES = [
    pytest.param(["0x64", "0x5", []], 0, 6, id="clipped-at-genesis"),
    pytest.param(["0x3", "0x20", []], 0x1E, 3, id="inside-the-chain"),
    pytest.param(["0x2", "earliest", []], 0, 1, id="earliest"),
    pytest.param(["0x2", "finalized", []], 59, 2, id="finalized"),
]


@pytest.mark.parametrize(("params", "oldest", "count"), RANGES)
def test_range(params: list[object], oldest: int, count: int) -> None:
    """The range ends at the newest block and holds at most the count of blocks of the node."""
    got = _result("eth_feeHistory", params)
    assert got["oldestBlock"] == hex(oldest)
    assert len(got["gasUsedRatio"]) == count
    assert len(got["baseFeePerGas"]) == count + 1


# Each list of percentiles that a request accepts, at the bounds and across decimal places.
ACCEPTED = [[0, 100], [100.0], [2.5, 10], [0.5, 1e1, 99.99]]


@pytest.mark.parametrize("percentiles", ACCEPTED)
def test_percentiles_accepted(percentiles: list[float]) -> None:
    """Percentiles from 0 to 100 that strictly increase give one reward each."""
    got = _result("eth_feeHistory", ["0x1", "latest", percentiles])
    assert len(got["reward"][0]) == len(percentiles)


INVALID_PARAMS: Final = {"code": -32602, "message": "Invalid params"}

# Each request that fails, with its whole error object.
FAILURES = [
    pytest.param(
        ["0x1", "latest", [50, 50]],
        {**INVALID_PARAMS, "data": "rewardPercentiles: not strictly increasing"},
        id="percentiles-equal",
    ),
    pytest.param(
        ["0x1", "latest", [20, 2.5]],
        {**INVALID_PARAMS, "data": "rewardPercentiles: not strictly increasing"},
        id="percentiles-decreasing",
    ),
    pytest.param(
        ["0x1", "latest", [100.0000001]],
        {**INVALID_PARAMS, "data": "rewardPercentile: above 100"},
        id="percentile-above-100",
    ),
    pytest.param(
        ["0x1", "latest", [-1]],
        {**INVALID_PARAMS, "data": "rewardPercentile: below 0"},
        id="percentile-negative",
    ),
    pytest.param(
        ["0x1", "latest", ["50"]],
        {**INVALID_PARAMS, "data": "rewardPercentile: not a number"},
        id="percentile-string",
    ),
    pytest.param(
        ["0x1", "latest"], {**INVALID_PARAMS, "data": "missing parameter"}, id="missing-percentiles"
    ),
    pytest.param(
        ["0x1", "0x3d", []],
        {"code": -32001, "message": "Resource not found", "data": "newest block not found"},
        id="unknown-block",
    ),
]


@pytest.mark.parametrize(("params", "error"), FAILURES)
def test_fee_history_failure(params: list[object], error: dict[str, object]) -> None:
    """A bad percentile list or an unknown block fails with its error object."""
    assert _serve("eth_feeHistory", params) == {"jsonrpc": "2.0", "id": 1, "error": error}


def test_base_fee_takes_no_parameter() -> None:
    """`eth_baseFee` rejects a parameter."""
    error = {**INVALID_PARAMS, "data": "the method takes no parameter"}
    assert _serve("eth_baseFee", ["latest"]) == {"jsonrpc": "2.0", "id": 1, "error": error}
