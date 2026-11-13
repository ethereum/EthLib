"""The Beacon API answers that read one field of a state, against the JSON of the whole state."""

from functools import cache
from pathlib import Path
from typing import Any

import pytest

from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS

CASES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "fork" / "minimal"

# The forks of the beacon chain in order.
ORDER = tuple(FORKS)

# Each query that a fork adds, with that fork; the key of the field in the state is the query.
SINCE = {
    "pending_deposits": "electra",
    "pending_partial_withdrawals": "electra",
    "pending_consolidations": "electra",
    "proposer_lookahead": "fulu",
    "builder_pending_payments": "gloas",
    "builder_pending_withdrawals": "gloas",
}

# The SSZ type of one item of each list or vector, to build the expected SSZ body item by item.
ITEM = {
    "pending_deposits": "PendingDeposit",
    "pending_partial_withdrawals": "PendingPartialWithdrawal",
    "pending_consolidations": "PendingConsolidation",
    "builder_pending_payments": "BuilderPendingPayment",
    "builder_pending_withdrawals": "BuilderPendingWithdrawal",
}

SLOTS_PER_EPOCH = 8

# The slot of the crafted states: epoch 5 of the minimal preset.
SLOT = 5 * SLOTS_PER_EPOCH + 3

# The pairs of a query and a fork at which the state holds its field, and before which it does not.
AFTER = [(query, fork) for query, first in SINCE.items() for fork in ORDER[ORDER.index(first) :]]
BEFORE = [(query, fork) for query, first in SINCE.items() for fork in ORDER[: ORDER.index(first)]]


def _hex(n: int, size: int) -> str:
    return "0x" + n.to_bytes(size, "little").hex()


def _withdrawal(n: int) -> dict[str, str]:
    return {"fee_recipient": _hex(n, 20), "amount": str(1000 + n), "builder_index": str(n)}


def _items(n: int) -> dict[str, list[Any]]:
    """Distinct items for each list that a fork adds, so that no answer is empty or shared."""
    return {
        "pending_deposits": [
            {
                "pubkey": _hex(n, 48),
                "withdrawal_credentials": _hex(n + 1, 32),
                "amount": str(32_000_000_000 + n),
                "signature": _hex(n + 2, 96),
                "slot": str(n + 3),
            }
        ],
        "pending_partial_withdrawals": [
            {"validator_index": str(n), "amount": str(2000 + n), "withdrawable_epoch": str(n + 9)}
        ],
        "pending_consolidations": [{"source_index": str(n), "target_index": str(n + 1)}],
        "builder_pending_withdrawals": [_withdrawal(n), _withdrawal(n + 1)],
    }


@cache
def _base(fork: str) -> bytes:
    """A state of the minimal preset at a fork, from the vendored upgrade cases."""
    if fork == "phase0":
        path = CASES / "altair" / "fork" / "fork" / "pyspec_tests" / "fork_base_state"
        return snappy.decompress((path / "pre.ssz_snappy").read_bytes())
    path = CASES / fork / "fork" / "fork" / "pyspec_tests" / "fork_base_state"
    return snappy.decompress((path / "post.ssz_snappy").read_bytes())


@cache
def _state(fork: str) -> bytes:
    """The base state with a distinct value in each field that a query reads."""
    state = consensus.api_json("minimal", FORKS[fork], "BeaconState", _base(fork))
    state["slot"] = str(SLOT)
    state["randao_mixes"] = [_hex(i + 1, 32) for i in range(len(state["randao_mixes"]))]
    for offset, key in enumerate(
        ("previous_justified_checkpoint", "current_justified_checkpoint", "finalized_checkpoint")
    ):
        state[key] = {"epoch": str(offset + 1), "root": _hex(offset + 7, 32)}
    for key, items in _items(ORDER.index(fork)).items():
        if key in state:
            state[key] = items
    if "proposer_lookahead" in state:
        state["proposer_lookahead"] = [str(i + 3) for i in range(len(state["proposer_lookahead"]))]
    if "builder_pending_payments" in state:
        state["builder_pending_payments"] = [
            {"weight": str(i), "withdrawal": _withdrawal(i), "proposer_index": str(i + 2)}
            for i in range(len(state["builder_pending_payments"]))
        ]
    return consensus.api_ssz("minimal", FORKS[fork], "BeaconState", state)


@cache
def _json(fork: str) -> dict[str, Any]:
    return consensus.api_json("minimal", FORKS[fork], "BeaconState", _state(fork))


def _query(fork: str, query: str, epoch: int | None = None) -> dict[str, Any]:
    return consensus.api_state_query("minimal", FORKS[fork], _state(fork), query, epoch)


@pytest.mark.parametrize("fork", ORDER)
def test_root_is_the_hash_tree_root(fork: str) -> None:
    root, _ = consensus.ssz_static("minimal", FORKS[fork], "BeaconState", _state(fork))
    assert _query(fork, "root") == {"data": {"root": "0x" + root.hex()}}


@pytest.mark.parametrize("fork", ORDER)
def test_fork_and_checkpoints_are_fields(fork: str) -> None:
    state = _json(fork)
    assert _query(fork, "fork") == {"data": state["fork"]}
    assert _query(fork, "finality_checkpoints") == {
        "data": {
            "previous_justified": {"epoch": "1", "root": _hex(7, 32)},
            "current_justified": {"epoch": "2", "root": _hex(8, 32)},
            "finalized": {"epoch": "3", "root": _hex(9, 32)},
        }
    }


@pytest.mark.parametrize("fork", ORDER)
def test_randao_reads_the_buffer(fork: str) -> None:
    length = len(_json(fork)["randao_mixes"])
    # Entry i of the crafted buffer holds the mix i + 1, and the state is in epoch 5.
    assert _query(fork, "randao") == {"data": {"randao": _hex(6, 32)}}
    assert _query(fork, "randao", 2) == {"data": {"randao": _hex(3, 32)}}
    # The buffer refuses no epoch: one a full turn later reads the same entry.
    assert _query(fork, "randao", 2 + length) == {"data": {"randao": _hex(3, 32)}}


@pytest.mark.parametrize(("query", "fork"), AFTER)
def test_field_of_a_later_fork(query: str, fork: str) -> None:
    field = _json(fork)[query]
    assert len(field) > 0
    # The schema names no consensus version for Heze, so its answers carry none.
    version = {} if fork == "heze" else {"version": fork}
    assert _query(fork, query) == {**version, "data": field}


@pytest.mark.parametrize(("query", "fork"), BEFORE)
def test_field_before_its_fork(query: str, fork: str) -> None:
    message = f"{query} is not in a state before {SINCE[query]}"
    with raises(consensus.ConsensusError, message) as error:
        _query(fork, query)
    assert error.value.code == 400
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_state_query_ssz("minimal", FORKS[fork], _state(fork), query)
    assert error.value.code == 400


@pytest.mark.parametrize(("query", "fork"), AFTER)
def test_ssz_body_is_the_field(query: str, fork: str) -> None:
    items = _json(fork)[query]
    if query == "proposer_lookahead":
        expected = b"".join(int(index).to_bytes(8, "little") for index in items)
    else:
        expected = b"".join(
            consensus.api_ssz("minimal", FORKS[fork], ITEM[query], item) for item in items
        )
    body = consensus.api_state_query_ssz("minimal", FORKS[fork], _state(fork), query)
    assert body == expected


@pytest.mark.parametrize(
    ("query", "epoch", "message"),
    [
        ("validators", None, "no state query is named validators"),
        ("validators", 3, "no state query is named validators"),
        ("root", 3, "the query root takes no epoch"),
    ],
)
def test_names_of_no_query(query: str, epoch: int | None, message: str) -> None:
    with raises(consensus.ConsensusError, message) as error:
        _query("phase0", query, epoch)
    assert error.value.code == 0


@pytest.mark.parametrize("query", ["root", "fork", "finality_checkpoints", "randao"])
def test_query_without_ssz_body(query: str) -> None:
    with raises(consensus.ConsensusError, f"the query {query} has no SSZ body") as error:
        consensus.api_state_query_ssz("minimal", FORKS["phase0"], _state("phase0"), query)
    assert error.value.code == 0
