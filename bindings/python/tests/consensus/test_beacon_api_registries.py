"""The Beacon API answers that read the registries of a state, against a hand-made registry."""

from functools import cache
from pathlib import Path
from typing import Any

import pytest

from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

from .containers import FORKS

FAR = 2**64 - 1

CASES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "fork" / "minimal"

# Epoch 20 of the minimal preset, which has 8 slots per epoch.
SLOT = 20 * 8


def _pubkey(i: int) -> str:
    return "0x" + f"{i + 1:02x}" * 48


def _validator(
    i: int, eligibility: int, activation: int, exit_epoch: int, withdrawable: int, slashed: bool
) -> dict[str, Any]:
    return {
        "pubkey": _pubkey(i),
        "withdrawal_credentials": "0x" + f"{i + 0x20:02x}" * 32,
        "effective_balance": "32000000000",
        "slashed": slashed,
        "activation_eligibility_epoch": str(eligibility),
        "activation_epoch": str(activation),
        "exit_epoch": str(exit_epoch),
        "withdrawable_epoch": str(withdrawable),
    }


# One validator per status at epoch 20: its epochs and slashing, its balance and its status.
# The conditions are those of the validator status document that the API links.
REGISTRY = [
    ((FAR, FAR, FAR, FAR, False), 32_000_000_000, "pending_initialized"),
    ((9, 21, FAR, FAR, False), 32_000_000_001, "pending_queued"),
    ((9, 15, FAR, FAR, False), 32_000_000_002, "active_ongoing"),
    ((9, 15, 25, 281, False), 31_000_000_000, "active_exiting"),
    ((9, 15, 25, 281, True), 30_000_000_000, "active_slashed"),
    ((9, 15, 20, 281, False), 32_000_000_003, "exited_unslashed"),
    ((9, 15, 18, 281, True), 29_000_000_000, "exited_slashed"),
    ((9, 15, 18, 20, False), 32_000_000_004, "withdrawal_possible"),
    ((9, 15, 18, 20, True), 0, "withdrawal_done"),
]


def _builder(i: int, deposit: int, withdrawable: int) -> dict[str, str]:
    return {
        "pubkey": "0x" + f"{i + 0x40:02x}" * 48,
        "version": "3",
        "execution_address": "0x" + f"{i + 0x60:02x}" * 20,
        "balance": str(1_000_000_000 + i),
        "deposit_epoch": str(deposit),
        "withdrawable_epoch": str(withdrawable),
    }


# The builders, with the state finalized at epoch 10, and the status of each.
BUILDERS = [
    (_builder(0, 10, FAR), "pending"),
    (_builder(1, 9, FAR), "active"),
    (_builder(2, 3, 40), "exited"),
]


@cache
def _state(fork: str) -> bytes:
    """The base state of a fork at epoch 20, with the registries above."""
    path = CASES / fork / "fork" / "fork" / "pyspec_tests" / "fork_base_state" / "post.ssz_snappy"
    base = snappy.decompress(path.read_bytes())
    state = consensus.api_json("minimal", FORKS[fork], "BeaconState", base)
    state["slot"] = str(SLOT)
    state["finalized_checkpoint"] = {"epoch": "10", "root": "0x" + "55" * 32}
    state["validators"] = [_validator(i, *epochs) for i, (epochs, _, _) in enumerate(REGISTRY)]
    state["balances"] = [str(balance) for _, balance, _ in REGISTRY]
    if "builders" in state:
        state["builders"] = [builder for builder, _ in BUILDERS]
    return consensus.api_ssz("minimal", FORKS[fork], "BeaconState", state)


def _query(
    query: str,
    ids: list[str] | None = None,
    statuses: list[str] | None = None,
    *,
    fork: str = "gloas",
    in_query: bool = False,
) -> dict[str, Any]:
    return consensus.api_registry_query(
        "minimal", FORKS[fork], _state(fork), query, ids=ids, statuses=statuses, in_query=in_query
    )


def _entry(i: int) -> dict[str, Any]:
    """The entry of the validators answer for validator i, from the registry above."""
    epochs, balance, status = REGISTRY[i]
    return {
        "index": str(i),
        "balance": str(balance),
        "status": status,
        "validator": _validator(i, *epochs),
    }


ALL = {"data": [_entry(i) for i in range(len(REGISTRY))]}


def test_every_validator_with_its_status() -> None:
    assert _query("validators") == ALL
    assert _query("validators", [], []) == ALL


def test_ids_by_index_and_by_public_key() -> None:
    """An unknown id gives no entry, and two names of one validator give one entry."""
    answer = _query("validators", ["2", _pubkey(1), "999999", "1", "0x" + "ee" * 48])
    assert answer == {"data": [_entry(1), _entry(2)]}


@pytest.mark.parametrize(
    ("statuses", "indices"),
    [
        (["pending"], [0, 1]),
        (["active"], [2, 3, 4]),
        (["exited"], [5, 6]),
        (["withdrawal"], [7, 8]),
        *[([status], [i]) for i, (_, _, status) in enumerate(REGISTRY)],
        (["withdrawal", "pending_queued"], [1, 7, 8]),
        (["active", "active_ongoing"], [2, 3, 4]),
    ],
)
def test_status_filter(statuses: list[str], indices: list[int]) -> None:
    assert _query("validators", None, statuses) == {"data": [_entry(i) for i in indices]}


def test_status_filter_with_ids() -> None:
    assert _query("validators", ["3", "5"], ["active"]) == {"data": [_entry(3)]}


@pytest.mark.parametrize(
    ("ids", "statuses", "message"),
    [
        (["foo"], None, "Invalid validator ID: foo"),
        (["0x" + "11" * 47], None, "Invalid validator ID: 0x" + "11" * 47),
        (None, ["Active"], "Invalid validator status: Active"),
    ],
)
def test_bad_request(ids: list[str] | None, statuses: list[str] | None, message: str) -> None:
    with raises(consensus.ConsensusError, message) as error:
        _query("validators", ids, statuses)
    assert error.value.code == 400


@pytest.mark.parametrize("query", ["validators", "validator_balances"])
def test_too_many_ids_in_a_query_string(query: str) -> None:
    ids = [str(i) for i in range(65)]
    with raises(consensus.ConsensusError, "Too many validator IDs in request") as error:
        _query(query, ids, in_query=True)
    assert error.value.code == 414
    # A body has no limit, and 64 ids in a query string pass.
    assert _query(query, ids) == _query(query)
    assert _query(query, ids[:64], in_query=True) == _query(query)


def test_one_validator() -> None:
    assert _query("validator", ["1"]) == {"data": _entry(1)}
    assert _query("validator", [_pubkey(3)]) == {"data": _entry(3)}
    with raises(consensus.ConsensusError, "Validator not found") as error:
        _query("validator", ["999999"])
    assert error.value.code == 404
    with raises(consensus.ConsensusError, "Invalid validator ID: foo") as error:
        _query("validator", ["foo"])
    assert error.value.code == 400


@pytest.mark.parametrize("ids", [None, ["1", "2"]])
def test_one_validator_takes_one_id(ids: list[str] | None) -> None:
    with raises(
        consensus.ConsensusError, "the query validator takes exactly one identifier"
    ) as error:
        _query("validator", ids)
    assert error.value.code == 0


def _balances(indices: list[int]) -> list[dict[str, str]]:
    return [{"index": str(i), "balance": str(REGISTRY[i][1])} for i in indices]


def test_balances() -> None:
    assert _query("validator_balances") == {"data": _balances(list(range(len(REGISTRY))))}
    assert _query("validator_balances", [_pubkey(2), "0"]) == {"data": _balances([0, 2])}


def _balances_ssz(ids: list[str] | None = None, *, in_query: bool = False) -> bytes:
    state = _state("gloas")
    return consensus.api_validator_balances_ssz(
        "minimal", FORKS["gloas"], state, ids=ids, in_query=in_query
    )


def _body(indices: list[int]) -> bytes:
    """Each entry is the index and the balance, each eight bytes in little-endian order."""
    return b"".join(i.to_bytes(8, "little") + REGISTRY[i][1].to_bytes(8, "little") for i in indices)


def test_balances_ssz_body() -> None:
    assert _balances_ssz(["3", "1"]) == _body([1, 3])
    assert _balances_ssz() == _body(list(range(len(REGISTRY))))


def test_balances_ssz_errors() -> None:
    with raises(consensus.ConsensusError, "Too many validator IDs in request") as error:
        _balances_ssz([str(i) for i in range(65)], in_query=True)
    assert error.value.code == 414
    with raises(consensus.ConsensusError, "Invalid validator ID: foo") as error:
        _balances_ssz(["foo"])
    assert error.value.code == 400


def test_identities() -> None:
    expected = [
        {"index": str(i), "pubkey": _pubkey(i), "activation_epoch": str(epochs[1])}
        for i, (epochs, _, _) in enumerate(REGISTRY)
    ]
    assert _query("validator_identities") == {"data": expected}
    assert _query("validator_identities", ["2"]) == {"data": [expected[2]]}


@pytest.mark.parametrize(
    ("query", "statuses", "in_query", "argument"),
    [
        ("validator", ["active"], False, "statuses"),
        ("validator", None, True, "query string"),
        ("validator_balances", ["active"], False, "statuses"),
        ("validator_identities", ["active"], False, "statuses"),
        ("validator_identities", None, True, "query string"),
        ("builders", None, True, "query string"),
    ],
)
def test_argument_that_a_query_does_not_take(
    query: str, statuses: list[str] | None, in_query: bool, argument: str
) -> None:
    with raises(consensus.ConsensusError, f"the query {query} takes no {argument}") as error:
        _query(query, ["1"], statuses, in_query=in_query)
    assert error.value.code == 0


def _builder_entry(i: int) -> dict[str, Any]:
    builder, status = BUILDERS[i]
    return {"index": str(i), "status": status, "builder": builder}


@pytest.mark.parametrize(
    ("ids", "statuses", "indices"),
    [
        (None, None, [0, 1, 2]),
        (None, ["pending"], [0]),
        (None, ["active"], [1]),
        (None, ["exited"], [2]),
        (None, ["pending", "exited"], [0, 2]),
        ([BUILDERS[2][0]["pubkey"], "7", "1"], None, [1, 2]),
    ],
)
def test_builders(ids: list[str] | None, statuses: list[str] | None, indices: list[int]) -> None:
    assert _query("builders", ids, statuses) == {"data": [_builder_entry(i) for i in indices]}


@pytest.mark.parametrize(
    ("ids", "statuses", "message"),
    [
        (None, ["withdrawal"], "Invalid builder status: withdrawal"),
        (["foo"], None, "Invalid builder ID: foo"),
    ],
)
def test_bad_builder_request(
    ids: list[str] | None, statuses: list[str] | None, message: str
) -> None:
    with raises(consensus.ConsensusError, message) as error:
        _query("builders", ids, statuses)
    assert error.value.code == 400


def test_builders_before_gloas() -> None:
    """A state before Gloas gets its error even for a request that does not parse."""
    for statuses in (None, ["withdrawal"]):
        with raises(consensus.ConsensusError, "builders is not in a state before gloas") as error:
            _query("builders", None, statuses, fork="fulu")
        assert error.value.code == 400
    # The validators answers do not depend on the fork.
    assert _query("validators", fork="fulu") == ALL


def test_unknown_query() -> None:
    with raises(consensus.ConsensusError, "no registry query is named committees") as error:
        _query("committees")
    assert error.value.code == 0
