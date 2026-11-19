"""The Beacon API statuses of validators and builders, against the conditions of the source."""

from functools import cache
from pathlib import Path

import pytest

from ethlib import consensus
from ethlib.networking import snappy
from raising import raises

FAR = 2**64 - 1

BALANCE = 32_000_000_000

CASES = Path(__file__).resolve().parents[4] / "tests" / "consensus" / "fork" / "minimal"


def _validator(
    eligibility: int, activation: int, exit_epoch: int, withdrawable: int, slashed: bool
) -> dict[str, object]:
    return {
        "pubkey": "0x" + "11" * 48,
        "withdrawal_credentials": "0x" + "22" * 32,
        "effective_balance": "32000000000",
        "slashed": slashed,
        "activation_eligibility_epoch": str(eligibility),
        "activation_epoch": str(activation),
        "exit_epoch": str(exit_epoch),
        "withdrawable_epoch": str(withdrawable),
    }


# One case per status, at epoch 20: the epochs, the slashing and the balance, then the answer.
STATUSES = [
    ((FAR, FAR, FAR, FAR, False), BALANCE, ("pending_initialized", "pending")),
    ((FAR, 30, FAR, FAR, False), BALANCE, ("pending_initialized", "pending")),
    ((9, FAR, FAR, FAR, False), BALANCE, ("pending_queued", "pending")),
    ((9, 21, FAR, FAR, False), BALANCE, ("pending_queued", "pending")),
    ((9, 15, FAR, FAR, False), BALANCE, ("active_ongoing", "active")),
    ((9, 20, FAR, FAR, False), BALANCE, ("active_ongoing", "active")),
    ((9, 15, FAR, FAR, True), BALANCE, ("active_ongoing", "active")),
    ((9, 15, 25, 281, False), BALANCE, ("active_exiting", "active")),
    ((9, 15, 25, 281, True), BALANCE, ("active_slashed", "active")),
    ((9, 15, 20, 281, False), BALANCE, ("exited_unslashed", "exited")),
    ((9, 15, 18, 281, True), BALANCE, ("exited_slashed", "exited")),
    ((9, 15, 18, 20, False), BALANCE, ("withdrawal_possible", "withdrawal")),
    ((9, 15, 18, 20, True), 0, ("withdrawal_done", "withdrawal")),
]


@pytest.mark.parametrize(("epochs", "balance", "expected"), STATUSES)
def test_validator_status(
    epochs: tuple[int, int, int, int, bool], balance: int, expected: tuple[str, str]
) -> None:
    assert consensus.api_validator_status(_validator(*epochs), balance, 20) == expected


def test_validator_through_exit_and_withdrawal() -> None:
    """Active and exiting at epoch 20, then withdrawable from 281."""
    validator = _validator(9, 15, 25, 281, False)
    assert consensus.api_validator_status(validator, BALANCE, 20) == ("active_exiting", "active")
    assert consensus.api_validator_status(validator, BALANCE, 281) == (
        "withdrawal_possible",
        "withdrawal",
    )
    assert consensus.api_validator_status(validator, 0, 281) == ("withdrawal_done", "withdrawal")


def test_out_of_order_epochs_take_the_first_group() -> None:
    """An exit before activation meets two conditions; the pending group comes first."""
    validator = _validator(9, 10, 5, 300, False)
    assert consensus.api_validator_status(validator, BALANCE, 7) == ("pending_queued", "pending")


def test_validator_that_does_not_decode() -> None:
    validator = _validator(9, 15, 25, 281, False)
    del validator["slashed"]
    message = 'document rejected: EthLib.Serialization.Ssz.Err.missingField "slashed"'
    with raises(consensus.ConsensusError, message):
        consensus.api_validator_status(validator, BALANCE, 20)


def _builder(deposit: int, withdrawable: int) -> dict[str, str]:
    return {
        "pubkey": "0x" + "33" * 48,
        "version": "3",
        "execution_address": "0x" + "44" * 20,
        "balance": "1000000000",
        "deposit_epoch": str(deposit),
        "withdrawable_epoch": str(withdrawable),
    }


@cache
def _gloas_state() -> bytes:
    """A Gloas state finalized at epoch 10, with a pending, an active and an exited builder."""
    path = (
        CASES / "gloas" / "fork" / "fork" / "pyspec_tests" / "fork_base_state" / "post.ssz_snappy"
    )
    state = consensus.api_json(
        "minimal", "glamsterdam", "BeaconState", snappy.decompress(path.read_bytes())
    )
    state["finalized_checkpoint"] = {"epoch": "10", "root": "0x" + "55" * 32}
    state["builders"] = [_builder(10, FAR), _builder(9, FAR), _builder(3, 40)]
    return consensus.api_ssz("minimal", "glamsterdam", "BeaconState", state)


@pytest.mark.parametrize(("index", "expected"), [(0, "pending"), (1, "active"), (2, "exited")])
def test_builder_status(index: int, expected: str) -> None:
    assert consensus.api_builder_status("minimal", "glamsterdam", _gloas_state(), index) == expected


def test_builder_outside_the_registry() -> None:
    message = "no builder status: EthLib.Consensus.AccessorError.builderIndexOutOfRange 3"
    with raises(consensus.ConsensusError, message) as error:
        consensus.api_builder_status("minimal", "glamsterdam", _gloas_state(), 3)
    assert error.value.code == 0


def test_builder_before_gloas() -> None:
    path = CASES / "fulu" / "fork" / "fork" / "pyspec_tests" / "fork_base_state" / "post.ssz_snappy"
    with raises(consensus.ConsensusError, "no builder before gloas, at fusaka") as error:
        consensus.api_builder_status("minimal", "fusaka", snappy.decompress(path.read_bytes()), 0)
    assert error.value.code == 0
