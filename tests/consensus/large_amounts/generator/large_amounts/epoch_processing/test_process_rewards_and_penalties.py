"""Rewards on balances above 2^53, and a reward that takes a balance past a uint64."""

from eth_consensus_specs.test.context import spec_state_test, with_phases
from eth_consensus_specs.test.helpers.constants import DENEB, HEZE
from eth_consensus_specs.test.helpers.epoch_processing import (
    run_epoch_processing_to,
    run_process_slots_up_to_epoch_boundary,
)
from eth_consensus_specs.test.helpers.state import next_epoch_with_full_participation
from eth_consensus_specs.test.large_amounts.amounts import (
    UINT64_MAX,
    is_above_float,
    rejects_overflow,
)

STEP = "process_rewards_and_penalties"


def _before_rewards(spec, state):
    """Move to the rewards of the third epoch, after an epoch in which every validator attested."""
    next_epoch_with_full_participation(spec, state)
    next_epoch_with_full_participation(spec, state)
    run_process_slots_up_to_epoch_boundary(spec, state)
    run_epoch_processing_to(spec, state, STEP, enable_slots_processing=False)


def _deltas(spec, state):
    """The change of each balance in the step, which does not depend on the balances themselves."""
    probe = state.copy()
    getattr(spec, STEP)(probe)
    return [after - before for before, after in zip(state.balances, probe.balances)]


@with_phases([DENEB, HEZE])
@spec_state_test
def test_balances_above_float(spec, state):
    _before_rewards(spec, state)
    deltas = _deltas(spec, state)
    assert all(delta > 0 for delta in deltas)
    # Each balance starts at an integer above 2^53 whose parity makes the result odd.
    for index, delta in enumerate(deltas):
        start = state.validators[index].effective_balance + 2**53
        state.balances[index] = start + 1 - delta % 2
    yield "pre", state
    getattr(spec, STEP)(state)
    yield "post", state
    assert all(is_above_float(balance) for balance in state.balances)


@with_phases([DENEB, HEZE])
@spec_state_test
def test_reward_past_uint64(spec, state):
    _before_rewards(spec, state)
    assert _deltas(spec, state)[0] > 0
    state.balances[0] = UINT64_MAX
    yield "pre", state
    rejects_overflow(lambda: getattr(spec, STEP)(state))
    yield "post", None
