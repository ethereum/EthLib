"""Pending top-ups that give a balance above 2^53, and sums that leave the range of a uint64."""

from eth_consensus_specs.test.context import spec_state_test, with_phases
from eth_consensus_specs.test.helpers.constants import HEZE
from eth_consensus_specs.test.helpers.deposits import prepare_pending_deposit
from eth_consensus_specs.test.helpers.epoch_processing import (
    run_epoch_processing_to,
    run_process_slots_up_to_epoch_boundary,
)
from eth_consensus_specs.test.large_amounts.amounts import (
    ABOVE_FLOAT,
    UINT64_MAX,
    is_above_float,
    rejects_overflow,
)

STEP = "process_pending_deposits"


def _top_up(spec, state, index, amount):
    """Queue a top-up of `amount` for a validator, with the churn to apply it this epoch."""
    state.pending_deposits.append(prepare_pending_deposit(spec, index, amount))
    state.deposit_balance_to_consume = amount
    run_process_slots_up_to_epoch_boundary(spec, state)
    run_epoch_processing_to(spec, state, STEP, enable_slots_processing=False)


@with_phases([HEZE])
@spec_state_test
def test_top_up_above_float(spec, state):
    _top_up(spec, state, 0, ABOVE_FLOAT)
    yield "pre", state
    getattr(spec, STEP)(state)
    yield "post", state
    assert len(state.pending_deposits) == 0
    assert is_above_float(state.balances[0])


@with_phases([HEZE])
@spec_state_test
def test_top_up_to_uint64_max(spec, state):
    _top_up(spec, state, 0, ABOVE_FLOAT)
    state.balances[0] = UINT64_MAX - ABOVE_FLOAT
    yield "pre", state
    getattr(spec, STEP)(state)
    yield "post", state
    assert state.balances[0] == UINT64_MAX


@with_phases([HEZE])
@spec_state_test
def test_top_up_past_uint64(spec, state):
    _top_up(spec, state, 0, ABOVE_FLOAT)
    state.balances[0] = UINT64_MAX - ABOVE_FLOAT + 1
    yield "pre", state
    rejects_overflow(lambda: getattr(spec, STEP)(state))
    yield "post", None


@with_phases([HEZE])
@spec_state_test
def test_churn_budget_past_uint64(spec, state):
    _top_up(spec, state, 0, ABOVE_FLOAT)
    state.deposit_balance_to_consume = UINT64_MAX
    yield "pre", state
    rejects_overflow(lambda: getattr(spec, STEP)(state))
    yield "post", None
