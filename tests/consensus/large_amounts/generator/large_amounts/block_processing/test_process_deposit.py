"""Deposits whose top-up gives a balance above 2^53, or past the range of a uint64."""

from eth_consensus_specs.test.context import spec_state_test, with_phases
from eth_consensus_specs.test.helpers.constants import DENEB
from eth_consensus_specs.test.helpers.deposits import (
    prepare_state_and_deposit,
    run_deposit_processing,
)
from eth_consensus_specs.test.large_amounts.amounts import (
    ABOVE_FLOAT,
    UINT64_MAX,
    is_above_float,
    rejects_overflow,
)


@with_phases([DENEB])
@spec_state_test
def test_top_up_above_float(spec, state):
    index = 0
    deposit = prepare_state_and_deposit(spec, state, index, ABOVE_FLOAT)
    yield from run_deposit_processing(spec, state, deposit, index)
    assert is_above_float(state.balances[index])


@with_phases([DENEB])
@spec_state_test
def test_top_up_to_uint64_max(spec, state):
    index = 0
    state.balances[index] = UINT64_MAX - ABOVE_FLOAT
    deposit = prepare_state_and_deposit(spec, state, index, ABOVE_FLOAT)
    yield from run_deposit_processing(spec, state, deposit, index)
    assert state.balances[index] == UINT64_MAX


@with_phases([DENEB])
@spec_state_test
def test_top_up_past_uint64(spec, state):
    index = 0
    state.balances[index] = UINT64_MAX - ABOVE_FLOAT + 1
    deposit = prepare_state_and_deposit(spec, state, index, ABOVE_FLOAT)
    yield "pre", state
    yield "deposit", deposit
    rejects_overflow(lambda: spec.process_deposit(state, deposit))
    yield "post", None
