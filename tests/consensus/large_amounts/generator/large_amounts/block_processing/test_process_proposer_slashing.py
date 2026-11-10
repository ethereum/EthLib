"""Proposer slashings of a balance above 2^53, and a reward that takes a balance past a uint64."""

from eth_consensus_specs.test.context import spec_state_test, with_phases
from eth_consensus_specs.test.helpers.constants import DENEB, HEZE
from eth_consensus_specs.test.helpers.proposer_slashings import (
    get_valid_proposer_slashing,
    run_proposer_slashing_processing,
)
from eth_consensus_specs.test.large_amounts.amounts import (
    ABOVE_FLOAT,
    UINT64_MAX,
    is_above_float,
    rejects_overflow,
)


def _slashing(spec, state):
    """A signed slashing of a validator other than the proposer, the slashed index and the proposer."""
    proposer = spec.get_beacon_proposer_index(state)
    active = spec.get_active_validator_indices(state, spec.get_current_epoch(state))
    slashed = next(index for index in reversed(active) if index != proposer)
    slashing = get_valid_proposer_slashing(
        spec, state, slashed_index=slashed, signed_1=True, signed_2=True
    )
    return slashing, slashed, proposer


@with_phases([DENEB, HEZE])
@spec_state_test
def test_slashed_balance_above_float(spec, state):
    slashing, slashed, _ = _slashing(spec, state)
    state.balances[slashed] = state.validators[slashed].effective_balance + ABOVE_FLOAT
    yield from run_proposer_slashing_processing(spec, state, slashing)
    assert state.validators[slashed].slashed
    assert is_above_float(state.balances[slashed])


@with_phases([DENEB, HEZE])
@spec_state_test
def test_proposer_reward_past_uint64(spec, state):
    slashing, _, proposer = _slashing(spec, state)
    state.balances[proposer] = UINT64_MAX
    yield "pre", state
    yield "proposer_slashing", slashing
    rejects_overflow(lambda: spec.process_proposer_slashing(state, slashing))
    yield "post", None
