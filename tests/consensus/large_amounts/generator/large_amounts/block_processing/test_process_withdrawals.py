"""A partial withdrawal of an excess balance above 2^53, and builder withdrawals past a uint64."""

from eth_consensus_specs.test.context import spec_state_test, with_phases
from eth_consensus_specs.test.helpers.builders import add_builder_to_registry
from eth_consensus_specs.test.helpers.constants import DENEB, HEZE
from eth_consensus_specs.test.helpers.execution_payload import (
    build_empty_execution_payload,
    compute_el_block_hash,
)
from eth_consensus_specs.test.helpers.forks import is_post_gloas
from eth_consensus_specs.test.helpers.withdrawals import (
    get_expected_withdrawals,
    run_withdrawals_processing,
    set_parent_block_full,
    set_validator_partially_withdrawable,
)
from eth_consensus_specs.test.large_amounts.amounts import (
    ABOVE_FLOAT,
    rejects_overflow,
)


@with_phases([DENEB, HEZE])
@spec_state_test
def test_partial_withdrawal_above_float(spec, state):
    index = 0
    set_validator_partially_withdrawable(spec, state, index, excess_balance=ABOVE_FLOAT)
    payload = None
    if is_post_gloas(spec):
        # From Gloas the withdrawals of a block follow a parent whose payload arrived.
        set_parent_block_full(spec, state)
    else:
        payload = build_empty_execution_payload(spec, state)
        payload.block_hash = compute_el_block_hash(spec, payload, state)
    withdrawals = get_expected_withdrawals(spec, state)
    assert [w.amount for w in withdrawals if w.validator_index == index] == [ABOVE_FLOAT]
    balance = state.balances[index]
    yield from run_withdrawals_processing(
        spec, state, payload, fully_withdrawable_indices=[], partial_withdrawals_indices=[index]
    )
    assert state.balances[index] == balance - ABOVE_FLOAT
    if is_post_gloas(spec):
        expected = [(w.validator_index, w.amount) for w in state.payload_expected_withdrawals]
        assert expected == [(index, ABOVE_FLOAT)]


@with_phases([HEZE])
@spec_state_test
def test_builder_withdrawals_past_uint64(spec, state):
    # Two pending payments of 2^63 Gwei to one builder sum to 2^64.
    set_parent_block_full(spec, state)
    add_builder_to_registry(spec, state, 0, balance=2**63)
    for _ in range(2):
        state.builder_pending_withdrawals.append(
            spec.BuilderPendingWithdrawal(
                fee_recipient=b"\x33" * 20, amount=2**63, builder_index=0
            )
        )
    yield "pre", state
    rejects_overflow(lambda: spec.process_withdrawals(state))
    yield "post", None
