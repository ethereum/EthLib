"""A sum of recent slashings whose product with the slashing multiplier passes a uint64."""

from eth_consensus_specs.test.context import spec_state_test, with_phases
from eth_consensus_specs.test.helpers.constants import DENEB, HEZE
from eth_consensus_specs.test.helpers.epoch_processing import (
    run_epoch_processing_to,
    run_process_slots_up_to_epoch_boundary,
)
from eth_consensus_specs.test.large_amounts.amounts import rejects_overflow

STEP = "process_slashings"


@with_phases([DENEB, HEZE])
@spec_state_test
def test_slashed_sum_times_multiplier_past_uint64(spec, state):
    # 2^63 Gwei of recent slashings, times the multiplier 3, passes 2^64 - 1.
    state.slashings[0] = 2**63
    run_process_slots_up_to_epoch_boundary(spec, state)
    run_epoch_processing_to(spec, state, STEP, enable_slots_processing=False)
    assert spec.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX == 3
    yield "pre", state
    rejects_overflow(lambda: getattr(spec, STEP)(state))
    yield "post", None
