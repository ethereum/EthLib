module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound

import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold

/-!
# Accountable safety with an a priori drift bound

Two runs extend a common run from genesis and finalize conflicting checkpoints.

Then the unslashed stake at the reference state is at most three times the accountable stake.

The bound adds twice a drift that reads only the reference state and the later finalized epoch.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Apriori Apriori.Internal

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Accountable safety with an a priori drift bound, before Glamsterdam.

Two runs extend a common run from genesis to `x` and finalize conflicting checkpoints.

Assume the hypotheses of `AccountableDriftBound`, such as the parameters, genesis and enough stake.

Then the unslashed stake at `x` is at most three times the accountable stake plus twice `drift`.

Or the runs contain hash evidence.

`drift` depends only on observables at `x` and on the later finalized epoch.

`AccountableWindowBound` strengthens this for a guarded `x` and two calls drawn from the runs.

It adds three times the stake of the keys active at `x` that exit before the earlier target epoch.

Those keys are absent from both calls. -/
theorem accountable_safety_apriori :
    AccountableDriftBound (preset := preset) (config := config) (checks := checks) ∧
      AccountableWindowBound (preset := preset) (config := config) (checks := checks) :=
  headline_of_block_deposits blockReplay_proved

end EthLib.Consensus.DirectSafety
