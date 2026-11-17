module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound

import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold

/-!
# Accountable safety with an a priori drift bound

Two runs extend a common run from genesis to a shared state and finalize conflicting checkpoints.

Then the unslashed active effective stake at the shared state is bounded by the accountable stake.

The bound is three times the accountable stake plus twice a drift.

Otherwise the runs contain hash evidence.

The drift reads only the shared state and the later finalized epoch, with no replay of the runs.

When the guard of the bound fails, the drift is the whole unslashed stake, and the bound is trivial.

The definitions are in the bound module, and the proof in the modules beside it.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Apriori Apriori.Internal

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Accountable safety with an a priori drift bound, before Glamsterdam.

Two runs extend a common run from genesis to `x` and finalize conflicting checkpoints.

Assume the parameters of the preset, genesis, enough stake and the other hypotheses of the bound.

Then the unslashed stake at `x` is at most three times the accountable stake plus twice the drift.

Or the runs contain hash evidence.

The drift depends only on observables at `x` and on the later finalized epoch.

When the guard fails at `x`, the drift is the unslashed stake at `x`, and the bound is trivial.

The guarded form takes the guard at `x` and two calls drawn from the runs.

It adds three times the stake of the keys active at `x` that exit before the earlier target epoch.

Those keys are absent from both calls. -/
theorem accountable_safety_apriori :
    AccountableDriftBound (preset := preset) (config := config) (checks := checks) ∧
      AccountableWindowBound (preset := preset) (config := config) (checks := checks) :=
  headline_of_block_deposits blockReplay_proved

end EthLib.Consensus.DirectSafety
