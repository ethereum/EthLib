module

public import EthLib.Consensus.Proofs.Transition.ValidatorStep

/-!
# Retired validators stay retired

A validator is retired when it is unslashed and its exit and withdrawable epochs have passed.

Each step keeps it unslashed and keeps both epochs.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Internal

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A run keeps the exit and withdrawal epochs of an unslashed retired validator. -/
theorem Run.retired_validator {x y : ForkedBeaconState preset}
    (run : Run config checks x y)
    (caps : CapOrder preset)
    (i : Nat) (v w : Validator) (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w) (exited : v.exitEpoch ≤ getCurrentEpoch x.state)
    (clean : v.slashed = false) (withdrawn : v.withdrawableEpoch ≤ getCurrentEpoch x.state) :
    w.slashed = false ∧ w.exitEpoch = v.exitEpoch ∧ w.withdrawableEpoch = v.withdrawableEpoch :=
  (CapStep.run run caps).1.retired i v w before after exited clean withdrawn

/-- A block keeps the exit and withdrawal epochs of an unslashed retired validator. -/
theorem processBlock_retired_validator {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processBlock config checks engine s block = .ok t)
    (i : Nat) (v w : Validator) (before : s.validators.data[i]? = some v)
    (after : t.validators.data[i]? = some w) (exited : v.exitEpoch ≤ getCurrentEpoch s)
    (clean : v.slashed = false) (withdrawn : v.withdrawableEpoch ≤ getCurrentEpoch s) :
    w.slashed = false ∧ w.exitEpoch = v.exitEpoch ∧ w.withdrawableEpoch = v.withdrawableEpoch :=
  (CapStep.block order ok).1.retired i v w before after exited clean withdrawn

end EthLib.Consensus
