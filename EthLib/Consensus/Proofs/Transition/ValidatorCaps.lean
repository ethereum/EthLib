module

public import EthLib.Consensus.Proofs.Transition.ValidatorStep

/-!
# Validator effective-balance caps

Each validator's effective balance is at most the cap of its withdrawal credentials.

Genesis gives it, and every step keeps it.

An epoch and a slot keep it at every fork.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Internal

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A validator with an assigned exit never gains compounding credentials along a run. -/
theorem Run.compounding_of_exit_assigned {x y : ForkedBeaconState preset}
    (run : Run config checks x y)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (i : Nat) (v : Validator)
    (found : x.state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ w, y.state.validators.data[i]? = some w ∧
      (hasCompoundingWithdrawalCredential w = true →
        hasCompoundingWithdrawalCredential v = true) := by
  have kept := (CapStep.run run activation compounding).1
  obtain ⟨w, read, _⟩ := kept.monotone i v found
  exact ⟨w, read, (kept.frozen i v w found read assigned).2⟩

/-- Each validator reached from genesis has an effective balance at most its cap.

The preset caps are assumed in order.

`MAX_EFFECTIVE_BALANCE` is at most `MIN_ACTIVATION_BALANCE`.

`MIN_ACTIVATION_BALANCE` is at most `MAX_EFFECTIVE_BALANCE_ELECTRA`.
-/
theorem Run.effectiveBalance_capped {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA) :
    ∀ v ∈ x.state.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset x.fork v :=
  (CapStep.run run activation compounding).1.capped genesis.effectiveBalance_capped

/-- An existing validator's cap cannot decrease along a run. -/
theorem Run.validatorCap_mono {x y : ForkedBeaconState preset}
    (run : Run config checks x y)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (i : Nat) (v : Validator)
    (found : x.state.validators.data[i]? = some v) :
    ∃ w, y.state.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset x.fork v ≤
        withdrawalMaxEffectiveBalance preset y.fork w :=
  (CapStep.run run activation compounding).1.monotone i v found

/-- The cap at an existing index cannot decrease during an epoch. -/
theorem processEpoch_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.epoch ok).1.monotone i v found

/-- The cap at an existing index cannot decrease in a proposer slashing. -/
theorem processProposerSlashing_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.proposerSlashing ok).1.monotone i v found

/-- The cap at an existing index cannot decrease in an attester slashing. -/
theorem processAttesterSlashing_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.attesterSlashing ok).1.monotone i v found

/-- The cap at an existing index cannot decrease in a deposit. -/
theorem processDeposit_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.processDeposit ok).1.monotone i v found

/-- The cap at an existing index cannot decrease in a voluntary exit. -/
theorem processVoluntaryExit_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.exit (processVoluntaryExit_initiates ok)).1.monotone i v found

/-- The cap at an existing index cannot decrease in a change of BLS credentials. -/
theorem processBlsToExecutionChange_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.blsChange ok).1.monotone i v found

/-- The cap at an existing index cannot decrease in a withdrawal request. -/
theorem processWithdrawalRequest_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.withdrawalRequest ok).1.monotone i v found

/-- The cap at an existing index cannot decrease in a consolidation request.

This needs `MIN_ACTIVATION_BALANCE` to be at most `MAX_EFFECTIVE_BALANCE_ELECTRA`. -/
theorem processConsolidationRequest_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processConsolidationRequest config s electra request = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.consolidationRequest compounding ok).1.monotone i v found

/-- One epoch keeps each effective balance at most the largest one of its validator. -/
theorem processEpoch_capped {f : Fork} {s t : BeaconState preset f}
    (ok : processEpoch config checks s = .ok t) (capped : EffectiveBalancesCapped s) :
    EffectiveBalancesCapped t :=
  (CapStep.epoch ok).1.capped capped

/-- One slot keeps each effective balance at most the largest one of its validator. -/
theorem advanceSlot_capped {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) (capped : EffectiveBalancesCapped s) :
    EffectiveBalancesCapped t :=
  (CapStep.slot ok).1.capped capped

/-- A block keeps each effective balance at most the largest one of its validator, at every fork.

The activation balance must be at most the cap of compounding credentials.

Then a switch to compounding credentials never lowers a cap. -/
theorem processBlock_capped {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processBlock config checks engine s block = .ok t) (capped : EffectiveBalancesCapped s) :
    EffectiveBalancesCapped t :=
  (CapStep.block compounding ok).1.capped capped

/-- The upgrade to the next fork keeps each effective balance at most the cap of its validator.

The caps of the preset are assumed in order.

The largest balance before Electra must be at most the least one from Electra.

That one must be at most the largest one for compounding credentials. -/
theorem upgradeNext_capped {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : upgradeNext config checks s = .ok t) (capped : EffectiveBalancesCapped s.state) :
    EffectiveBalancesCapped t.val.state :=
  (CapStep.upgrade activation compounding ok).1.capped capped

/-- The epoch prefix before payments preserves effective-balance caps. -/
theorem capped_epochBeforePayments
    {fork : Fork} {s t : BeaconState preset fork}
    (ok : epochBeforePayments config checks s = .ok t)
    (capped : ∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork v) :
    ∀ v ∈ t.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork v := by
  rw [epochBeforePayments_eq_run] at ok
  exact (CapStep.epochTrace (EpochTrace.run_ok_iff.mp ok)).capped capped

/-- The cap at an existing index cannot decrease during a block. -/
theorem processBlock_validatorCap_mono {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processBlock config checks engine s block = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    ∃ w, t.validators.data[i]? = some w ∧
      withdrawalMaxEffectiveBalance preset f v ≤ withdrawalMaxEffectiveBalance preset f w :=
  (CapStep.block order ok).1.monotone i v found

end EthLib.Consensus
