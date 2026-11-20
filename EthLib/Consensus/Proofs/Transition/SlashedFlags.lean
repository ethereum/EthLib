module

public import EthLib.Consensus.Proofs.Transition.FfgStake
public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle

/-!
# Proofs: processing slots keeps every slashed flag

Each epoch stage that writes a validator keeps its slashed flag.

A new entry is not slashed, as a position past the end of the registry reads.

So processing slots keeps the slashed flag at each registry position, in both directions.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- Equal registries have equal flags. -/
private theorem slashFlags_of_validators {state after : BeaconState preset fork}
    (same : after.validators.data = state.validators.data := by rfl) :
    ∀ i, (slashedFlagAt after i).getD false = (slashedFlagAt state i).getD false := by
  intro i
  simp only [slashedFlagAt, same]

/-- Replacing one validator with the same flag keeps the flag map. -/
private theorem slashFlags_setValidatorAt {state after : BeaconState preset fork}
    {position : Nat} {validator old : Validator}
    (found : getValidatorAt state position = .ok old)
    (set : state.setValidatorAt position validator = .ok after) (same : validator.slashed =
      old.slashed) :
    ∀ i, (slashedFlagAt after i).getD false = (slashedFlagAt state i).getD false := by
  intro i
  rw [slashedFlagAt_setValidatorAt found set same]

/-- Exit scheduling changes neither existing slashing flags nor registry length. -/
private theorem slashFlags_initiateValidatorExit {config : Config}
    {state after : BeaconState preset fork} {index : ValidatorIndex}
    (run : initiateValidatorExit config state index = .ok after) :
    ∀ i, (slashedFlagAt after i).getD false = (slashedFlagAt state i).getD false := by
  intro i
  rw [slashedFlagAt_initiateValidatorExit run]

/-- A new validator has the same false flag as an absent registry position. -/
private theorem slashFlags_addValidator {state after : BeaconState preset fork}
    {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (run : addValidatorToRegistry state pubkey credentials amount = .ok after) :
    ∀ i, (slashedFlagAt after i).getD false = (slashedFlagAt state i).getD false := by
  have added := addValidatorToRegistry_validators_eq_push run
  intro i
  simp only [slashedFlagAt, added]
  by_cases before : i < state.validators.data.size
  · simp [Array.getElem?_push, before, Nat.ne_of_lt before]
  · by_cases atEnd : i = state.validators.data.size
    · subst i
      simp [getValidatorFromDeposit]
    · simp [Array.getElem?_push, before, atEnd]

/-- The existing epoch traversal preserves default-false positional slashing flags. -/
private theorem slashFlags_epochLaws :
    EpochFrameLaws (fun (state after : BeaconState preset fork) =>
      ∀ i, (slashedFlagAt after i).getD false = (slashedFlagAt state i).getD false) where
  refl := fun _ _ => rfl
  trans := fun one two i => (two i).trans (one i)
  setValidatorAt := fun set found _ flag _ _ => slashFlags_setValidatorAt found set flag
  increaseBalance := fun ok =>
    slashFlags_of_validators (congrArg (·.data) (increaseBalance_validators ok))
  decreaseBalance := fun ok =>
    slashFlags_of_validators (congrArg (·.data) (decreaseBalance_validators ok))
  initiateValidatorExit := slashFlags_initiateValidatorExit
  addValidatorToRegistry := fun ok _ => slashFlags_addValidator ok
  eth1DataVotes _ _ := slashFlags_of_validators
  inactivityScores _ _ := slashFlags_of_validators
  slashings _ _ := slashFlags_of_validators
  randaoMixes _ _ := slashFlags_of_validators
  historicalRoots _ _ := slashFlags_of_validators
  historicalSummaries _ _ := slashFlags_of_validators
  participationRecords _ := slashFlags_of_validators
  pendingDeposits _ _ _ := slashFlags_of_validators
  pendingConsolidations _ _ := slashFlags_of_validators
  syncCommittees _ _ _ := slashFlags_of_validators
  proposerLookahead _ _ := slashFlags_of_validators
  ptcWindow _ _ := slashFlags_of_validators

/-- Every stage in the shared epoch schedule preserves the default-false slashing flag. -/
private theorem slashFlags_processEpoch {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (run : processEpoch config checks state = .ok after) :
    ∀ i, (slashedFlagAt after i).getD false = (slashedFlagAt state i).getD false := by
  apply (processEpoch_trace run).transport
    (fun s t => ∀ i, (slashedFlagAt t i).getD false = (slashedFlagAt s i).getD false)
    (fun _ _ => rfl) (fun a b i => (b i).trans (a i))
  intro stage _ s t ok
  have edge := EpochStage.action_cases.mp ok
  cases stage
  case registry => exact slashFlags_epochLaws.processRegistryUpdates edge
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact slashFlags_epochLaws.processPendingDeposits edge
    · exact edge ▸ fun _ => rfl
  case effectiveBalances => exact slashFlags_epochLaws.processEffectiveBalanceUpdates edge
  all_goals
    exact slashFlags_of_validators
      (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))

/-- Advancing one slot keeps the slashed flag at each registry position. -/
theorem slashedFlagAt_advanceSlot {config : Config} {checks : SignatureChecks}
    {s t : BeaconState preset fork} (ok : advanceSlot config checks s = .ok t) :
    ∀ i, (slashedFlagAt t i).getD false = (slashedFlagAt s i).getD false := by
  obtain ⟨next, cached, epoched, _, cachedOk, epochOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have first := slashFlags_of_validators (state := s) (after := cached) (by rw [cachedEq])
  have middle : ∀ i, (slashedFlagAt epoched i).getD false =
      (slashedFlagAt cached i).getD false := by
    obtain ⟨_, epochOk⟩ | ⟨_, rfl⟩ := epochIfLast_cases epochOk
    · exact slashFlags_processEpoch epochOk
    · exact fun _ => rfl
  exact fun i => (middle i).trans (first i)

/-- Processing slots keeps the slashed flag at each registry position.

A position past the end of the registry reads as not slashed. -/
theorem slashedFlagAt_processSlots {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slot : Slot}
    (run : processSlots config checks state slot = .ok after) :
    ∀ i, (slashedFlagAt after i).getD false = (slashedFlagAt state i).getD false := by
  have steps {count : Nat} {s t : BeaconState preset fork}
      (ok : advanceSlots config checks count s = .ok t) :
      ∀ i, (slashedFlagAt t i).getD false = (slashedFlagAt s i).getD false := by
    induction count generalizing s with
    | zero => cases ok; exact fun _ => rfl
    | succ count ih =>
      obtain ⟨_, first, rest⟩ := bind_ok_iff.mp ok
      exact fun i => (ih rest i).trans (slashedFlagAt_advanceSlot first i)
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
  obtain ⟨_, _, advanced⟩ := run
  exact steps advanced

end EthLib.Consensus
