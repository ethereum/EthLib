module

public import EthLib.Consensus.Proofs.Transition.Totality.Rewards

import EthLib.Base.Proofs.Uint64
import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.Block
import EthLib.Consensus.Proofs.Transition.Invariants
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.Requests
import EthLib.Consensus.Proofs.Transition.Withdrawals
import EthLib.Consensus.Proofs.PayloadTimeliness

/-!
# Proofs: a block raises the effective balances only through new validators

A block keeps the effective balance of each validator that was there before it.

Each new validator starts with an effective balance of at most `MAX_EFFECTIVE_BALANCE`.

Before Electra that is the cap of a deposit, and from Electra a deposit adds a validator at zero.

So a block raises the sum of the effective balances by at most that much per new validator.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Fork}

/-- The second state keeps each effective balance of the first, and grows its registry.

Each validator past the end of the first registry has an effective balance at most the cap. -/
private def Joined (cap : Nat) (s t : BeaconState preset fork) : Prop :=
  EffectiveKept s t ∧ s.validators.data.size ≤ t.validators.data.size ∧
    ∀ j, s.validators.data.size ≤ j → j < t.validators.data.size →
      effectiveAt ⟨fork, t⟩ j ≤ cap

private theorem Joined.refl (cap : Nat) (s : BeaconState preset fork) : Joined cap s s :=
  ⟨effectiveKept_refl s, Nat.le_refl _, fun _ low high => absurd high (Nat.not_lt.mpr low)⟩

private theorem Joined.trans {cap : Nat} {s t u : BeaconState preset fork}
    (one : Joined cap s t) (two : Joined cap t u) : Joined cap s u := by
  refine ⟨effectiveKept_trans one.1 two.1 one.2.1, Nat.le_trans one.2.1 two.2.1,
    fun j low high => ?_⟩
  by_cases inside : j < t.validators.data.size
  · rw [two.1 j inside]
    exact one.2.2 j low inside
  · exact two.2.2 j (Nat.not_lt.mp inside) high

/-- A step that keeps the size of the registry and each effective balance in it. -/
private theorem Joined.of_kept {cap : Nat} {s t : BeaconState preset fork}
    (kept : EffectiveKept s t) (size : t.validators.data.size = s.validators.data.size) :
    Joined cap s t :=
  ⟨kept, Nat.le_of_eq size.symm, fun _ low high => absurd (size ▸ high) (Nat.not_lt.mpr low)⟩

/-- A step that keeps the registry. -/
private theorem Joined.of_validators {cap : Nat} {s t : BeaconState preset fork}
    (same : t.validators.data = s.validators.data) : Joined cap s t :=
  Joined.of_kept (effectiveKept_data same) (by rw [same])

/-- A step that appends one validator with an effective balance at most the cap. -/
private theorem Joined.push {cap : Nat} {s t : BeaconState preset fork} {validator : Validator}
    (pushed : t.validators.data = s.validators.data.push validator)
    (le : validator.effectiveBalance.toNat ≤ cap) : Joined cap s t := by
  refine ⟨fun i inside => ?_, by simp [pushed], fun j low high => ?_⟩
  · simp [effectiveAt, pushed, Array.getElem?_push, Nat.ne_of_lt inside]
  · have last : j = s.validators.data.size := by
      simp only [pushed, Array.size_push] at high
      omega
    subst last
    simpa [effectiveAt, pushed] using le

/-- A validator from a deposit has an effective balance at most `MAX_EFFECTIVE_BALANCE`.

The deposit comes before Electra, or brings in no Gwei. -/
private theorem getValidatorFromDeposit_effectiveBalance_le {pubkey : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei} (early : fork < .pectra ∨ amount = 0) :
    (getValidatorFromDeposit preset fork pubkey credentials amount).effectiveBalance.toNat ≤
      preset.MAX_EFFECTIVE_BALANCE.toNat := by
  unfold getValidatorFromDeposit
  rcases early with early | rfl
  · -- Before Electra the cap of every validator is `MAX_EFFECTIVE_BALANCE`.
    simp only [withdrawalMaxEffectiveBalance, Uint64.toNat_min]
    split
    · exact absurd ‹_› (Nat.not_le.mpr early)
    · exact Nat.min_le_right _ _
  · -- No Gwei gives an effective balance of zero.
    simp [Uint64.toNat_min]

/-- A deposit of a block keeps each effective balance and adds at most one validator.

That validator has an effective balance at most `MAX_EFFECTIVE_BALANCE`. -/
private theorem joined_processDeposit {before : fork < .hegota} {deposit : Deposit}
    {s t : BeaconState preset fork}
    (computed : processDeposit config checks before s deposit = .ok t) :
    Joined preset.MAX_EFFECTIVE_BALANCE.toNat s t := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  rcases applyDeposit_cases applied with rfl | ⟨_, middle, _, rfl | added, rfl⟩ |
    ⟨early, applied⟩
  · exact Joined.of_validators rfl
  · exact Joined.of_validators rfl
  · -- From Electra a deposit with a new key adds a validator with no Gwei.
    exact Joined.push (by simpa using addValidatorToRegistry_validators_eq_push added)
      (getValidatorFromDeposit_effectiveBalance_le (.inr rfl))
  · rcases applyPendingDeposit_cases applied with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · exact Joined.of_validators rfl
    · exact Joined.of_validators (by rw [increaseBalance_validators raised])
    · exact Joined.push (by simpa using addValidatorToRegistry_validators_eq_push added)
        (getValidatorFromDeposit_effectiveBalance_le (.inl early))

/-- A step that keeps the sizes of the registry and each effective balance in it. -/
private theorem Joined.of_sameSizes {cap : Nat} {s t : BeaconState preset fork}
    (kept : EffectiveKept s t) (sizes : SameSizes s t) : Joined cap s t :=
  Joined.of_kept kept sizes.1

/-- A block keeps each effective balance and adds validators within `MAX_EFFECTIVE_BALANCE`. -/
private theorem joined_processBlock {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    Joined preset.MAX_EFFECTIVE_BALANCE.toNat state after := by
  have refl := Joined.refl (preset := preset) (fork := fork) preset.MAX_EFFECTIVE_BALANCE.toNat
  have trans {a b c : BeaconState preset fork} :=
    @Joined.trans preset fork preset.MAX_EFFECTIVE_BALANCE.toNat a b c
  have folds {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
      (each : ∀ a x b, step a x = .ok b → Joined preset.MAX_EFFECTIVE_BALANCE.toNat a b)
      {items : List α} {a b : BeaconState preset fork} (ok : items.foldlM step a = .ok b) :
      Joined preset.MAX_EFFECTIVE_BALANCE.toNat a b :=
    foldlM_ok_invariant (Joined preset.MAX_EFFECTIVE_BALANCE.toNat a)
      (fun _ _ _ before stepped => trans before (each _ _ _ stepped)) (refl a) ok
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  have head : Joined preset.MAX_EFFECTIVE_BALANCE.toNat state input :=
    started.step_of _ refl trans
      (fun _ paid => by
        obtain ⟨kept, size⟩ := effectiveKept_parentPayload paid
        exact Joined.of_kept kept size)
      (fun headed => by
        obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headed
        exact Joined.of_validators rfl)
      (fun _ executed => Joined.of_validators (by rw [processBlockExecution_validators executed]))
      (fun revealed => by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealed
        exact Joined.of_validators rfl)
      (fun _ voted => by
        obtain ⟨_, _, rest⟩ := processEth1Data_eq voted
        rw [← rest]
        exact Joined.of_validators rfl)
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of _ refl trans
      joined_processDeposit
      (fun exited => Joined.of_sameSizes (effectiveKept_voluntaryExit exited)
        (sameSizes_processVoluntaryExit exited))
      (fun changed => Joined.of_sameSizes (effectiveKept_blsChange changed)
        (sameSizes_processBlsToExecutionChange changed))
      (fun requested => Joined.of_sameSizes (effectiveKept_requests requested)
        (sameSizes_processExecutionRequests requested))
      (fun attested => Joined.of_validators (by rw [processPayloadAttestation_eq attested]))
      operated
  have tail : Joined preset.MAX_EFFECTIVE_BALANCE.toNat last after := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact Joined.of_validators rfl
    · cases synced
      exact refl _
  exact trans head <| trans (folds (fun _ _ _ slashed => Joined.of_sameSizes
      (effectiveKept_proposerSlashing slashed) (sameSizes_processProposerSlashing slashed))
      proposersOk) <|
    trans (folds (fun _ _ _ slashed => Joined.of_sameSizes
      (effectiveKept_attesterSlashing slashed) (sameSizes_processAttesterSlashing slashed))
      slashingsOk) <|
    trans (folds (fun _ _ _ attested => Joined.of_sameSizes
      (effectiveKept_data (by rw [(processAttestation_registry attested).1]))
      (sameSizes_processAttestation attested)) attestedOk) <|
    trans rest tail

/-- A block raises the sum of the effective balances only through its new validators.

Each of them adds at most `MAX_EFFECTIVE_BALANCE`. -/
theorem processBlock_effectiveBalanceSum_le {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    effectiveBalanceSum after ≤ effectiveBalanceSum state +
      (after.validators.data.size - state.validators.data.size) *
        preset.MAX_EFFECTIVE_BALANCE.toNat := by
  obtain ⟨kept, grows, joined⟩ := joined_processBlock computed
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le grows
  rw [effectiveBalanceSum_eq_sum_range after, effectiveBalanceSum_eq_sum_range state, hk,
    Nat.add_sub_cancel_left]
  have first : ((List.range state.validators.data.size).map fun j =>
      ((after.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0).sum =
      ((List.range state.validators.data.size).map fun j =>
      ((state.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0).sum := by
    congr 1
    apply List.map_congr_left
    intro j hj
    exact kept j (List.mem_range.mp hj)
  rw [← first, List.range_add, List.map_append, List.sum_append, List.map_map]
  refine Nat.add_le_add_left ((sum_map_le (high := preset.MAX_EFFECTIVE_BALANCE.toNat)
    fun i inside => ?_).trans_eq (by rw [List.length_range])) _
  have size := List.mem_range.mp inside
  exact joined (state.validators.data.size + i) (Nat.le_add_right _ _) (by omega)

end EthLib.Consensus
