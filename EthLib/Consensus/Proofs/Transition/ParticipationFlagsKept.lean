module

public import EthLib.Consensus.Proofs.Transition.TargetFlags
public import EthLib.Consensus.Proofs.Transition.Invariants
import EthLib.Consensus.Proofs.Transition.BlockRewards
import EthLib.Consensus.Proofs.Transition.Totality.SupplyBlock

/-!
# Proofs: a block keeps the target flags it finds

From Altair the state keeps one byte of flags for each validator, in each of two epochs.

A block never clears the timely target flag of a validator that the registry held before it.

Its attestations only add flags.

Its deposits keep the flags below the old size of the registry, and its other steps keep both lists.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## Flags kept forward -/

/-- One flag of one attester keeps the target flag. -/
private theorem addFlagReward_keeps {total : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} {flags flags' : ParticipationFlags} {numerator numerator' : Gwei}
    {flag : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    (computed :
      addFlagReward state total earned index (flags, numerator) flag = .ok (flags', numerator'))
    (set : hasFlag flags TIMELY_TARGET_FLAG_INDEX = true) :
    hasFlag flags' TIMELY_TARGET_FLAG_INDEX = true := by
  unfold addFlagReward at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    by_cases same : flag = ⟨1, by decide⟩
    · subst same
      exact hasFlag_addFlag flags TIMELY_TARGET_FLAG_INDEX
    · exact (hasFlag_addFlag_of_ne flags (other := ⟨1, by decide⟩) (Ne.symm same)).trans set
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, _⟩ := computed
    exact set

/-- One attester keeps the size of the list of flags and each target flag. -/
private theorem addAttesterFlags_keeps {total : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} {participation updated : EpochParticipation preset fork}
    {numerator numerator' : Gwei}
    (computed :
      addAttesterFlags state total earned (participation, numerator) index =
        .ok (updated, numerator')) :
    updated.data.size = participation.data.size ∧
      ∀ position, TargetFlagAt participation position → TargetFlagAt updated position := by
  unfold addAttesterFlags at computed
  dsimp only at computed
  split at computed
  · rename_i inside
    simp only [bind_ok_iff] at computed
    obtain ⟨⟨flags, _⟩, fold, final⟩ := computed
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at final
    obtain ⟨rfl, _⟩ := final
    have byte : hasFlag participation.data[index.toNat] TIMELY_TARGET_FLAG_INDEX = true →
        hasFlag flags TIMELY_TARGET_FLAG_INDEX = true := fun set =>
      foldlM_ok_invariant (fun step => hasFlag step.1 TIMELY_TARGET_FLAG_INDEX = true)
        (fun ⟨_, _⟩ _ ⟨_, _⟩ holds step => addFlagReward_keeps step holds) set fold
    refine ⟨by simp, fun position ⟨value, found, set⟩ => ?_⟩
    by_cases same : index.toNat = position
    · subst same
      rw [Array.getElem?_eq_getElem inside, Option.some.injEq] at found
      subst found
      exact ⟨flags, by simp, byte set⟩
    · exact ⟨value, by rw [Array.getElem?_set]; simp [same, found], set⟩
  · cases computed

/-- From Altair, an attestation keeps each target flag of both epochs. -/
private theorem processAttestationAltair_keepsTargetFlag {attestation : Attestation preset fork}
    {altair : .altair ≤ fork} {parentSlot : Slot}
    (computed :
      processAttestationAltair config checks state attestation altair parentSlot = .ok after)
    (current : Bool) (position : Nat)
    (flagged : TargetFlagAt (recentParticipation state altair current) position) :
    TargetFlagAt (recentParticipation after altair current) position := by
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨updated, _⟩,
    fold, _, _, raised, raisedOk, final⟩ := computed
  have kept :
      recentParticipation after altair current = recentParticipation raised altair current := by
    split at final
    · rw [recordPaymentWeight_eq final]
      rfl
    · cases final
      rfl
  obtain ⟨_, set⟩ := increaseBalance_ok raisedOk
  obtain ⟨_, rfl⟩ := setBalance_ok set
  simp only [BeaconState.putBalance, recentParticipation] at kept
  unfold recentParticipation at flagged ⊢
  rw [kept]
  generalize (attestation.data.target.epoch == getCurrentEpoch state) = same at fold ⊢
  have moved : TargetFlagAt _ position → TargetFlagAt _ position := fun holds =>
    foldlM_ok_invariant
      (fun (carried : EpochParticipation preset fork × Gwei) => TargetFlagAt carried.1 position)
      (fun ⟨_, _⟩ _ ⟨_, _⟩ holds ok => (addAttesterFlags_keeps ok).2 position holds) holds fold
  cases same <;> cases current
  · simpa [setEpochParticipation] using moved (by simpa using flagged)
  · simpa [setEpochParticipation] using flagged
  · simpa [setEpochParticipation] using flagged
  · simpa [setEpochParticipation] using moved (by simpa using flagged)

/-- From Altair, an attestation keeps each target flag of both epochs. -/
private theorem processAttestation_keepsTargetFlag {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after)
    (altair : .altair ≤ fork) (current : Bool) (position : Nat)
    (flagged : TargetFlagAt (recentParticipation state altair current) position) :
    TargetFlagAt (recentParticipation after altair current) position := by
  unfold processAttestation at computed
  split at computed
  · exact processAttestationAltair_keepsTargetFlag computed current position flagged
  · rename_i before
    exact absurd altair before

/-! ## Blocks -/

/-- From Altair, a block keeps each target flag at a position of the registry before it. -/
theorem TargetFlagAt.of_processBlock {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (altair : .altair ≤ fork) (current : Bool) {position : Nat}
    (inside : position < state.validators.data.size)
    (flagged : TargetFlagAt (recentParticipation state altair current) position) :
    TargetFlagAt (recentParticipation after altair current) position := by
  obtain ⟨first, attested, sized, kept, attestedOk, -, below⟩ :=
    processBlock_participationKept computed
  have head : TargetFlagAt (recentParticipation first altair current) position := by
    cases current <;> simpa [recentParticipation, kept.1, kept.2] using flagged
  obtain ⟨grown, ⟨flags, found, set⟩⟩ := foldlM_ok_invariant
    (fun (now : BeaconState preset fork) => first.validators.data.size ≤ now.validators.data.size ∧
      TargetFlagAt (recentParticipation now altair current) position)
    (fun _ _ _ ⟨grows, held⟩ ok => ⟨Nat.le_trans grows (frame_processAttestation ok).registryGrows,
      processAttestation_keepsTargetFlag ok altair current position held⟩)
    ⟨Nat.le_refl _, head⟩ attestedOk
  have same := below altair position (by omega)
  refine ⟨flags, ?_, set⟩
  cases current <;> simpa [recentParticipation, same.1, same.2] using found

end EthLib.Consensus
