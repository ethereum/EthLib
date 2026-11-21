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

/-- One flag of one attester keeps each flag already set. -/
private theorem addFlagReward_keeps {total : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} {flags flags' : ParticipationFlags} {numerator numerator' : Gwei}
    {flag kept : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    (computed :
      addFlagReward state total earned index (flags, numerator) flag = .ok (flags', numerator'))
    (set : hasFlag flags kept.val.toUInt64 = true) :
    hasFlag flags' kept.val.toUInt64 = true := by
  unfold addFlagReward at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    by_cases same : flag = kept
    · subst same
      exact hasFlag_addFlag flags _
    · exact (hasFlag_addFlag_of_ne flags (other := kept) (Ne.symm same)).trans set
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, _⟩ := computed
    exact set

/-- One attester keeps the size of the list of flags and each flag already set. -/
theorem addAttesterFlags_keeps {total : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} {participation updated : EpochParticipation preset fork}
    {numerator numerator' : Gwei}
    (computed :
      addAttesterFlags state total earned (participation, numerator) index =
        .ok (updated, numerator')) :
    updated.data.size = participation.data.size ∧
      ∀ (position : Nat) (kept : Fin PARTICIPATION_FLAG_WEIGHTS.length),
        hasFlag ((participation.data[position]?).getD 0) kept.val.toUInt64 = true →
          hasFlag ((updated.data[position]?).getD 0) kept.val.toUInt64 = true := by
  unfold addAttesterFlags at computed
  dsimp only at computed
  split at computed
  · rename_i inside
    simp only [bind_ok_iff] at computed
    obtain ⟨⟨flags, _⟩, fold, final⟩ := computed
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at final
    obtain ⟨rfl, _⟩ := final
    refine ⟨by simp, fun position kept set => ?_⟩
    by_cases same : index.toNat = position
    · subst same
      rw [Array.getElem?_eq_getElem inside, Option.getD_some] at set
      have byte : hasFlag flags kept.val.toUInt64 = true :=
        foldlM_ok_invariant (fun step => hasFlag step.1 kept.val.toUInt64 = true)
          (fun ⟨_, _⟩ _ ⟨_, _⟩ holds step => addFlagReward_keeps step holds) set fold
      simpa [inside] using byte
    · simpa [Array.getElem?_set, same] using set
  · cases computed

/-- From Altair, an attestation keeps each flag of both epochs. -/
private theorem processAttestationAltair_keepsFlag {attestation : Attestation preset fork}
    {altair : .altair ≤ fork} {parentSlot : Slot}
    (computed :
      processAttestationAltair config checks state attestation altair parentSlot = .ok after)
    (current : Bool) (position : Nat) (kept : Fin PARTICIPATION_FLAG_WEIGHTS.length)
    (flagged : hasFlag (((recentParticipation state altair current).data[position]?).getD 0)
      kept.val.toUInt64 = true) :
    hasFlag (((recentParticipation after altair current).data[position]?).getD 0)
      kept.val.toUInt64 = true := by
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨updated, _⟩,
    fold, _, _, raised, raisedOk, final⟩ := computed
  have same :
      recentParticipation after altair current = recentParticipation raised altair current := by
    split at final
    · rw [recordPaymentWeight_eq final]
      rfl
    · cases final
      rfl
  obtain ⟨_, set⟩ := increaseBalance_ok raisedOk
  obtain ⟨_, rfl⟩ := setBalance_ok set
  simp only [BeaconState.putBalance, recentParticipation] at same
  unfold recentParticipation at flagged ⊢
  rw [same]
  generalize (attestation.data.target.epoch == getCurrentEpoch state) = target at fold ⊢
  have moved : hasFlag (((_ : EpochParticipation preset fork).data[position]?).getD 0)
      kept.val.toUInt64 = true →
      hasFlag (((_ : EpochParticipation preset fork).data[position]?).getD 0)
        kept.val.toUInt64 = true := fun holds =>
    foldlM_ok_invariant
      (fun (carried : EpochParticipation preset fork × Gwei) =>
        hasFlag ((carried.1.data[position]?).getD 0) kept.val.toUInt64 = true)
      (fun ⟨_, _⟩ _ ⟨_, _⟩ holds ok => (addAttesterFlags_keeps ok).2 position kept holds)
      holds fold
  cases target <;> cases current
  · simpa [setEpochParticipation] using moved (by simpa using flagged)
  · simpa [setEpochParticipation] using flagged
  · simpa [setEpochParticipation] using flagged
  · simpa [setEpochParticipation] using moved (by simpa using flagged)

/-- From Altair, an attestation keeps each flag of both epochs.

A position past the end of a list of flags reads as the empty flags. -/
theorem processAttestation_keepsFlag {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after)
    (altair : .altair ≤ fork) (current : Bool) (position : Nat)
    (kept : Fin PARTICIPATION_FLAG_WEIGHTS.length)
    (flagged : hasFlag (((recentParticipation state altair current).data[position]?).getD 0)
      kept.val.toUInt64 = true) :
    hasFlag (((recentParticipation after altair current).data[position]?).getD 0)
      kept.val.toUInt64 = true := by
  unfold processAttestation at computed
  split at computed
  · exact processAttestationAltair_keepsFlag computed current position kept flagged
  · rename_i before
    exact absurd altair before

/-- The target flag is the flag at position one.

A position past the end reads as the empty flags, which hold no target flag. -/
theorem targetFlagAt_iff {participation : EpochParticipation preset fork}
    {position : Nat} :
    TargetFlagAt participation position ↔
      hasFlag ((participation.data[position]?).getD 0)
        (⟨1, by decide⟩ : Fin PARTICIPATION_FLAG_WEIGHTS.length).val.toUInt64 = true := by
  have target : (⟨1, by decide⟩ : Fin PARTICIPATION_FLAG_WEIGHTS.length).val.toUInt64 =
      TIMELY_TARGET_FLAG_INDEX := by decide
  rw [target]
  constructor
  · rintro ⟨flags, found, set⟩
    rw [found, Option.getD_some]
    exact set
  · intro set
    cases read : participation.data[position]? with
    | none =>
      rw [read, Option.getD_none] at set
      exact absurd set (by decide)
    | some flags =>
      rw [read, Option.getD_some] at set
      exact ⟨flags, read, set⟩

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
      targetFlagAt_iff.mpr (processAttestation_keepsFlag ok altair current position ⟨1, by decide⟩
        (targetFlagAt_iff.mp held))⟩)
    ⟨Nat.le_refl _, head⟩ attestedOk
  have same := below altair position (by omega)
  refine ⟨flags, ?_, set⟩
  cases current <;> simpa [recentParticipation, same.1, same.2] using found

end EthLib.Consensus
