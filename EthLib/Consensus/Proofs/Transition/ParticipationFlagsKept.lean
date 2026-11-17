module

public import EthLib.Consensus.Proofs.Transition.TargetFlags
public import EthLib.Consensus.Proofs.Transition.Invariants
import EthLib.Consensus.Proofs.PayloadTimeliness
import EthLib.Consensus.Proofs.Transition.BlockRewards
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
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

variable {preset : Preset} {fork : Fork}

/-! ## The forward relation -/

/-- The registry does not shrink, and each target flag at a position of it before is kept. -/
private def FlagKeeps (state after : BeaconState preset fork) : Prop :=
  state.validators.data.size ≤ after.validators.data.size ∧
    ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat),
      position < state.validators.data.size →
      TargetFlagAt (recentParticipation state altair current) position →
      TargetFlagAt (recentParticipation after altair current) position

variable {config : Config} {checks : SignatureChecks} {state after : BeaconState preset fork}

private theorem FlagKeeps.refl (state : BeaconState preset fork) : FlagKeeps state state :=
  ⟨Nat.le_refl _, fun _ _ _ _ flagged => flagged⟩

private theorem FlagKeeps.trans {first second third : BeaconState preset fork}
    (one : FlagKeeps first second) (two : FlagKeeps second third) : FlagKeeps first third :=
  ⟨Nat.le_trans one.1 two.1, fun altair current position inside flagged =>
    two.2 altair current position (Nat.lt_of_lt_of_le inside one.1)
      (one.2 altair current position inside flagged)⟩

private theorem FlagKeeps.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ a x b, step a x = .ok b → FlagKeeps a b) {items : List α}
    {a b : BeaconState preset fork} (computed : items.foldlM step a = .ok b) : FlagKeeps a b :=
  (foldlM_ok_steps FlagKeeps FlagKeeps.refl FlagKeeps.trans each computed).1

/-- A step that grows the registry and keeps both lists of flags keeps each flag. -/
private theorem FlagKeeps.of_flags
    (grows : state.validators.data.size ≤ after.validators.data.size)
    (flags : Flags state after) : FlagKeeps state after :=
  ⟨grows, fun altair current _ _ flagged => by
    cases current <;> simpa [recentParticipation, flags.1, flags.2] using flagged⟩

/-- A step that grows the registry and keeps the flags below its old size keeps each flag. -/
private theorem FlagKeeps.of_below
    (grows : state.validators.data.size ≤ after.validators.data.size)
    (below : FlagsBelow state after) : FlagKeeps state after :=
  ⟨grows, fun altair current position inside ⟨flags, found, set⟩ => by
    have kept := below altair position inside
    refine ⟨flags, ?_, set⟩
    cases current <;> simpa [recentParticipation, kept.1, kept.2] using found⟩

/-! ## Steps that keep both lists of flags -/

/-- From Electra to Fulu, the requests of a block keep both lists of flags. -/
private theorem flags_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    Flags state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := computed
  exact (Flags.foldlM (fun _ _ _ ok => flags_depositRequest ok) deposits).trans <|
    (Flags.foldlM (fun _ _ _ ok => (fixed_withdrawalRequest ok).flags) withdrawals).trans
      (Flags.foldlM (fun _ _ _ ok => flags_consolidationRequest ok) consolidations)

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

private theorem flagKeeps_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    FlagKeeps state after := by
  refine ⟨(frame_processAttestation computed).registryGrows,
    fun altair current position _ flagged => ?_⟩
  unfold processAttestation at computed
  split at computed
  · exact processAttestationAltair_keepsTargetFlag computed current position flagged
  · rename_i before
    exact absurd altair before

/-! ## Blocks -/

private theorem flagKeeps_processBlock {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    FlagKeeps state after := by
  obtain ⟨input, last, started, operated, frame, synced⟩ := processBlock_operationsInput computed
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of FlagKeeps FlagKeeps.refl FlagKeeps.trans
      (fun ok => FlagKeeps.of_below (frame_processDeposit ok).registryGrows
        (flagsBelow_deposit ok))
      (fun ok => FlagKeeps.of_flags (frame_processVoluntaryExit ok).registryGrows
        (fixed_voluntaryExit ok).flags)
      (fun ok => FlagKeeps.of_flags (frame_processBlsToExecutionChange ok).registryGrows
        (fixed_blsChange ok).flags)
      (fun ok => FlagKeeps.of_flags (frame_processExecutionRequests ok).registryGrows
        (flags_processExecutionRequests ok))
      (fun ok => by rw [processPayloadAttestation_eq ok]; exact FlagKeeps.refl _) operated
  have tail : Flags last after := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact ⟨rfl, rfl⟩
    · cases synced
      exact ⟨rfl, rfl⟩
  exact (FlagKeeps.of_flags (frame_operationsInput started).registryGrows
      (flags_operationsInput started)).trans <|
    (FlagKeeps.foldlM (fun _ _ _ ok => FlagKeeps.of_flags
      (frame_processProposerSlashing ok).registryGrows (flags_proposerSlashing ok))
      proposersOk).trans <|
    (FlagKeeps.foldlM (fun _ _ _ ok => FlagKeeps.of_flags
      (frame_processAttesterSlashing ok).registryGrows (flags_attesterSlashing ok))
      slashingsOk).trans <|
    (FlagKeeps.foldlM (fun _ _ _ ok => flagKeeps_processAttestation ok) attestedOk).trans <|
    rest.trans (FlagKeeps.of_flags frame.registryGrows tail)

/-- From Altair, a block keeps each target flag at a position of the registry before it. -/
theorem TargetFlagAt.of_processBlock {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (altair : .altair ≤ fork) (current : Bool) {position : Nat}
    (inside : position < state.validators.data.size)
    (flagged : TargetFlagAt (recentParticipation state altair current) position) :
    TargetFlagAt (recentParticipation after altair current) position :=
  (flagKeeps_processBlock computed).2 altair current position inside flagged

end EthLib.Consensus
