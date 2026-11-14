module

public import EthLib.Consensus.Proofs.Transition.ActiveKept
public import EthLib.Consensus.Proofs.Transition.Totality.FlagWeight
public import EthLib.Consensus.Proofs.Transition.Totality.PendingBlock

/-!
# Proofs: participation flags are set only at active validators, along a chain

From Altair, a state records the participation flags of each validator in two epochs.

An attestation sets flags only at members of a committee of its target epoch.

That epoch is the previous or the current one, and each member is active at it.

A new validator gets no flag.

At the end of an epoch the current flags move to the previous epoch, and new ones start unset.

The upgrade to Altair sets flags only at the attesters of the pending attestations.

This needs their slots in the previous epoch, which well-formed pending attestations ensure.

Each step keeps which validators are active in each epoch up to the current one.

So each step of a chain keeps the flags set only at validators active at their epoch.

That bounds the weight of the flags by the active balances of the two epochs.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Fork}
  {state after : BeaconState preset fork}

/-- Each validator with a flag set in an epoch is active at that epoch.

The epochs are the previous and the current one.

Before Altair a state has no flags, so it always holds. -/
def FlagsActive (state : BeaconState preset fork) : Prop :=
  ∀ altair : .altair ≤ fork, ∀ (j : Nat) (flags : ParticipationFlags) (validator : Validator),
    state.validators.data[j]? = some validator → flags ≠ 0 →
      ((state.previousEpochParticipation altair).data[j]? = some flags →
        isActiveValidator validator (getPreviousEpoch state)) ∧
      ((state.currentEpochParticipation altair).data[j]? = some flags →
        isActiveValidator validator (getCurrentEpoch state))

/-- A state with no flag set has its flags only at active validators. -/
theorem FlagsActive.of_unset
    (unset : ∀ altair : .altair ≤ fork,
      (∀ flags ∈ (state.previousEpochParticipation altair).data, flags = 0) ∧
        ∀ flags ∈ (state.currentEpochParticipation altair).data, flags = 0) :
    FlagsActive state := fun altair _ _ _ _ nonzero =>
  ⟨fun found => absurd ((unset altair).1 _ (Array.mem_of_getElem? found)) nonzero,
    fun found => absurd ((unset altair).2 _ (Array.mem_of_getElem? found)) nonzero⟩

/-! ## Frames of the flags -/

/-- A position active at an epoch holds a validator active at it. -/
private theorem isActiveValidator_of_isActiveAt {epoch : Epoch} {j : Nat} {validator : Validator}
    (present : state.validators.data[j]? = some validator)
    (active : isActiveAt state epoch j = true) : isActiveValidator validator epoch = true := by
  simpa [isActiveAt, present] using active

/-- A step after which each set flag was set at that position before, inside the registry. -/
private def FlagsFrame (state after : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (j : Nat) (flags : ParticipationFlags), flags ≠ 0 →
    j < after.validators.data.size →
    ((after.previousEpochParticipation altair).data[j]? = some flags →
      (state.previousEpochParticipation altair).data[j]? = some flags ∧
        j < state.validators.data.size) ∧
    ((after.currentEpochParticipation altair).data[j]? = some flags →
      (state.currentEpochParticipation altair).data[j]? = some flags ∧
        j < state.validators.data.size)

/-- Every state is a frame of the flags to itself. -/
private theorem FlagsFrame.refl (state : BeaconState preset fork) : FlagsFrame state state :=
  fun _ _ _ _ inside => ⟨fun found => ⟨found, inside⟩, fun found => ⟨found, inside⟩⟩

/-- Two frames of the flags in a row are one. -/
private theorem FlagsFrame.trans {first second third : BeaconState preset fork}
    (one : FlagsFrame first second) (two : FlagsFrame second third) : FlagsFrame first third :=
  fun altair j flags nonzero inside =>
    ⟨fun found =>
      let ⟨middle, inside'⟩ := (two altair j flags nonzero inside).1 found
      (one altair j flags nonzero inside').1 middle,
    fun found =>
      let ⟨middle, inside'⟩ := (two altair j flags nonzero inside).2 found
      (one altair j flags nonzero inside').2 middle⟩

/-- A step that keeps each flag or zeroes it, and does not grow the registry, is a frame. -/
private theorem FlagsFrame.of_kept (flags : FlagsKeptOrZero state after)
    (le : after.validators.data.size ≤ state.validators.data.size) : FlagsFrame state after :=
  fun altair j value nonzero inside =>
    ⟨fun found => ⟨((flags altair j value).1 found).resolve_right nonzero, by omega⟩,
      fun found => ⟨((flags altair j value).2 found).resolve_right nonzero, by omega⟩⟩

/-- A step that keeps each flag or zeroes it, and keeps the sizes, is a frame of the flags. -/
private theorem FlagsFrame.of_sizes (flags : FlagsKeptOrZero state after)
    (sizes : SameSizes state after) : FlagsFrame state after :=
  .of_kept flags (Nat.le_of_eq sizes.1)

/-- A block frame that keeps the registry is a frame of the flags. -/
private theorem FlagsFrame.keep (frame : BlockFrame state after)
    (validators : after.validators = state.validators) : FlagsFrame state after :=
  .of_kept frame.flags (by rw [validators])

/-- A new validator gets no flag, and keeps the flags at the other positions. -/
private theorem flagsFrame_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    FlagsFrame state after := by
  have pushed := addValidatorToRegistry_validators_eq_push computed
  intro altair j flags nonzero inside
  rw [pushed, Array.size_push] at inside
  unfold addValidatorToRegistry at computed
  simp only [altair, ↓reduceDIte, addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨index, indexOk, _, _, _, _, previous, previousOk, current, currentOk, _, _, rfl⟩ :=
    computed
  have atEnd := (getIndexForNewValidator_ok_iff.mp indexOk).2
  refine ⟨fun found => ?_, fun found => ?_⟩
  · rw [show _ = _ from setOrAppendList_getElem? previousOk j] at found
    split at found
    · exact absurd (Option.some.inj found).symm nonzero
    · exact ⟨found, by omega⟩
  · rw [show _ = _ from setOrAppendList_getElem? currentOk j] at found
    split at found
    · exact absurd (Option.some.inj found).symm nonzero
    · exact ⟨found, by omega⟩

/-- The frame of the flags meets the frame laws of the steps of an epoch. -/
private theorem flagsFrameLaws : EpochFrameLaws (@FlagsFrame preset fork) where
  refl := FlagsFrame.refl
  trans := FlagsFrame.trans
  setValidatorAt := fun set found key flag le whole =>
    .of_sizes (mutatorEpochFrameLaws.setValidatorAt set found key flag le whole).flags
      (sameSizes_setValidatorAt set)
  increaseBalance := fun ok =>
    .of_sizes (frame_increaseBalance ok).flags (sameSizes_increaseBalance ok)
  decreaseBalance := fun ok =>
    .of_sizes (frame_decreaseBalance ok).flags (sameSizes_decreaseBalance ok)
  initiateValidatorExit := fun ok =>
    .of_sizes (frame_initiateValidatorExit ok).flags (sameSizes_initiateValidatorExit ok)
  addValidatorToRegistry := fun ok _ => flagsFrame_addValidatorToRegistry ok
  eth1DataVotes _ _ := .refl _
  inactivityScores _ _ := .refl _
  slashings _ _ := .refl _
  randaoMixes _ _ := .refl _
  historicalRoots _ _ := .refl _
  historicalSummaries _ _ := .refl _
  participationRecords _ := .refl _
  pendingDeposits _ _ _ := .refl _
  pendingConsolidations _ _ := .refl _
  syncCommittees _ _ _ := .refl _
  proposerLookahead _ _ := .refl _
  ptcWindow _ _ := .refl _

/-! ## Attestations -/

/-- Each member of a committee is active at the epoch of its slot, at its own position. -/
private theorem isActiveAt_of_getBeaconCommittee {slot : Slot} {index : CommitteeIndex}
    {committee : Array ValidatorIndex}
    (computed : getBeaconCommittee state slot index = .ok committee)
    {member : ValidatorIndex} (mem : member ∈ committee) :
    isActiveAt state (computeEpochAtSlot preset slot) member.toNat = true := by
  obtain ⟨_, _, shuffleOk⟩ := attesterShuffle_ok_of_getBeaconCommittee computed
  simp only [attesterShuffle, bind_ok_iff] at shuffleOk
  obtain ⟨_, _, indices, indicesOk, _⟩ := shuffleOk
  have listed := mem_getActiveValidatorIndices_of_getBeaconCommittee computed mem
  rw [← getActiveValidatorIndicesChecked_ok indicesOk] at listed
  exact isActiveAt_eq_true_iff.mpr
    ((mem_iff_of_getActiveValidatorIndicesChecked_ok indicesOk).mp listed)

/-- Setting the flags of attesters changes only the positions of the attesters. -/
private theorem foldlM_addAttesterFlags_positions {total : Gwei} {earned : List UInt64}
    {attesters : List ValidatorIndex} {participation updated : EpochParticipation preset fork}
    {numerator numerator' : Gwei}
    (computed : attesters.foldlM (addAttesterFlags state total earned) (participation, numerator) =
      .ok (updated, numerator')) (j : Nat) (flags : ParticipationFlags)
    (found : updated.data[j]? = some flags) :
    participation.data[j]? = some flags ∨ ∃ attester ∈ attesters, attester.toNat = j := by
  refine foldlM_ok_invariant_of_mem
    (fun (carried : EpochParticipation preset fork × Gwei) => ∀ j flags,
      carried.1.data[j]? = some flags →
        participation.data[j]? = some flags ∨ ∃ attester ∈ attesters, attester.toNat = j)
    (fun ⟨list, _⟩ attester ⟨list', _⟩ mem holds ok => ?_) (fun _ _ found => .inl found)
    computed j flags found
  intro position value present
  unfold addAttesterFlags at ok
  dsimp only at ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨_, _, rfl, _⟩ := ok
    dsimp only at present
    rw [Array.getElem?_set] at present
    split at present
    · exact .inr ⟨attester, mem, by assumption⟩
    · exact holds position value present
  · cases ok

/-- Each signer of an attestation is active at the epoch of its slot, at its own position. -/
private theorem isActiveAt_of_getAttestingIndices {attestation : Attestation preset fork}
    {attesters : List ValidatorIndex}
    (computed : getAttestingIndices state attestation = .ok attesters)
    {attester : ValidatorIndex} (mem : attester ∈ attesters) :
    isActiveAt state (computeEpochAtSlot preset attestation.data.slot) attester.toNat = true := by
  obtain ⟨_, _, -, committeeOk, inCommittee⟩ :=
    exists_mem_getBeaconCommittee_of_getAttestingIndices computed mem
  exact isActiveAt_of_getBeaconCommittee committeeOk inCommittee

/-- A step that keeps the registry and the slot, and sets flags only at active positions. -/
private def VoteStep (state after : BeaconState preset fork) : Prop :=
  after.validators = state.validators ∧ after.slot = state.slot ∧
    ∀ (altair : .altair ≤ fork) (j : Nat) (flags : ParticipationFlags), flags ≠ 0 →
      ((after.previousEpochParticipation altair).data[j]? = some flags →
        (state.previousEpochParticipation altair).data[j]? = some flags ∨
          isActiveAt state (getPreviousEpoch state) j = true) ∧
      ((after.currentEpochParticipation altair).data[j]? = some flags →
        (state.currentEpochParticipation altair).data[j]? = some flags ∨
          isActiveAt state (getCurrentEpoch state) j = true)

/-- Every state is a step of votes to itself. -/
private theorem VoteStep.refl (state : BeaconState preset fork) : VoteStep state state :=
  ⟨rfl, rfl, fun _ _ _ _ => ⟨.inl, .inl⟩⟩

/-- Two steps of votes in a row are one. -/
private theorem VoteStep.trans {first second third : BeaconState preset fork}
    (one : VoteStep first second) (two : VoteStep second third) : VoteStep first third := by
  obtain ⟨validators, slot, flags⟩ := one
  obtain ⟨validators', slot', flags'⟩ := two
  have active (epoch : Epoch) (j : Nat) : isActiveAt second epoch j = isActiveAt first epoch j := by
    simp only [isActiveAt, validators]
  have current : getCurrentEpoch second = getCurrentEpoch first := by
    simp only [getCurrentEpoch, slot]
  have previous : getPreviousEpoch second = getPreviousEpoch first := by
    simp only [getPreviousEpoch, current]
  refine ⟨validators'.trans validators, slot'.trans slot, fun altair j value nonzero =>
    ⟨fun found => ?_, fun found => ?_⟩⟩
  · rcases (flags' altair j value nonzero).1 found with old | fresh
    · exact (flags altair j value nonzero).1 old
    · exact .inr (by rwa [active, previous] at fresh)
  · rcases (flags' altair j value nonzero).2 found with old | fresh
    · exact (flags altair j value nonzero).2 old
    · exact .inr (by rwa [active, current] at fresh)

/-- An attestation sets flags only at its signers, who are active at its target epoch. -/
private theorem voteStep_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    VoteStep state after := by
  refine ⟨(processAttestation_registry computed).1, (frame_processAttestation computed).slot,
    fun altair j value nonzero => ?_⟩
  unfold processAttestation at computed
  simp only [altair, ↓reduceDIte] at computed
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, recent, _, slotEpoch, _, _, _, _, _, _, _, _, earned, earnedOk, indexed, indexedOk,
    valid, validOk, _, checked, _, _, attesters, attestersOk, ⟨updated, _⟩, fold, _, _,
    raised, raisedOk, final⟩ := computed
  have kept : after.previousEpochParticipation altair = raised.previousEpochParticipation altair ∧
      after.currentEpochParticipation altair = raised.currentEpochParticipation altair := by
    split at final
    · rw [recordPaymentWeight_eq final]
      exact ⟨rfl, rfl⟩
    · cases final
      exact ⟨rfl, rfl⟩
  obtain ⟨_, set⟩ := increaseBalance_ok raisedOk
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rw [ensure_ok_iff] at recent slotEpoch
  have active : ∀ attester ∈ attesters,
      isActiveAt state attestation.data.target.epoch attester.toNat = true := fun _ mem => by
    rw [slotEpoch]
    exact isActiveAt_of_getAttestingIndices attestersOk mem
  have positions := foldlM_addAttesterFlags_positions fold j value
  rw [kept.1, kept.2]
  simp only [BeaconState.putBalance]
  clear kept final set raisedOk
  generalize chosen : (attestation.data.target.epoch == getCurrentEpoch state) = same
    at fold positions
  cases same
  · have previous : attestation.data.target.epoch = getPreviousEpoch state :=
      recent.resolve_right fun same => by simp [same] at chosen
    refine ⟨fun found => ?_, fun found => .inl found⟩
    rcases positions found with old | ⟨attester, mem, rfl⟩
    · exact .inl (by simpa using old)
    · exact .inr (previous ▸ active attester mem)
  · have current : attestation.data.target.epoch = getCurrentEpoch state := by
      simpa using chosen
    refine ⟨fun found => .inl found, fun found => ?_⟩
    rcases positions found with old | ⟨attester, mem, rfl⟩
    · exact .inl (by simpa using old)
    · exact .inr (current ▸ active attester mem)

/-! ## Activity at the epochs of the flags -/

/-- A set flag of the previous epoch, inside the registry, marks a position active at that epoch. -/
private theorem FlagsActive.previous_at (holds : FlagsActive state) {altair : .altair ≤ fork}
    {j : Nat} {flags : ParticipationFlags}
    (found : (state.previousEpochParticipation altair).data[j]? = some flags)
    (nonzero : flags ≠ 0) (inside : j < state.validators.data.size) :
    isActiveAt state (getPreviousEpoch state) j = true := by
  have present := Array.getElem?_eq_getElem inside
  simpa [isActiveAt, present] using (holds altair j flags _ present nonzero).1 found

/-- A set flag of the current epoch, inside the registry, marks a position active at that epoch. -/
private theorem FlagsActive.current_at (holds : FlagsActive state) {altair : .altair ≤ fork}
    {j : Nat} {flags : ParticipationFlags}
    (found : (state.currentEpochParticipation altair).data[j]? = some flags)
    (nonzero : flags ≠ 0) (inside : j < state.validators.data.size) :
    isActiveAt state (getCurrentEpoch state) j = true := by
  have present := Array.getElem?_eq_getElem inside
  simpa [isActiveAt, present] using (holds altair j flags _ present nonzero).2 found

/-- A position active at an epoch up to the current one stays active at it after a kept step. -/
private theorem isActiveValidator_of_activeKept {post : Fork} {other : BeaconState preset post}
    (kept : ActiveKept (activityFixedEpoch state) state other) {epoch : Epoch}
    (le : epoch ≤ getCurrentEpoch state) {j : Nat} (active : isActiveAt state epoch j = true)
    {validator : Validator} (present : other.validators.data[j]? = some validator) :
    isActiveValidator validator epoch = true := by
  have same := kept epoch (UInt64.le_trans le (getCurrentEpoch_le_activityFixedEpoch state)) j
  rw [← same] at active
  simpa [isActiveAt, present] using active

/-! ## Slots -/

/-- From Altair, an epoch moves the current flags to the previous epoch and unsets the current. -/
private theorem processEpoch_flags (altair : .altair ≤ fork)
    (computed : processEpoch config checks state = .ok after) {j : Nat}
    {flags : ParticipationFlags} (nonzero : flags ≠ 0) (inside : j < after.validators.data.size) :
    ((after.previousEpochParticipation altair).data[j]? = some flags →
      (state.currentEpochParticipation altair).data[j]? = some flags ∧
        j < state.validators.data.size) ∧
    (after.currentEpochParticipation altair).data[j]? ≠ some flags := by
  simp only [processEpoch, altair, ↓reduceDIte] at computed
  obtain ⟨justified, rooted, justifiedOk, head, tail⟩ :=
    flagsFrameLaws.processEpochAltair_rotationSplit (fun _ ok => by
      rw [processBuilderPendingPayments_eq ok]
      exact FlagsFrame.refl _) computed
  have keeps := processJustificationAndFinalization_keeps justifiedOk
  have first : FlagsFrame state justified :=
    .of_sizes (FlagsKeptOrZero.of_eq keeps.2.2.2.2.2.2.2.2.1 keeps.2.2.2.2.2.2.2.2.2)
      (sameSizes_processJustificationAndFinalization justifiedOk)
  refine ⟨fun found => ?_, fun found => ?_⟩
  · obtain ⟨rotated, inside'⟩ := (tail altair j flags nonzero inside).1 found
    rw [processParticipationFlagUpdates_previous] at rotated
    obtain ⟨rooted', inside''⟩ := (head altair j flags nonzero inside').2 rotated
    exact (first altair j flags nonzero inside'').2 rooted'
  · obtain ⟨rotated, -⟩ := (tail altair j flags nonzero inside).2 found
    rw [processParticipationFlagUpdates_current, Array.getElem?_replicate] at rotated
    split at rotated
    · exact nonzero (Option.some.inj rotated).symm
    · cases rotated

/-! ## Blocks -/

/-- A block frame that keeps the registry keeps the slot and activity. -/
private theorem activeStep_keep {state after : BeaconState preset fork}
    (frame : BlockFrame state after) (validators : after.validators = state.validators) :
    ActiveStep state after :=
  ActiveStep.of_validators (congrArg (·.data) validators) frame.slot

/-- The steps of a block before its operations are a frame of the flags. -/
private theorem flagsFrame_operationsInput {block : BeaconBlock preset fork}
    {input : BeaconState preset fork}
    (started : OperationsInput config checks engine state block input) :
    FlagsFrame state input :=
  started.step_of FlagsFrame FlagsFrame.refl FlagsFrame.trans
    (fun _ ok => processParentExecutionPayload_step_of FlagsFrame FlagsFrame.refl
      FlagsFrame.trans FlagsFrame.keep (flagsFrameLaws.processWithdrawalRequest FlagsFrame.keep)
      (flagsFrameLaws.processConsolidationRequest FlagsFrame.keep) ok)
    (fun ok => .of_sizes (frame_processBlockHeader ok).flags (sameSizes_processBlockHeader ok))
    (fun _ ok => processBlockExecution_step_of FlagsFrame FlagsFrame.refl FlagsFrame.trans
      FlagsFrame.keep (flagsFrameLaws.processWithdrawals FlagsFrame.keep) ok)
    (fun ok => .of_sizes (frame_processRandao ok).flags (sameSizes_processRandao ok))
    (fun _ ok => .of_sizes (frame_processEth1Data ok).flags (sameSizes_processEth1Data ok))

/-- The steps of a block before its operations keep the slot and activity. -/
private theorem activeStep_operationsInput {block : BeaconBlock preset fork}
    {input : BeaconState preset fork}
    (started : OperationsInput config checks engine state block input) :
    ActiveStep state input :=
  started.step_of ActiveStep ActiveStep.refl ActiveStep.trans
    (fun _ ok => processParentExecutionPayload_step_of ActiveStep ActiveStep.refl
      ActiveStep.trans activeStep_keep activeStep_processWithdrawalRequest
      activeStep_processConsolidationRequest ok)
    activeStep_processBlockHeader (fun _ ok => activeStep_processBlockExecution ok)
    activeStep_processRandao (fun _ ok => activeStep_processEth1Data ok)

/-- Flags set only at active validators keep their weight within the active balances. -/
theorem FlagsWithinActive.of_flagsActive (holds : FlagsActive state) : FlagsWithinActive state :=
  FlagsWithinActive.of_active
    (fun altair j flags found nonzero validator present =>
      (holds altair j flags validator present nonzero).1 found)
    (fun altair j flags found nonzero validator present =>
      (holds altair j flags validator present nonzero).2 found)

/-- One slot keeps the flags set only at active validators.

At the end of an epoch the current flags become the previous ones, and the current ones start unset.

The validators active at the epoch that ends stay active at it. -/
theorem FlagsActive.of_advanceSlot (holds : FlagsActive state)
    (computed : advanceSlot config checks state = .ok after) : FlagsActive after := by
  have kept := activeKept_advanceSlot computed
  obtain ⟨next, cached, epoched, sum, cachedOk, epochOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  intro altair j flags validator present nonzero
  have inside : j < epoched.validators.data.size := (Array.getElem?_eq_some_iff.mp present).1
  unfold epochIfLast at epochOk
  split at epochOk
  · rename_i boundary
    -- The new previous epoch is the epoch that ends.
    have previous : getPreviousEpoch { epoched with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getPreviousEpoch_toNat, getCurrentEpoch_toNat, getCurrentEpoch_toNat]
      exact (congrArg (· - 1) (nextSlot_epoch_of_boundary sum boundary)).trans
        (Nat.add_sub_cancel _ _)
    obtain ⟨moved, unset⟩ := processEpoch_flags altair epochOk nonzero inside
    refine ⟨fun found => ?_, fun found => absurd found unset⟩
    obtain ⟨old, inside'⟩ := moved found
    rw [previous]
    exact isActiveValidator_of_activeKept kept (UInt64.le_refl _)
      (holds.current_at old nonzero inside') present
  · rename_i notBoundary
    simp only [pure, Except.pure, Except.ok.injEq] at epochOk
    subst epochOk
    have epoch : computeEpochAtSlot preset next = computeEpochAtSlot preset state.slot := by
      unfold computeEpochAtSlot
      rw [← UInt64.toNat_inj, UInt64.toNat_div, UInt64.toNat_div]
      exact nextSlot_epoch_of_inside sum notBoundary
    have := holds altair j flags validator present nonzero
    simp only [getPreviousEpoch, getCurrentEpoch] at this ⊢
    rw [epoch]
    exact this

/-- A block keeps the flags set only at active validators.

Its attestations set flags only at members of a committee of the previous or the current epoch. -/
theorem FlagsActive.of_processBlock {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork} (holds : FlagsActive state)
    (computed : processBlock config checks engine state block = .ok after) : FlagsActive after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  obtain ⟨proposersDone, slashingsDone, attested, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of FlagsFrame FlagsFrame.refl FlagsFrame.trans
      (flagsFrameLaws.processDeposit FlagsFrame.keep) flagsFrameLaws.processVoluntaryExit
      flagsFrameLaws.processBlsToExecutionChange
      (flagsFrameLaws.processExecutionRequests FlagsFrame.keep)
      (fun ok => by
        rw [processPayloadAttestation_eq ok]
        exact FlagsFrame.refl _) operated
  -- Before the attestations: a frame of the flags that keeps activity.
  have headFrame : FlagsFrame state slashingsDone :=
    (flagsFrame_operationsInput started).trans <|
      (flagsFrameLaws.foldlM (fun _ _ _ ok => .of_sizes (frame_processProposerSlashing ok).flags
        (sameSizes_processProposerSlashing ok)) proposersOk).trans <|
      flagsFrameLaws.foldlM (fun _ _ _ ok => .of_sizes (frame_processAttesterSlashing ok).flags
        (sameSizes_processAttesterSlashing ok)) slashingsOk
  have headActive : ActiveStep state slashingsDone :=
    (activeStep_operationsInput started).trans <|
      (foldlM_ok_invariant (ActiveStep input) (fun _ _ _ before ok =>
        before.trans (activeStep_processProposerSlashing ok)) (ActiveStep.refl _)
          proposersOk).trans <|
      foldlM_ok_invariant (ActiveStep proposersDone) (fun _ _ _ before ok =>
        before.trans (activeStep_processAttesterSlashing ok)) (ActiveStep.refl _) slashingsOk
  -- The attestations set flags only at active positions.
  have votes : VoteStep slashingsDone attested :=
    foldlM_ok_invariant (VoteStep slashingsDone) (fun _ _ _ before ok =>
      before.trans (voteStep_processAttestation ok)) (VoteStep.refl _) attestedOk
  -- After them: a frame of the flags.
  have tailFrame : FlagsFrame attested after := rest.trans <| by
    split at synced
    · exact flagsFrameLaws.processSyncAggregate synced
    · cases synced
      exact FlagsFrame.refl _
  have kept := activeKept_processBlock computed
  have slot := (frame_processBlock computed).slot
  have current : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot]
  have previous : getPreviousEpoch after = getPreviousEpoch state := by
    simp only [getPreviousEpoch, current]
  have headCurrent : getCurrentEpoch slashingsDone = getCurrentEpoch state := by
    simp only [getCurrentEpoch, headActive.1]
  have headPrevious : getPreviousEpoch slashingsDone = getPreviousEpoch state := by
    simp only [getPreviousEpoch, headCurrent]
  have headKept (epoch : Epoch) (le : epoch ≤ getCurrentEpoch state) (j : Nat) :
      isActiveAt slashingsDone epoch j = isActiveAt state epoch j :=
    headActive.2 epoch (UInt64.le_trans le (getCurrentEpoch_le_activityFixedEpoch state)) j
  have sizes : attested.validators.data.size = slashingsDone.validators.data.size := by
    rw [votes.1]
  intro altair j flags validator present nonzero
  have inside : j < after.validators.data.size := (Array.getElem?_eq_some_iff.mp present).1
  refine ⟨fun found => ?_, fun found => ?_⟩
  · rw [previous]
    refine isActiveValidator_of_activeKept kept (getPreviousEpoch_le state) ?_ present
    obtain ⟨found', inside'⟩ := (tailFrame altair j flags nonzero inside).1 found
    rcases (votes.2.2 altair j flags nonzero).1 found' with old | fresh
    · obtain ⟨old', inside''⟩ := (headFrame altair j flags nonzero (sizes ▸ inside')).1 old
      exact holds.previous_at old' nonzero inside''
    · rwa [headPrevious, headKept _ (getPreviousEpoch_le state)] at fresh
  · rw [current]
    refine isActiveValidator_of_activeKept kept (UInt64.le_refl _) ?_ present
    obtain ⟨found', inside'⟩ := (tailFrame altair j flags nonzero inside).2 found
    rcases (votes.2.2 altair j flags nonzero).2 found' with old | fresh
    · obtain ⟨old', inside''⟩ := (headFrame altair j flags nonzero (sizes ▸ inside')).2 old
      exact holds.current_at old' nonzero inside''
    · rwa [headCurrent, headKept _ (UInt64.le_refl _)] at fresh

/-! ## Upgrades -/

/-- Equal lists keep each flag. -/
private theorem kept_of_eq {xs ys : Array ParticipationFlags} (same : ys = xs) :
    ∀ (i : Nat) flags, ys[i]? = some flags → xs[i]? = some flags ∨ flags = 0 :=
  fun _ _ found => .inl (same ▸ found)

/-- An upgrade that keeps the slot, activity, and each flag or a zero keeps the flags active. -/
private theorem FlagsActive.of_upgrade {post : Fork} {other : BeaconState preset post}
    (holds : FlagsActive state) (altair : .altair ≤ fork)
    (kept : ActiveKept (activityFixedEpoch state) state other) (slot : other.slot = state.slot)
    (le : other.validators.data.size ≤ state.validators.data.size)
    (previous : ∀ altair' : .altair ≤ post, ∀ (i : Nat) flags,
      (other.previousEpochParticipation altair').data[i]? = some flags →
        (state.previousEpochParticipation altair).data[i]? = some flags ∨ flags = 0)
    (current : ∀ altair' : .altair ≤ post, ∀ (i : Nat) flags,
      (other.currentEpochParticipation altair').data[i]? = some flags →
        (state.currentEpochParticipation altair).data[i]? = some flags ∨ flags = 0) :
    FlagsActive other := by
  have currentEq : getCurrentEpoch other = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot]
  have previousEq : getPreviousEpoch other = getPreviousEpoch state := by
    simp only [getPreviousEpoch, currentEq]
  intro altair' j flags validator present nonzero
  have inside : j < state.validators.data.size :=
    Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp present).1 le
  refine ⟨fun found => ?_, fun found => ?_⟩
  · rw [previousEq]
    exact isActiveValidator_of_activeKept kept (getPreviousEpoch_le state)
      (holds.previous_at ((previous altair' j flags found).resolve_right nonzero) nonzero inside)
      present
  · rw [currentEq]
    exact isActiveValidator_of_activeKept kept (UInt64.le_refl _)
      (holds.current_at ((current altair' j flags found).resolve_right nonzero) nonzero inside)
      present

/-- Each signer of a pending attestation is active at the epoch of its slot, at its position. -/
private theorem isActiveAt_of_getPendingAttestingIndices {attestation : PendingAttestation preset}
    {attesters : List ValidatorIndex}
    (computed : getPendingAttestingIndices state attestation = .ok attesters)
    {attester : ValidatorIndex} (mem : attester ∈ attesters) :
    isActiveAt state (computeEpochAtSlot preset attestation.data.slot) attester.toNat = true := by
  simp only [getPendingAttestingIndices, bind_ok_iff] at computed
  obtain ⟨_, committeeOk, listedOk⟩ := computed
  exact isActiveAt_of_getBeaconCommittee committeeOk (mem_of_committeeAttesters listedOk mem)

/-- A translated attestation sets flags of the previous epoch only at its signers. -/
private theorem translateAttestation_positions {altair : .altair ≤ fork}
    {attestation : PendingAttestation preset}
    (computed : translateAttestation state altair attestation = .ok after) {j : Nat}
    {flags : ParticipationFlags}
    (found : (after.previousEpochParticipation altair).data[j]? = some flags) :
    (state.previousEpochParticipation altair).data[j]? = some flags ∨
      ∃ attesters, getPendingAttestingIndices state attestation = .ok attesters ∧
        ∃ attester ∈ attesters, attester.toNat = j := by
  simp only [translateAttestation, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, -, attesters, attestersOk, participation, folded, rfl⟩ := computed
  have positions := foldlM_ok_invariant_of_mem
    (fun (list : EpochParticipation preset fork) => ∀ j flags, list.data[j]? = some flags →
      (state.previousEpochParticipation altair).data[j]? = some flags ∨
        ∃ attester ∈ attesters, attester.toNat = j)
    (fun list attester list' mem holds step => by
      split at step
      · cases step
        intro position value present
        dsimp only at present
        rw [Array.getElem?_set] at present
        split at present
        · exact .inr ⟨attester, mem, by assumption⟩
        · exact holds position value present
      · cases step)
    (fun _ _ present => .inl present) folded j flags found
  rcases positions with old | ⟨attester, mem, place⟩
  · exact .inl old
  · exact .inr ⟨attesters, liftAccessor_ok.mp attestersOk, attester, mem, place⟩

/-- The upgrade to Altair sets flags only at active signers of previous pending attestations. -/
private theorem flagsActive_upgradeToAltair {pre : BeaconState preset .phase0}
    {middle post : BeaconState preset .altair} (wellFormed : PendingWellFormed pre)
    (folded : (pre.previousEpochAttestations (by decide)).data.toList.foldlM
      (fun state attestation => translateAttestation state (by decide) attestation)
      (carryFields config .altair pre (by decide) (by decide)) = .ok middle)
    (validators : post.validators = middle.validators) (slot : post.slot = pre.slot)
    (previous : post.previousEpochParticipation = middle.previousEpochParticipation)
    (current : post.currentEpochParticipation = middle.currentEpochParticipation) :
    FlagsActive post := by
  obtain ⟨zeros, zeros', -⟩ := carryFields_of_lt_altair (config := config) (post := .altair) pre
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨participation, rfl, -⟩ := foldlM_translateAttestation folded
  have epochs := (wellFormed (by decide)).1
  obtain ⟨-, -, translated⟩ := foldlM_ok_invariant_of_mem
    (fun (step : BeaconState preset .altair) =>
      step.validators = (carryFields config .altair pre (by decide) (by decide)).validators ∧
      step.slot = (carryFields config .altair pre (by decide) (by decide)).slot ∧
      ∀ j flags, flags ≠ 0 →
        (step.previousEpochParticipation (by decide)).data[j]? = some flags →
          isActiveAt (carryFields config .altair pre (by decide) (by decide))
            (getPreviousEpoch pre) j = true)
    (fun step attestation next mem ⟨validatorsEq, slotEq, flagged⟩ ok => by
      have positions := fun j flags => translateAttestation_positions (j := j) (flags := flags) ok
      obtain ⟨_, rfl, -⟩ := translateAttestation_spec ok
      refine ⟨validatorsEq, slotEq, fun j flags nonzero found => ?_⟩
      rcases positions j flags found with old | ⟨attesters, attestersOk, attester, chosen, rfl⟩
      · exact flagged j flags nonzero old
      · have active := isActiveAt_of_getPendingAttestingIndices attestersOk chosen
        rw [(epochs attestation (Array.mem_toList_iff.mp mem)).1] at active
        simpa only [isActiveAt, validatorsEq] using active)
    ⟨rfl, rfl, fun j flags nonzero found => by
      rw [show _ = _ from zeros, Array.getElem?_replicate] at found
      split at found
      · exact absurd (Option.some.inj found).symm nonzero
      · cases found⟩
    folded
  have previousEq : getPreviousEpoch post = getPreviousEpoch pre := by
    simp only [getPreviousEpoch, getCurrentEpoch, slot]
  intro altair j flags validator present nonzero
  refine ⟨fun found => ?_, fun found => ?_⟩
  · rw [previousEq]
    rw [previous] at found
    refine isActiveValidator_of_isActiveAt present ?_
    simpa only [isActiveAt, validators] using translated j flags nonzero found
  · rw [current] at found
    rw [show _ = _ from zeros', Array.getElem?_replicate] at found
    split at found
    · exact absurd (Option.some.inj found).symm nonzero
    · cases found

/-- An upgrade keeps the flags set only at active validators.

The upgrade to Altair sets flags only at the attesters of the previous-epoch pending attestations.

The pending attestations must be well formed, which puts their slots in the previous epoch. -/
theorem FlagsActive.of_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (holds : FlagsActive pre.state) (wellFormed : PendingWellFormed pre.state)
    (computed : upgradeNext config checks pre = .ok post) : FlagsActive post.val.state := by
  have kept := activeKept_upgradeNext computed
  have slot := (upgradeFrame_upgradeNext computed).slot
  obtain ⟨fork, pre⟩ := pre
  cases fork with
  | phase0 =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨after, afterOk, rfl⟩ := computed
    obtain ⟨middle, folded, _, rfl⟩ := upgradeToAltair_ok afterOk
    exact flagsActive_upgradeToAltair wellFormed folded rfl slot rfl rfl
  | altair =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact holds.of_upgrade (show Fork.altair ≤ .altair by decide) kept slot
      (Nat.le_refl _) (fun _ => kept_of_eq rfl)
      (fun _ => kept_of_eq rfl)
  | bellatrix =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact holds.of_upgrade (show Fork.altair ≤ .bellatrix by decide) kept slot
      (Nat.le_refl _) (fun _ => kept_of_eq rfl)
      (fun _ => kept_of_eq rfl)
  | shapella =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact holds.of_upgrade (show Fork.altair ≤ .shapella by decide) kept slot
      (Nat.le_refl _) (fun _ => kept_of_eq rfl)
      (fun _ => kept_of_eq rfl)
  | dencun =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨after, afterOk, rfl⟩ := computed
    have sizes := (upgradeToElectra_spec afterOk).1
    simp only [upgradeToElectra, bind_ok_iff] at afterOk
    obtain ⟨_, -, _, -, _, -, _, -, middle, queued, compounded⟩ := afterOk
    -- Both folds keep each flag or zero it.
    have frame := (BlockFrame.foldlM (fun _ _ _ ok => frame_queuePreActivation ok) queued).trans
      (BlockFrame.foldlM (fun _ _ _ ok => frame_queueCompoundingExcess ok) compounded)
    exact holds.of_upgrade (show Fork.altair ≤ .dencun by decide) kept slot
      (Nat.le_of_eq sizes)
      (fun _ i flags found => (frame.flags (by decide) i flags).1 found)
      (fun _ i flags found => (frame.flags (by decide) i flags).2 found)
  | pectra =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨after, afterOk, rfl⟩ := computed
    have validators := (upgradeToFulu_spec afterOk).1
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at afterOk
    obtain ⟨_, -, rfl⟩ := afterOk
    exact holds.of_upgrade (show Fork.altair ≤ .pectra by decide) kept slot
      (Nat.le_of_eq (by rw [validators]))
      (fun _ => kept_of_eq rfl) (fun _ => kept_of_eq rfl)
  | fusaka =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨after, afterOk, rfl⟩ := computed
    have validators := (upgradeToGloas_spec afterOk).1
    unfold upgradeToGloas at afterOk
    obtain ⟨_, -, rest⟩ := bind_ok_iff.mp afterOk
    obtain ⟨_, -, onboarded⟩ := bind_ok_iff.mp rest
    obtain ⟨⟨_, _, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    exact holds.of_upgrade (show Fork.altair ≤ .fusaka by decide) kept slot
      (Nat.le_of_eq (by rw [validators]))
      (fun _ => kept_of_eq rfl) (fun _ => kept_of_eq rfl)
  | glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨after, afterOk, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp afterOk
    have lists := upgradeHezeFields_lists (config := config) pre
    exact holds.of_upgrade (show Fork.altair ≤ .glamsterdam by decide) kept slot
      (Nat.le_of_eq (by rw [lists.1]))
      (fun _ => kept_of_eq lists.2.2.1) (fun _ => kept_of_eq lists.2.2.2.1)
  | _ => cases computed

/-- One step of a chain keeps the flags set only at active validators.

The pending attestations of the state before must be well formed. -/
theorem ChainStep.flagsActive {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) (holds : FlagsActive forked.state)
    (wellFormed : PendingWellFormed forked.state) : FlagsActive after.state := by
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    exact (processUpgrades_induction
      (property := fun forked => FlagsActive forked.state ∧ PendingWellFormed forked.state)
      (forked := ⟨_, advanced⟩)
      (fun held stepOk => ⟨held.1.of_upgradeNext held.2 stepOk,
        PendingWellFormed.of_altair (upgradeNext_altair stepOk).1 _⟩)
      ⟨holds.of_advanceSlot advancedOk, wellFormed.of_advanceSlot advancedOk⟩ upgraded).1
  | block _ _ _ computed => exact holds.of_processBlock (applySignedBlock_ok computed).2.1

/-- A run of steps of a chain keeps the pending attestations well formed.

The least inclusion delay must be positive; it is one slot on mainnet and minimal. -/
theorem pendingWellFormed_of_chainSteps
    (delay : 0 < preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat)
    {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last)
    (wellFormed : PendingWellFormed first.state) : PendingWellFormed last.state := by
  induction steps with
  | refl => exact wellFormed
  | tail _ step held =>
    cases step with
    | slot computed =>
      obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
      exact (held.of_advanceSlot advancedOk).of_processUpgrades upgraded
    | block _ _ _ computed =>
      exact held.of_processBlock delay (applySignedBlock_ok computed).2.1

/-- A run of steps of a chain keeps the flags set only at active validators.

The pending attestations at its start must be well formed.

The least inclusion delay must be positive; it is one slot on mainnet and minimal. -/
theorem flagsActive_of_chainSteps (delay : 0 < preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat)
    {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last)
    (holds : FlagsActive first.state) (wellFormed : PendingWellFormed first.state) :
    FlagsActive last.state := by
  induction steps with
  | refl => exact holds
  | tail before step held =>
    exact step.flagsActive held (pendingWellFormed_of_chainSteps delay before wellFormed)

end EthLib.Consensus
