module

public import EthLib.Consensus.Proofs.Transition.BlockRoots
public import EthLib.Consensus.Proofs.Transition.TargetVotes

/-!
# Proofs: the target flags across the slot and epoch steps

From Altair each target flag of the state comes from a vote of a set for the link of its epoch.

Each slot keeps this, the epoch step included.

In the buffer of block roots, the slot step writes only the entry at the current slot.

The root at the first slot of a recent epoch stays while it is in the buffer of roots.

The buffer must cover two epochs, as both presets do, and an epoch must have at least one slot.

The epoch step makes the flags of the current epoch those of the previous epoch.

It clears the flags of the current epoch.

Justification makes the current justified checkpoint the previous one.

It does not run in the first two epochs.

So the proof needs the two justified checkpoints equal in those epochs, which the slots keep.

Gasper §4.4, Definitions 4.5 and 4.6, justify a checkpoint by a supermajority link.

The votes for that link carry more than 2/3 of the stake.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- In the first two epochs, the previous and the current justified checkpoints are equal. -/
def JustifiedEarly (state : BeaconState preset fork) : Prop :=
  getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
    state.previousJustifiedCheckpoint = state.currentJustifiedCheckpoint

/-! ## Justification -/

/-- Justification makes the old current justified checkpoint the previous one.

In the first two epochs it changes nothing, so there the two must already be equal. -/
theorem JustifiedEarly.previousJustified_of_justification (early : JustifiedEarly state)
    (computed : processJustificationAndFinalization state = .ok after) :
    after.previousJustifiedCheckpoint = state.currentJustifiedCheckpoint := by
  by_cases first : getCurrentEpoch state ≤ GENESIS_EPOCH + 1
  · rw [processJustificationAndFinalization_early_eq first computed]
    exact early first
  unfold processJustificationAndFinalization at computed
  split at computed
  · unfold processJustificationAndFinalizationAltair at computed
    simp only [first, ↓reduceIte] at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, weighed⟩ := computed
    exact (weighJustificationAndFinalization_checkpoints weighed).1
  all_goals first
    | simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, _, _, _, _, _, _, weighed⟩ := computed
      exact (weighJustificationAndFinalization_checkpoints weighed).1

/-! ## One slot -/

/-- One slot keeps the fork versions, the genesis validators root and the keys.

It never shrinks the registry. -/
theorem advanceSlot_keys (computed : advanceSlot config checks state = .ok after) :
    after.forkVersions = state.forkVersions ∧
      after.genesisValidatorsRoot = state.genesisValidatorsRoot ∧
      state.validators.data.size ≤ after.validators.data.size ∧
      KeysKept state after := by
  obtain ⟨next, cached, epoched, -, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  suffices kept : epoched.forkVersions = cached.forkVersions ∧
      epoched.genesisValidatorsRoot = cached.genesisValidatorsRoot ∧
      cached.validators.data.size ≤ epoched.validators.data.size ∧
      KeysKept cached epoched by
    obtain ⟨forkVersions, root, grows, keys⟩ := kept
    refine ⟨forkVersions.trans cachedFrame.forkVersions,
      root.trans cachedFrame.genesisValidatorsRoot,
      Nat.le_trans cachedFrame.registryGrows grows, ?_⟩
    exact cachedFrame.keysKept.trans
      (keys.trans fun _ validator found => ⟨validator, found, rfl⟩)
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    obtain ⟨-, -, -, -, -, validators, forkVersions, root, -, -⟩ :=
      processJustificationAndFinalization_keeps justifiedOk
    refine ⟨frame.forkVersions.trans forkVersions, frame.genesisValidatorsRoot.trans root,
      validators ▸ frame.registryGrows, ?_⟩
    exact (KeysKept.of_validators (by simp only [validators])).trans frame.keysKept
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact ⟨rfl, rfl, Nat.le_refl _, KeysKept.refl _⟩

/-- A frame keeps the two justified checkpoints equal in the first two epochs. -/
theorem JustifiedEarly.of_frame (frame : Frame state after) (early : JustifiedEarly state) :
    JustifiedEarly after := by
  unfold JustifiedEarly getCurrentEpoch at early ⊢
  rw [frame.slot, frame.previousJustified, frame.currentJustified]
  exact early

/-- One slot keeps the two justified checkpoints equal in the first two epochs.

The epoch step at the end of the first epoch does not run justification. -/
theorem JustifiedEarly.of_advanceSlot (early : JustifiedEarly state)
    (computed : advanceSlot config checks state = .ok after) : JustifiedEarly after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  have cachedEarly := early.of_frame cachedFrame
  have one : (GENESIS_EPOCH + 1 : Epoch).toNat = 1 := by decide
  have cachedEpoch := getCurrentEpoch_toNat cached
  rw [cachedFrame.slot] at cachedEpoch
  intro afterEarly
  have afterEarly' := UInt64.le_iff_toNat_le.mp afterEarly
  rw [getCurrentEpoch_toNat, one] at afterEarly'
  dsimp only at afterEarly' ⊢
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epochs := nextSlot_epoch_of_boundary sum boundary
    have cachedFirst : getCurrentEpoch cached ≤ GENESIS_EPOCH + 1 :=
      UInt64.le_iff_toNat_le.mpr (by rw [one, cachedEpoch]; omega)
    obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    obtain rfl := processJustificationAndFinalization_early_eq cachedFirst justifiedOk
    exact frame.previousJustified.trans
      ((cachedEarly cachedFirst).trans frame.currentJustified.symm)
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact cachedEarly (UInt64.le_iff_toNat_le.mpr (by
      rw [one, cachedEpoch, ← nextSlot_epoch_of_inside sum inside]
      exact afterEarly'))

/-- Once justification runs, the previous justified epoch is below the previous epoch.

It runs from the third epoch on. -/
def JustifiedSeparated (state : BeaconState preset fork) : Prop :=
  GENESIS_EPOCH + 1 < getCurrentEpoch state →
    state.previousJustifiedCheckpoint.epoch < getPreviousEpoch state

/-- A frame keeps the previous justified epoch below the previous epoch. -/
theorem JustifiedSeparated.of_frame (frame : Frame state after)
    (separated : JustifiedSeparated state) : JustifiedSeparated after := by
  unfold JustifiedSeparated getPreviousEpoch getCurrentEpoch at separated ⊢
  rw [frame.slot, frame.previousJustified]
  exact separated

/-- One slot keeps the previous justified epoch below the previous epoch once justification runs.

In the first two epochs the two justified checkpoints must be equal.

The current justified epoch must be at most the previous epoch. -/
theorem JustifiedSeparated.of_advanceSlot (early : JustifiedEarly state)
    (settled : JustifiedSettled state) (separated : JustifiedSeparated state)
    (computed : advanceSlot config checks state = .ok after) : JustifiedSeparated after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  have one : (GENESIS_EPOCH + 1 : Epoch).toNat = 1 := by decide
  have cachedEpoch := getCurrentEpoch_toNat cached
  rw [cachedFrame.slot] at cachedEpoch
  have afterEpoch := getCurrentEpoch_toNat { epoched with slot := next }
  have afterPrevious := getPreviousEpoch_toNat { epoched with slot := next }
  dsimp only at afterEpoch afterPrevious ⊢
  intro late
  have late' := UInt64.lt_iff_toNat_lt.mp late
  rw [getCurrentEpoch_toNat, one] at late'
  dsimp only at late'
  apply UInt64.lt_iff_toNat_lt.mpr
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epochs := nextSlot_epoch_of_boundary sum boundary
    obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    have settled' := UInt64.le_iff_toNat_le.mp settled
    rw [getPreviousEpoch_toNat, getCurrentEpoch_toNat] at settled'
    rw [afterPrevious, afterEpoch, epochs, frame.previousJustified,
      (early.of_frame cachedFrame).previousJustified_of_justification justifiedOk,
      cachedFrame.currentJustified]
    omega
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have epochs := nextSlot_epoch_of_inside sum inside
    have below := UInt64.lt_iff_toNat_lt.mp
      (separated (UInt64.lt_iff_toNat_lt.mpr (by rw [one, getCurrentEpoch_toNat]; omega)))
    rw [getPreviousEpoch_toNat, getCurrentEpoch_toNat] at below
    rw [afterPrevious, afterEpoch, epochs, cachedFrame.previousJustified]
    exact below

/-- The first slot of the current or the previous epoch is less than two epochs back.

So it stays in a buffer of roots that covers two epochs, at the next slot. -/
theorem slot_lt_epoch_add_historical (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {epoch : Epoch} (near : epoch = getCurrentEpoch state ∨ epoch = getPreviousEpoch state) :
    state.slot.toNat <
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
  have split := Nat.div_add_mod state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  have small := Nat.mod_lt state.slot.toNat positive
  have current := getCurrentEpoch_toNat state
  have previous := getPreviousEpoch_toNat state
  rw [current] at previous
  rw [Nat.mul_comm] at split
  rcases near with rfl | rfl
  · rw [current]
    omega
  · rw [previous, Nat.sub_one_mul]
    omega

/-- The caching of a slot keeps each target flag backed by a vote of the set for its link.

An epoch must have at least one slot, and the buffer of roots must cover two epochs. -/
theorem TargetFlagsVoted.of_processSlot {votes : Set (ValidatorIndex × AttestationData)}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (holds : TargetFlagsVoted votes state)
    (computed : processSlot state = .ok after) : TargetFlagsVoted votes after := by
  have frame := frame_processSlot computed
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  intro altair current position flagged
  have participation := processSlot_participation computed
  have same : recentParticipation after altair current =
      recentParticipation state altair current := by
    cases current <;> simp only [recentParticipation, participation.1, participation.2]
  rw [same] at flagged
  obtain ⟨vote, voted, index, epoch, source, rootOk⟩ := holds altair current position flagged
  refine ⟨vote, voted, index, ?_, ?_, ?_⟩
  · rw [currentEq, previousEq]
    exact epoch
  · rw [frame.currentJustified, frame.previousJustified]
    exact source
  · have near : vote.2.target.epoch = getCurrentEpoch state ∨
        vote.2.target.epoch = getPreviousEpoch state := by
      cases current
      · exact .inr epoch
      · exact .inl epoch
    rw [getBlockRoot_processSlot computed (slot_lt_epoch_add_historical positive window near)]
    exact rootOk

/-- One slot keeps each target flag backed by a vote of the set for the link of its epoch.

An epoch must have at least one slot, and the buffer of roots must cover two epochs.

The two justified checkpoints must be equal in the first two epochs. -/
theorem TargetFlagsVoted.of_advanceSlot {votes : Set (ValidatorIndex × AttestationData)}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (early : JustifiedEarly state) (holds : TargetFlagsVoted votes state)
    (computed : advanceSlot config checks state = .ok after) :
    TargetFlagsVoted votes after := by
  have roots : ∀ {epoch : Epoch} {root : Root}, getBlockRoot state epoch = .ok root →
      (epoch = getCurrentEpoch state ∨ epoch = getPreviousEpoch state) →
      getBlockRoot after epoch = .ok root :=
    fun read near =>
      getBlockRoot_advanceSlot computed read (slot_lt_epoch_add_historical positive window near)
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  have cachedEarly' := early.of_frame cachedFrame
  obtain ⟨cachedPrevious, cachedCurrent⟩ := processSlot_participation cachedOk
  have stateEpoch := getCurrentEpoch_toNat state
  have afterEpoch := getCurrentEpoch_toNat { epoched with slot := next }
  dsimp only at afterEpoch
  intro altair current position flagged
  obtain ⟨flags, found, set⟩ := flagged
  unfold recentParticipation at found
  dsimp only at found
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epochs := nextSlot_epoch_of_boundary sum boundary
    have previousEq : getPreviousEpoch { epoched with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getPreviousEpoch_toNat, afterEpoch, stateEpoch, epochs]
      rfl
    simp only [processEpoch, altair, ↓reduceDIte] at epochedOk
    obtain ⟨justified, rooted, justifiedOk, head, tail⟩ := processEpochAltair_split epochedOk
    obtain ⟨-, -, -, -, -, -, -, -, -, justifiedCurrent⟩ :=
      processJustificationAndFinalization_keeps justifiedOk
    have previousJustified := (cachedEarly'.previousJustified_of_justification justifiedOk)
    cases current
    · rcases (tail.flags altair position flags).1 found with rotated | rfl
      · rcases (head.flags altair position flags).2 rotated with old | rfl
        · rw [justifiedCurrent, cachedCurrent] at old
          obtain ⟨vote, voted, index, epoch, source, rootOk⟩ :=
            holds altair true position ⟨flags, old, set⟩
          refine ⟨vote, voted, index, ?_, ?_, roots rootOk (.inl epoch)⟩
          · exact epoch.trans previousEq.symm
          · exact source.trans <|
              (cachedFrame.currentJustified.symm.trans previousJustified.symm).trans
                (head.previousJustified.symm.trans tail.previousJustified.symm)
        · exact absurd set (by decide)
      · exact absurd set (by decide)
    · rcases (tail.flags altair position flags).2 found with rotated | rfl
      · simp only [processParticipationFlagUpdates, Array.getElem?_replicate] at rotated
        split at rotated
        · cases rotated
          exact absurd set (by decide)
        · cases rotated
      · exact absurd set (by decide)
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have currentEq : getCurrentEpoch { cached with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [afterEpoch, stateEpoch]
      exact nextSlot_epoch_of_inside sum inside
    have previousEq : getPreviousEpoch { cached with slot := next } = getPreviousEpoch state := by
      unfold getPreviousEpoch
      rw [currentEq]
    cases current
    · rw [cachedPrevious] at found
      obtain ⟨vote, voted, index, epoch, source, rootOk⟩ :=
        holds altair false position ⟨flags, found, set⟩
      exact ⟨vote, voted, index, epoch.trans previousEq.symm,
        source.trans cachedFrame.previousJustified.symm, roots rootOk (.inr epoch)⟩
    · rw [cachedCurrent] at found
      obtain ⟨vote, voted, index, epoch, source, rootOk⟩ :=
        holds altair true position ⟨flags, found, set⟩
      exact ⟨vote, voted, index, epoch.trans currentEq.symm,
        source.trans cachedFrame.currentJustified.symm, roots rootOk (.inl epoch)⟩

/-! ## Slots and blocks -/

/-- Slots never shrink the registry. -/
theorem advanceSlots_registryGrows :
    ∀ {count : Nat} {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      state.validators.data.size ≤ after.validators.data.size
  | 0, state, after, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Nat.le_refl _
  | count + 1, state, after, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact Nat.le_trans (advanceSlot_keys nextOk).2.2.1 (advanceSlots_registryGrows rest)

/-- Slots keep the two justified checkpoints equal in the first two epochs. -/
theorem JustifiedEarly.of_advanceSlots :
    ∀ {count : Nat} {state after : BeaconState preset fork}, JustifiedEarly state →
      advanceSlots config checks count state = .ok after → JustifiedEarly after
  | 0, state, after, early, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ early
  | count + 1, state, after, early, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact JustifiedEarly.of_advanceSlots (early.of_advanceSlot nextOk) rest

/-- Slots keep the previous justified epoch below the previous epoch once justification runs.

The state before them must keep the invariant of valid blocks.

In its first two epochs, its two justified checkpoints must be equal. -/
theorem JustifiedSeparated.of_advanceSlots :
    ∀ {count : Nat} {state after : BeaconState preset fork}, Invariant state →
      JustifiedEarly state → JustifiedSeparated state →
      advanceSlots config checks count state = .ok after → JustifiedSeparated after := by
  intro count
  induction count with
  | zero =>
    intro state after _ _ separated computed
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ separated
  | succ count ih =>
    intro state after holds early separated computed
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact ih (advanceSlot_invariant holds nextOk).1 (early.of_advanceSlot nextOk)
      (separated.of_advanceSlot early holds.settled nextOk) rest

/-- Slots keep each target flag backed by a vote of the set for its link.

An epoch must have at least one slot, and the buffer of roots must cover two epochs.

The two justified checkpoints must be equal in the first two epochs before the slots. -/
theorem TargetFlagsVoted.of_advanceSlots {votes : Set (ValidatorIndex × AttestationData)}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    ∀ {count : Nat} {state after : BeaconState preset fork}, JustifiedEarly state →
      TargetFlagsVoted votes state → advanceSlots config checks count state = .ok after →
        TargetFlagsVoted votes after
  | 0, state, after, _, holds, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ holds
  | count + 1, state, after, early, holds, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact TargetFlagsVoted.of_advanceSlots positive window (early.of_advanceSlot nextOk)
      (holds.of_advanceSlot positive window early nextOk) rest

/-- A block that the transition accepts keeps the two justified checkpoints equal in early epochs.

Those are the first two epochs, and the slots before the block keep that, as the block does. -/
theorem JustifiedEarly.of_stateTransition {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (early : JustifiedEarly state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    JustifiedEarly after := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, -, slotsOk⟩ := slotsOk
  exact (early.of_advanceSlots slotsOk).of_frame (frame_processBlock blockOk)

/-- A block that the transition accepts keeps the previous justified epoch below the previous one.

That holds once justification runs, and the slots before the block keep it too.

The state before must keep the invariant of valid blocks.

In its first two epochs, its two justified checkpoints must be equal. -/
theorem JustifiedSeparated.of_stateTransition {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (holds : Invariant state) (early : JustifiedEarly state)
    (separated : JustifiedSeparated state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    JustifiedSeparated after := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, -, slotsOk⟩ := slotsOk
  exact (JustifiedSeparated.of_advanceSlots holds early separated slotsOk).of_frame
    (frame_processBlock blockOk)

end EthLib.Consensus
