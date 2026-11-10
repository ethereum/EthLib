module

public import EthLib.Consensus.Proofs.Transition.BlockRoots
public import EthLib.Consensus.Proofs.Transition.TargetVotes

/-!
# Proofs: the target flags across the slot and epoch steps

From Altair each target flag of the state comes from a vote for the link of its epoch.

That vote is signed, and each slot keeps this, the epoch step included.

The slot step writes only the block root at the current slot.

The root at the first slot of a recent epoch stays while it is in the buffer of roots.

The buffer must cover two epochs, as both presets do, and an epoch must have a slot.

The epoch step makes the flags of the current epoch those of the previous epoch.

It clears the flags of the current epoch.

Justification makes the current justified checkpoint the previous one.

It does not run in the first two epochs.

So the proof needs the two justified checkpoints equal in those epochs, which the slots keep.

Gasper §4.4, Definition 4.5, justifies a checkpoint by the stake of the votes for one link.

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
    | exact absurd ‹getCurrentEpoch state ≤ GENESIS_EPOCH + 1› first
    | simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, _, _, _, _, _, _, weighed⟩ := computed
      exact (weighJustificationAndFinalization_checkpoints weighed).1

/-! ## One slot -/

/-- One slot keeps the fork versions, the genesis validators root and the keys.

It never shrinks the registry, and the keys need it below 2^64 validators after the slot. -/
theorem advanceSlot_keys (computed : advanceSlot config checks state = .ok after) :
    after.forkVersions = state.forkVersions ∧
      after.genesisValidatorsRoot = state.genesisValidatorsRoot ∧
      state.validators.data.size ≤ after.validators.data.size ∧
      (after.validators.data.size < 2 ^ 64 → KeysKept state after) := by
  obtain ⟨next, cached, epoched, -, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  suffices kept : epoched.forkVersions = cached.forkVersions ∧
      epoched.genesisValidatorsRoot = cached.genesisValidatorsRoot ∧
      cached.validators.data.size ≤ epoched.validators.data.size ∧
      (epoched.validators.data.size < 2 ^ 64 → KeysKept cached epoched) by
    obtain ⟨forkVersions, root, grows, keys⟩ := kept
    refine ⟨forkVersions.trans cachedFrame.forkVersions,
      root.trans cachedFrame.genesisValidatorsRoot,
      Nat.le_trans cachedFrame.registryGrows grows, fun small => ?_⟩
    exact (cachedFrame.keysKept (Nat.lt_of_le_of_lt grows small)).trans
      ((keys small).trans fun _ validator found => ⟨validator, found, rfl⟩)
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    obtain ⟨-, -, -, -, -, validators, forkVersions, root, -, -⟩ :=
      processJustificationAndFinalization_keeps justifiedOk
    refine ⟨frame.forkVersions.trans forkVersions, frame.genesisValidatorsRoot.trans root,
      validators ▸ frame.registryGrows, fun small => ?_⟩
    refine KeysKept.trans (fun index validator found => ⟨validator, ?_, rfl⟩)
      (frame.keysKept small)
    rw [getValidator, validators]
    exact found
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact ⟨rfl, rfl, Nat.le_refl _, fun _ => KeysKept.refl _⟩

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

/-- The first slot of the current or the previous epoch is less than two epochs back.

So it stays in a buffer of roots that covers two epochs, at the next slot. -/
private theorem recent_of_epoch (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
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

/-- One slot keeps each target flag backed by a signed vote for the link of its epoch.

The epochs must have slots, and the buffer of roots must cover two epochs.

The two justified checkpoints must be equal in the first two epochs.

The registry must stay below 2^64 validators after the slot. -/
theorem TargetFlagsSigned.of_advanceSlot
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (early : JustifiedEarly state) (small : after.validators.data.size < 2 ^ 64)
    (holds : TargetFlagsSigned config checks state)
    (computed : advanceSlot config checks state = .ok after) :
    TargetFlagsSigned config checks after := by
  obtain ⟨forkVersions, genesisRoot, -, keys⟩ := advanceSlot_keys computed
  have signed : ∀ vote, SignedVote config checks state vote →
      SignedVote config checks after vote :=
    fun _ one => one.of_keys forkVersions genesisRoot (keys small)
  have roots : ∀ {epoch : Epoch} {root : Root}, getBlockRoot state epoch = .ok root →
      (epoch = getCurrentEpoch state ∨ epoch = getPreviousEpoch state) →
      getBlockRoot after epoch = .ok root :=
    fun read near => getBlockRoot_advanceSlot computed read (recent_of_epoch positive window near)
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
          obtain ⟨vote, ⟨index, epoch, source, rootOk⟩, voted⟩ :=
            holds altair true position ⟨flags, old, set⟩
          refine ⟨vote, ⟨index, ?_, ?_, roots rootOk (.inl epoch)⟩, signed vote voted⟩
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
      obtain ⟨vote, ⟨index, epoch, source, rootOk⟩, voted⟩ :=
        holds altair false position ⟨flags, found, set⟩
      refine ⟨vote, ⟨index, epoch.trans previousEq.symm, ?_, roots rootOk (.inr epoch)⟩,
        signed vote voted⟩
      exact source.trans cachedFrame.previousJustified.symm
    · rw [cachedCurrent] at found
      obtain ⟨vote, ⟨index, epoch, source, rootOk⟩, voted⟩ :=
        holds altair true position ⟨flags, found, set⟩
      refine ⟨vote, ⟨index, epoch.trans currentEq.symm, ?_, roots rootOk (.inl epoch)⟩,
        signed vote voted⟩
      exact source.trans cachedFrame.currentJustified.symm

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

/-- Slots keep each target flag backed by a signed vote for its link.

The epochs must have slots, and the buffer of roots must cover two epochs.

The two justified checkpoints must be equal in the first two epochs before the slots.

The registry must stay below 2^64 validators after the slots. -/
theorem TargetFlagsSigned.of_advanceSlots (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    ∀ {count : Nat} {state after : BeaconState preset fork}, JustifiedEarly state →
      after.validators.data.size < 2 ^ 64 → TargetFlagsSigned config checks state →
      advanceSlots config checks count state = .ok after → TargetFlagsSigned config checks after
  | 0, state, after, _, _, holds, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ holds
  | count + 1, state, after, early, small, holds, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact TargetFlagsSigned.of_advanceSlots positive window (early.of_advanceSlot nextOk) small
      (holds.of_advanceSlot positive window early
        (Nat.lt_of_le_of_lt (advanceSlots_registryGrows rest) small) nextOk) rest

/-- A block that the transition accepts keeps the justified checkpoints equal in early epochs.

That holds in the first two epochs, through the slots before the block and the block itself. -/
theorem JustifiedEarly.of_stateTransition {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (early : JustifiedEarly state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    JustifiedEarly after := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, -, slotsOk⟩ := slotsOk
  exact (early.of_advanceSlots slotsOk).of_frame (frame_processBlock blockOk)

/-- A block that the transition accepts keeps each target flag backed by a signed vote.

That vote is for the link of the epoch of the flag.

The slots before the block keep that, and so does the block itself.

The epochs must have slots, and the buffer of roots must cover two epochs, as in both presets.

The two justified checkpoints must be equal in the first two epochs before the block.

The registry must stay below 2^64 validators after the block. -/
theorem TargetFlagsSigned.of_stateTransition {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (early : JustifiedEarly state) (small : after.validators.data.size < 2 ^ 64)
    (holds : TargetFlagsSigned config checks state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    TargetFlagsSigned config checks after := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, -, slotsOk⟩ := slotsOk
  obtain ⟨votes, frame, -⟩ := voteFrame_processBlock blockOk
  exact (TargetFlagsSigned.of_advanceSlots positive window early
    (Nat.lt_of_le_of_lt frame.registryGrows small) holds slotsOk).of_voteFrame small frame

end EthLib.Consensus
