module

public import EthLib.Consensus.Proofs.ForkChoice.BlockRuns
public import EthLib.Consensus.Proofs.ForkChoice.CheckpointBlocks

/-!
# Proofs: the realized justification of held blocks

A state transition never lowers the current justified epoch of a state that keeps the invariant.

So along a chain of held blocks the realized justification only grows.

A block's voting source is its realized justification, or the unrealized one of its pull-up.

So every voting source above a block is at least the block's realized justification.

The store's realized finality is the anchor's, or strictly before its realized justification.

The store's realized justification is at most its unrealized justification.

Justification finalizes a checkpoint only below one it justifies at the same time.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Fork}

section Transition

variable {config : Config} {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- Justification and finalization cannot lower a settled current justified epoch. -/
private theorem processJustificationAndFinalization_currentJustified_mono
    (settled : JustifiedSettled state)
    (computed : processJustificationAndFinalization state = .ok after) :
    state.currentJustifiedCheckpoint.epoch ≤ after.currentJustifiedCheckpoint.epoch := by
  rcases processJustificationAndFinalization_currentJustified computed with same | ⟨recent, -⟩
  · rw [same]
    exact UInt64.le_refl _
  · rcases recent with previous | current
    · rw [previous]
      exact settled
    · rw [current]
      exact UInt64.le_trans settled (getPreviousEpoch_le state)

/-- An epoch transition cannot lower the current justified epoch of an invariant state. -/
private theorem processEpoch_currentJustified_mono (holds : Invariant state)
    (computed : processEpoch config checks state = .ok after) :
    state.currentJustifiedCheckpoint.epoch ≤ after.currentJustifiedCheckpoint.epoch := by
  obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame computed
  rw [frame.toFrame.currentJustified]
  exact processJustificationAndFinalization_currentJustified_mono holds.settled justifiedOk

/-- Advancing one slot cannot lower the current justified epoch of an invariant state. -/
private theorem advanceSlot_currentJustified_mono (holds : Invariant state)
    (computed : advanceSlot config checks state = .ok after) :
    state.currentJustifiedCheckpoint.epoch ≤ after.currentJustifiedCheckpoint.epoch := by
  obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have frame := frame_processSlot cachedOk
  change state.currentJustifiedCheckpoint.epoch ≤ epoched.currentJustifiedCheckpoint.epoch
  rw [← frame.currentJustified]
  unfold epochIfLast at epochedOk
  split at epochedOk
  · exact processEpoch_currentJustified_mono (frame.invariant holds) epochedOk
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    rw [← epochedOk]
    exact UInt64.le_refl _

/-- Any number of slot steps cannot lower the current justified epoch of an invariant state. -/
theorem advanceSlots_currentJustified_mono {count : Nat} (holds : Invariant state)
    (computed : advanceSlots config checks count state = .ok after) :
    state.currentJustifiedCheckpoint.epoch ≤ after.currentJustifiedCheckpoint.epoch :=
  (advanceSlots_invariant_of (fun s t => s.currentJustifiedCheckpoint.epoch ≤
      t.currentJustifiedCheckpoint.epoch) (fun _ => UInt64.le_refl _)
    (fun _ one two => UInt64.le_trans one two) advanceSlot_currentJustified_mono holds
    computed).2.2

/-- Advancing to a slot cannot lower the current justified epoch of an invariant state. -/
private theorem processSlots_currentJustified_mono {slot : Slot} (holds : Invariant state)
    (computed : processSlots config checks state slot = .ok after) :
    state.currentJustifiedCheckpoint.epoch ≤ after.currentJustifiedCheckpoint.epoch := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact advanceSlots_currentJustified_mono holds advanced

/-- A successful state transition cannot lower an invariant state's current justified epoch.

Block processing keeps the checkpoint produced by the slot steps.

The result holds for every signature check and either value of the result-validation flag.
-/
theorem stateTransition_currentJustified_mono
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool} (holds : Invariant state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    state.currentJustifiedCheckpoint.epoch ≤ after.currentJustifiedCheckpoint.epoch := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  rw [(frame_processBlock blockOk).currentJustified]
  exact processSlots_currentJustified_mono holds slotsOk

end Transition

/-- A pair whose finality is at most the anchor epoch `a`, or before its justification. -/
private def PairBelow (a : ℕ) (justified finalized : Checkpoint) : Prop :=
  finalized.epoch.toNat ≤ a ∨ finalized.epoch.toNat < justified.epoch.toNat

/-- A state whose finality is at most the anchor epoch `a`, or before its current justification. -/
private def FinalBelow (a : ℕ) (state : BeaconState preset fork) : Prop :=
  PairBelow a state.currentJustifiedCheckpoint state.finalizedCheckpoint

/-- Bit 0 ties the current justified epoch to the previous epoch.

Past two epochs after the anchor, a set bit 0 makes the current justified epoch the previous one. -/
private def BitLinked (a : ℕ) (state : BeaconState preset fork) : Prop :=
  (getCurrentEpoch state).toNat ≤ a + 2 ∨
    (state.justificationBits.bits[0] = true →
      state.currentJustifiedCheckpoint.epoch.toNat + 1 = (getCurrentEpoch state).toNat)

section Transition

variable {config : Config} {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork} {a : ℕ}

/-- A justification step keeps the finality order, and links bit 0 when it weighs the votes. -/
private theorem justification_step (holds : Invariant state) (below : FinalBelow a state)
    (linked : BitLinked a state)
    (computed : processJustificationAndFinalization state = .ok after) :
    FinalBelow a after ∧
      (((getCurrentEpoch state).toNat ≤ 1 ∧ after = state) ∨
        (after.justificationBits.bits[0] = true →
          after.currentJustifiedCheckpoint.epoch.toNat = (getCurrentEpoch state).toNat)) := by
  rcases processJustificationAndFinalization_reads computed with ⟨early, same⟩ |
    ⟨-, -, -, total, previous, current, -, -, -, -, -, weighed⟩
  · subst same
    refine ⟨below, .inl ⟨?_, rfl⟩⟩
    have := UInt64.le_iff_toNat_le.mp early
    rwa [toNat_genesisEpoch_add_one] at this
  obtain ⟨threshold, previousWeight, currentWeight, thresholdOk, previousOk, currentOk, bit0,
    bit1, -, -, finalized⟩ := weighJustificationAndFinalization_bits weighed
  have mono := UInt64.le_iff_toNat_le.mp
    (processJustificationAndFinalization_currentJustified_mono holds.settled computed)
  have ordered := holds.ordered
  have previousLe := UInt64.le_iff_toNat_le.mp ordered.2
  have linkAfter : after.justificationBits.bits[0] = true →
      after.currentJustifiedCheckpoint.epoch.toNat = (getCurrentEpoch state).toNat := by
    intro set
    obtain ⟨-, root, -, eq⟩ := bit0 set
    rw [eq]
  refine ⟨?_, .inr linkAfter⟩
  unfold FinalBelow PairBelow at below ⊢
  rcases finalized with same | ⟨same, set, rule⟩ | ⟨same, set, rule⟩
  · rw [same]
    omega
  · -- The old current justified checkpoint is finalized below the newly justified current epoch.
    rw [same, linkAfter set]
    omega
  · -- The old previous justified checkpoint is finalized below a justified previous epoch.
    rw [same]
    by_cases near : (getCurrentEpoch state).toNat ≤ a + 2
    · omega
    have link := linked.resolve_left near
    rcases bit1 set with ⟨passed, -⟩ | old
    · rcases weighJustificationAndFinalization_currentJustified weighed with ⟨-, failed⟩ |
        ⟨which, threshold', weight, thresholdOk', weightOk, -, epochEq, -⟩
      · have below := failed false threshold previousWeight thresholdOk (by simpa using previousOk)
        exact absurd passed (UInt64.not_le.mpr below)
      · have previousNat := getPreviousEpoch_toNat state
        have epochNat := congrArg UInt64.toNat epochEq
        cases which <;> simp only [Bool.false_eq_true, ↓reduceIte] at epochNat <;> omega
    · have := link old
      omega

/-- Processing a slot keeps both state properties. -/
private theorem advanceSlot_keeps (holds : Invariant state) (below : FinalBelow a state)
    (linked : BitLinked a state) (computed : advanceSlot config checks state = .ok after) :
    FinalBelow a after ∧ BitLinked a after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have frame := frame_processSlot cachedOk
  have cachedEpoch : getCurrentEpoch cached = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have cachedBelow : FinalBelow a cached := by
    unfold FinalBelow
    rw [frame.currentJustified, frame.finalized]
    exact below
  have cachedLinked : BitLinked a cached := by
    unfold BitLinked
    rw [cachedEpoch, frame.currentJustified, frame.justificationBits]
    exact linked
  have epochNat (s : BeaconState preset fork) :
      (getCurrentEpoch { s with slot := next }).toNat =
        next.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    rw [getCurrentEpoch_toNat]
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    obtain ⟨justified, justifiedOk, rest⟩ := processEpoch_frame epochedOk
    obtain ⟨justifiedBelow, link⟩ :=
      justification_step (frame.invariant holds) cachedBelow cachedLinked justifiedOk
    have step := nextSlot_epoch_of_boundary sum boundary
    have cachedNat := getCurrentEpoch_toNat cached
    rw [frame.slot] at cachedNat
    refine ⟨?_, ?_⟩
    · unfold FinalBelow
      change PairBelow a epoched.currentJustifiedCheckpoint epoched.finalizedCheckpoint
      rw [rest.toFrame.currentJustified, rest.toFrame.finalized]
      exact justifiedBelow
    · unfold BitLinked
      rw [epochNat]
      change _ ∨ (epoched.justificationBits.bits[0] = true →
        epoched.currentJustifiedCheckpoint.epoch.toNat + 1 = _)
      rw [rest.toFrame.currentJustified, rest.toFrame.justificationBits]
      rcases link with ⟨early, -⟩ | link
      · left
        omega
      · right
        intro set
        have := link set
        omega
  · cases Except.ok.inj epochedOk
    have step := nextSlot_epoch_of_inside sum ‹_›
    have stateNat := getCurrentEpoch_toNat state
    refine ⟨cachedBelow, ?_⟩
    unfold BitLinked at cachedLinked ⊢
    rw [epochNat]
    change _ ∨ (cached.justificationBits.bits[0] = true →
      cached.currentJustifiedCheckpoint.epoch.toNat + 1 = _)
    rw [cachedEpoch] at cachedLinked
    rcases cachedLinked with early | link
    · left
      omega
    · right
      intro set
      have := link set
      omega

/-- A state transition keeps both state properties. -/
private theorem stateTransition_keeps {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} (holds : Invariant state) (below : FinalBelow a state)
    (linked : BitLinked a state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    FinalBelow a after ∧ BitLinked a after := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  have frame := frame_processBlock blockOk
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, slotsOk⟩ := slotsOk
  obtain ⟨advancedBelow, advancedLinked⟩ := (advanceSlots_invariant_of
    (fun s t => FinalBelow a s ∧ BitLinked a s → FinalBelow a t ∧ BitLinked a t)
    (fun _ kept => kept) (fun _ one two kept => two (one kept))
    (fun holds ok kept => advanceSlot_keeps holds kept.1 kept.2 ok) holds slotsOk).2.2
    ⟨below, linked⟩
  refine ⟨?_, ?_⟩
  · unfold FinalBelow
    rw [frame.currentJustified, frame.finalized]
    exact advancedBelow
  · unfold BitLinked
    have epochEq : getCurrentEpoch after = getCurrentEpoch advanced := by
      simp only [getCurrentEpoch, frame.slot]
    rw [epochEq, frame.currentJustified, frame.justificationBits]
    exact advancedLinked

end Transition

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork}

/-- A cached unrealized justification is no older than the stored realized justification. -/
private theorem walk_realized_le_unrealized {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    {root : Root} {state : BeaconState preset fork} {checkpoint : Checkpoint}
    (stored : store.blockStates[root]? = some state)
    (entry : store.unrealizedJustifications[root]? = some checkpoint) :
    state.currentJustifiedCheckpoint.epoch ≤ checkpoint.epoch := by
  rcases reachable.unrealizedJustification_origin entry with ⟨epoch, held⟩ |
    ⟨base, pulled, held, run, same⟩
  · rw [stored, Option.some.injEq] at held
    subst state
    rw [epoch]
    exact UInt64.le_trans sound.settled (getPreviousEpoch_le _)
  · rw [stored, Option.some.injEq] at held
    subst base
    rw [same]
    exact processJustificationAndFinalization_currentJustified_mono
      ((reachable.ordered sound).2 stored).settled run

/-- Realized justification cannot decrease along a held descendant chain. -/
private theorem walk_realized_mono {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (before : fork < .glamsterdam)
    {root tip : Root} {block : BeaconBlock preset fork}
    {base state : BeaconState preset fork}
    (known : store.blocks[root]? = some block)
    (baseStored : store.blockStates[root]? = some base)
    (tipStored : store.blockStates[tip]? = some state)
    (descends : store.isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true) :
    base.currentJustifiedCheckpoint.epoch ≤ state.currentJustifiedCheckpoint.epoch := by
  have rel := reachable.relation_of_getAncestor
    (fun s t => Invariant s →
      Invariant t ∧ s.currentJustifiedCheckpoint.epoch ≤ t.currentJustifiedCheckpoint.epoch)
    (fun _ holds => ⟨holds, UInt64.le_refl _⟩)
    (fun one two holds => ⟨(two (one holds).1).1,
      UInt64.le_trans (one holds).2 (two (one holds).1).2⟩)
    (fun computed holds => ⟨(stateTransition_invariant holds computed).1,
      stateTransition_currentJustified_mono holds computed⟩)
    anchorSlot (Store.getAncestor_of_isAncestor_of_lt before known descends) tipStored baseStored
  exact (rel ((reachable.ordered sound).2 baseStored)).2

/-- Every descendant source is at least as recent as the root's realized justification. -/
theorem Store.Reachable.realized_le_source {config : Config}
    {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (before : fork < .glamsterdam)
    {root tip : Root} {block : BeaconBlock preset fork} {base : BeaconState preset fork}
    {source : Checkpoint}
    (known : store.blocks[root]? = some block)
    (stored : store.blockStates[root]? = some base)
    (descends : store.isAncestor ⟨tip, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (read : store.getVotingSource config tip = .ok source) :
    base.currentJustifiedCheckpoint.epoch ≤ source.epoch := by
  unfold Store.getVotingSource at read
  simp only [bind_ok_iff] at read
  obtain ⟨tipBlock, tipRead, current, _, read⟩ := read
  obtain ⟨state, held, _⟩ := reachable.blockStatesFromParents
    (Store.block_ok_iff.mp tipRead)
  have mono := walk_realized_mono reachable sound anchorSlot before known stored held descends
  split at read
  · cases entry : store.unrealizedJustifications[tip]? with
    | none => simp [entry] at read
    | some checkpoint =>
      simp only [entry, pure, Except.pure, Except.ok.injEq] at read
      subst source
      exact UInt64.le_trans mono (walk_realized_le_unrealized reachable sound held entry)
  · simp only [held, pure, Except.pure, Except.ok.injEq] at read
    subst source
    exact mono

/-- Every block state of a reachable store keeps both state properties. -/
private theorem Store.Reachable.states_finalBelow {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) {root : Root} {state : BeaconState preset fork}
    (found : store.blockStates[root]? = some state) :
    FinalBelow (getCurrentEpoch anchorState).toNat state ∧
      BitLinked (getCurrentEpoch anchorState).toNat state :=
  reachable.blockState_induction reachable.blockStatesFromParents
    (fun _ st => FinalBelow (getCurrentEpoch anchorState).toNat st ∧
      BitLinked (getCurrentEpoch anchorState).toNat st)
    (fun _ _ => ⟨.inl (UInt64.le_iff_toNat_le.mp
        (UInt64.le_trans (Store.finalized_le_currentJustified sound.ordered)
          (UInt64.le_trans sound.settled (getPreviousEpoch_le _)))), .inl (by omega)⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ parentHeld transition ih =>
      stateTransition_keeps ((reachable.ordered sound).2 parentHeld) ih.1 ih.2 transition)
    found

/-- A store whose realized and unrealized pairs are both in order. -/
private def StoreBelow (a : ℕ) (store : Store preset fork) : Prop :=
  PairBelow a store.justifiedCheckpoint store.finalizedCheckpoint ∧
    PairBelow a store.unrealizedJustifiedCheckpoint store.unrealizedFinalizedCheckpoint

private theorem StoreBelow.same {a : ℕ} {s t : Store preset fork}
    (same : Store.SameCheckpoints s t) (h : StoreBelow a s) : StoreBelow a t := by
  unfold StoreBelow
  rw [same.justified, same.finalized, same.unrealizedJustified, same.unrealizedFinalized]
  exact h

/-- Moving the realized pair to an ordered pair keeps the store in order. -/
private theorem StoreBelow.update {a : ℕ} {s : Store preset fork} {j f : Checkpoint}
    (h : StoreBelow a s) (pair : PairBelow a j f) : StoreBelow a (s.updateCheckpoints j f) := by
  obtain ⟨realized, unrealized⟩ := h
  unfold PairBelow at realized pair
  unfold Store.updateCheckpoints
  by_cases jl : s.justifiedCheckpoint.epoch < j.epoch <;>
    by_cases fl : s.finalizedCheckpoint.epoch < f.epoch <;>
    simp only [jl, fl, ↓reduceIte] <;>
    refine ⟨?_, unrealized⟩ <;> unfold PairBelow <;> try dsimp only
  · omega
  · have := UInt64.lt_iff_toNat_lt.mp jl
    omega
  · have := UInt64.not_lt.mp jl
    have := UInt64.le_iff_toNat_le.mp this
    omega
  · omega

/-- Moving the unrealized pair to an ordered pair keeps the store in order. -/
private theorem StoreBelow.updateUnrealized {a : ℕ} {s : Store preset fork} {j f : Checkpoint}
    (h : StoreBelow a s) (pair : PairBelow a j f) :
    StoreBelow a (s.updateUnrealizedCheckpoints j f) := by
  obtain ⟨realized, unrealized⟩ := h
  unfold PairBelow at unrealized pair
  unfold Store.updateUnrealizedCheckpoints
  by_cases jl : s.unrealizedJustifiedCheckpoint.epoch < j.epoch <;>
    by_cases fl : s.unrealizedFinalizedCheckpoint.epoch < f.epoch <;>
    simp only [jl, fl, ↓reduceIte] <;>
    refine ⟨realized, ?_⟩ <;> unfold PairBelow <;> try dsimp only
  · omega
  · have := UInt64.lt_iff_toNat_lt.mp jl
    omega
  · have := UInt64.not_lt.mp jl
    have := UInt64.le_iff_toNat_le.mp this
    omega
  · omega

/-- A tick within a slot keeps the store in order. -/
private theorem StoreBelow.onTickPerSlot {a : ℕ} {s t : Store preset fork} {time : UInt64}
    (h : StoreBelow a s) (ticked : s.onTickPerSlot config time = .ok t) : StoreBelow a t := by
  obtain ⟨-, -, -, -, -, moved, which, same, -⟩ := Store.onTickPerSlot_frame ticked
  apply StoreBelow.same same
  rcases which with rfl | rfl
  · exact h
  · exact h.update h.2

/-- Every reachable store has both of its pairs in order. -/
private theorem Store.Reachable.storeBelow {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) : StoreBelow (getCurrentEpoch anchorState).toNat store := by
  induction reachable with
  | anchor made =>
    obtain ⟨_, _, _, _, _, finalized, _, unrealizedFinalized⟩ := getForkchoiceStore_anchor made
    unfold StoreBelow PairBelow
    rw [finalized, unrealizedFinalized]
    exact ⟨.inl (Nat.le_refl _), .inl (Nat.le_refl _)⟩
  | tick _ ticked ih =>
    obtain ⟨_, caught, -, caughtUp, ticked⟩ := Store.onTick_ok ticked
    exact (Store.catchUp_preserves (P := StoreBelow (getCurrentEpoch anchorState).toNat)
      (fun h tick => h.onTickPerSlot tick) ih caughtUp).onTickPerSlot ticked
  | @block prior after checks sources signed reached added ih =>
    have reachedAfter := Store.Reachable.block reached added
    cases root : SszType.hashTreeRoot signed.message with
    | error err => simp [Store.onBlock, root, Except.mapError, bind, Except.bind] at added
    | ok blockRoot =>
      by_cases known : prior.blocks.contains blockRoot
      · rw [Store.onBlock_known root known] at added
        cases added
        exact ih
      simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError,
        ↓reduceIte, Bool.false_eq_true] at added
      unfold Store.addBlock at added
      simp only [bind_ok_iff] at added
      obtain ⟨state, valid, head, _, voted, vote, recorded, record, boosted, boost, pulled⟩ :=
        added
      obtain ⟨pre, preFound, _, _, transition⟩ := Store.validateOnBlock_ok valid
      obtain ⟨preBelow, preLinked⟩ := reached.states_finalBelow sound preFound
      have stateBelow := (stateTransition_keeps ((reached.ordered sound).2 preFound) preBelow
        preLinked transition).1
      obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
      have boostedBelow : StoreBelow (getCurrentEpoch anchorState).toNat boosted :=
        StoreBelow.same (Store.updateProposerBoostRoot_frame boost).2.2.2.2.1
          (StoreBelow.same (Store.recordBlockTimeliness_frame record).2.2.2.2.1 ih)
      have updatedBelow := boostedBelow.update stateBelow
      obtain ⟨-, -, states, -, counted, countedState, countedFound, countedOk, moved, which,
        same, -⟩ := Store.computePulledUpTip_frame pulled
      have afterFound : after.blockStates[blockRoot]? = some counted := by
        rw [states]
        exact countedFound
      obtain ⟨countedBelow, countedLinked⟩ := reachedAfter.states_finalBelow sound afterFound
      have pulledBelow := (justification_step ((reachedAfter.ordered sound).2 afterFound)
        countedBelow countedLinked countedOk).1
      apply StoreBelow.same same
      rcases which with rfl | rfl
      · exact updatedBelow.updateUnrealized pulledBelow
      · exact (updatedBelow.updateUnrealized pulledBelow).update pulledBelow
  | attestation _ attested ih => exact ih.same (Store.onAttestation_frame attested).2.2.2.1
  | attesterSlashing _ slashed ih =>
    exact ih.same (Store.onAttesterSlashing_frame slashed).2.2.2.1
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih
  | envelope _ accepted ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    exact ih
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok _ accepted
    exact ih

/-- A reachable store finalizes at the anchor's epoch or earlier, or before its justified epoch.

The anchor state must keep the invariant of the state transition. -/
theorem Store.Reachable.finalized_lt_justified_or_anchor {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) :
    store.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState ∨
      store.finalizedCheckpoint.epoch < store.justifiedCheckpoint.epoch := by
  rcases (reachable.storeBelow sound).1 with atAnchor | below
  · exact .inl (UInt64.le_iff_toNat_le.mpr atAnchor)
  · exact .inr (UInt64.lt_iff_toNat_lt.mpr below)

/-- A voting source of a forward-reachable store is no later than its justified checkpoint. -/
theorem Store.ForwardReachable.votingSource_le_justified
    {store : Store preset fork}
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (sound : Invariant anchorState) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (slots : 0 < config.SLOT_DURATION_MS)
    (anchorLower : getCurrentEpoch anchorState ≤ store.justifiedCheckpoint.epoch)
    {tip : Root} {source : Checkpoint}
    (read : store.getVotingSource config tip = .ok source) :
    source.epoch ≤ store.justifiedCheckpoint.epoch := by
  have reached := forward.reachable
  unfold Store.getVotingSource at read
  simp only [bind_ok_iff] at read
  obtain ⟨block, blockOk, current, currentOk, read⟩ := read
  split at read
  · rename_i older
    cases entry : store.unrealizedJustifications[tip]? with
    | none => simp [entry] at read
    | some value =>
      simp only [entry, pure, Except.pure, Except.ok.injEq] at read
      subst source
      rcases (reached.unrealizedJustification_origin entry).imp And.left id with anchorEpoch |
        ⟨state, pulled, held, run, same⟩
      · rw [anchorEpoch]
        exact anchorLower
      · rw [same]
        have epochRead := currentOk
        unfold Store.getCurrentStoreEpoch at epochRead
        obtain ⟨slot, slotOk, epochEq⟩ := bind_ok_iff.mp epochRead
        simp only [pure, Except.pure, Except.ok.injEq] at epochEq
        subst epochEq
        exact forward.justified_le_of_pulledUp sound positive slots slotOk
          (Store.block_ok_iff.mp blockOk) held run older
  · cases held : store.blockStates[tip]? with
    | none => simp [held] at read
    | some state =>
      simp only [held, pure, Except.pure, Except.ok.injEq] at read
      subst source
      exact reached.justified_le_of_blockState sound held

/-- The justified epoch of a reachable store is at most its unrealized justified epoch.

The anchor state must keep the invariant of the state transition. -/
theorem Store.Reachable.justified_epoch_le_unrealized {store : Store preset fork}
    (anchor : Invariant anchorState)
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.justifiedCheckpoint.epoch ≤ store.unrealizedJustifiedCheckpoint.epoch := by
  induction reachable with
  | anchor made =>
    obtain ⟨_, -, -, -, justified, -, pending, -⟩ := getForkchoiceStore_anchor made
    rw [justified, pending]
    exact UInt64.le_refl _
  | tick _ ticked ih =>
    obtain ⟨same, justified⟩ := Store.onTick_unrealizedJustifiedCheckpoint ticked
    rw [same]
    rcases justified with eq | eq <;> rw [eq]
    · exact ih
    · exact UInt64.le_refl _
  | block previous added ih =>
    obtain ⟨raised, justified⟩ := Store.onBlock_unrealized_epoch_le added
    rcases justified with eq | ⟨root, state, pulled, held, run, pending, eq | eq⟩ <;> rw [eq]
    · exact UInt64.le_trans ih raised
    · exact UInt64.le_trans (processJustificationAndFinalization_currentJustified_mono
        (((previous.block added).ordered anchor).2 held).settled run) pending
    · exact pending
  | attestation _ attested ih =>
    obtain ⟨-, -, -, same, -⟩ := Store.onAttestation_frame attested
    rw [same.justified, same.unrealizedJustified]
    exact ih
  | attesterSlashing _ slashed ih =>
    obtain ⟨-, -, -, same, -⟩ := Store.onAttesterSlashing_frame slashed
    rw [same.justified, same.unrealizedJustified]
    exact ih
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih
  | envelope _ accepted ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    exact ih
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok _ accepted
    exact ih

end EthLib.Consensus
