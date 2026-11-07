module

public import EthLib.Consensus.Proofs.ForkChoice.Reachable

/-!
# Proofs: the order of the checkpoints of a store

The finalized epoch of a reachable store is at most its justified epoch.

The same holds for the unrealized checkpoints, which become those of the store at a new epoch.

The anchor state must keep the invariant of the state transition, as a genesis state does.

Each valid block then keeps that invariant in the state after it, whose checkpoints are in order.

A block writes the checkpoints of such a state, and those it reaches at the end of its epoch.

A new epoch writes the unrealized checkpoints, which are in order too.

From Gloas the store is not yet specified here, so no store is reachable there.

The result does not say that the finalized block is an ancestor of the justified block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork}

namespace Store

/-- The finalized epoch is at most the justified epoch, for both pairs of checkpoints. -/
def EpochsOrdered (store : Store preset fork) : Prop :=
  store.finalizedCheckpoint.epoch ≤ store.justifiedCheckpoint.epoch ∧
    store.unrealizedFinalizedCheckpoint.epoch ≤ store.unrealizedJustifiedCheckpoint.epoch

/-- Every state that the store keeps for a block keeps the invariant of the state transition. -/
def StatesHold (store : Store preset fork) : Prop :=
  ∀ {root : Root} {state : BeaconState preset fork},
    store.blockStates[root]? = some state → Invariant state

variable {config : Config} {store after : Store preset fork}

theorem StatesHold.of_eq (holds : store.StatesHold)
    (states : after.blockStates = store.blockStates) : after.StatesHold := by
  intro root state found
  rw [states] at found
  exact holds found

/-- The finalized epoch of an ordered state is at most its current justified epoch. -/
theorem finalized_le_currentJustified {state : BeaconState preset fork}
    (ordered : CheckpointsOrdered state) :
    state.finalizedCheckpoint.epoch ≤ state.currentJustifiedCheckpoint.epoch :=
  UInt64.le_trans ordered.1 ordered.2

private theorem le_of_not_lt' {a b : UInt64} (h : ¬ a < b) : b ≤ a := by
  rw [UInt64.lt_iff_toNat_lt] at h
  rw [UInt64.le_iff_toNat_le]
  omega

/-- Replacing the checkpoints by an ordered pair keeps them ordered. -/
theorem updateCheckpoints_ordered {justified finalized : Checkpoint}
    (ordered : store.EpochsOrdered) (le : finalized.epoch ≤ justified.epoch) :
    (store.updateCheckpoints justified finalized).EpochsOrdered := by
  unfold updateCheckpoints EpochsOrdered
  obtain ⟨o1, o2⟩ := ordered
  by_cases j : store.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.finalizedCheckpoint.epoch < finalized.epoch <;>
    simp only [j, f, ↓reduceIte] <;> refine ⟨?_, o2⟩
  · exact le
  · exact UInt64.le_trans o1 (UInt64.le_of_lt j)
  · exact UInt64.le_trans le (le_of_not_lt' j)
  · exact o1

/-- Replacing the unrealized checkpoints by an ordered pair keeps them ordered. -/
theorem updateUnrealizedCheckpoints_ordered {justified finalized : Checkpoint}
    (ordered : store.EpochsOrdered) (le : finalized.epoch ≤ justified.epoch) :
    (store.updateUnrealizedCheckpoints justified finalized).EpochsOrdered := by
  unfold updateUnrealizedCheckpoints EpochsOrdered
  obtain ⟨o1, o2⟩ := ordered
  by_cases j : store.unrealizedJustifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.unrealizedFinalizedCheckpoint.epoch < finalized.epoch <;>
    simp only [j, f, ↓reduceIte] <;> refine ⟨o1, ?_⟩
  · exact le
  · exact UInt64.le_trans o2 (UInt64.le_of_lt j)
  · exact UInt64.le_trans le (le_of_not_lt' j)
  · exact o2

/-- The tip pulled up to the end of its epoch keeps the checkpoints ordered. -/
theorem computePulledUpTip_ordered {root : Root}
    (ordered : store.EpochsOrdered) (holds : store.StatesHold)
    (pulled : store.computePulledUpTip config root = .ok after) : after.EpochsOrdered := by
  unfold computePulledUpTip at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨state, found, pulledState, weighed, block, -, epoch, -, pulled⟩ := pulled
  have invariant : Invariant state := holds (blockState_ok_iff.mp found)
  have le := finalized_le_currentJustified
    (processJustificationAndFinalization_ordered invariant.ordered invariant.settled
      (Base.mapError_ok_iff.mp weighed)).1
  have unrealized := updateUnrealizedCheckpoints_ordered (store := { store with
    unrealizedJustifications :=
      store.unrealizedJustifications.insert root pulledState.currentJustifiedCheckpoint })
    ordered le
  split at pulled <;> simp only [pure, Except.pure, Except.ok.injEq] at pulled <;> subst pulled
  · exact updateCheckpoints_ordered unrealized le
  · exact unrealized

/-- A tick within a slot keeps the checkpoints ordered. -/
theorem onTickPerSlot_ordered {timeMs : UInt64} (ordered : store.EpochsOrdered)
    (ticked : store.onTickPerSlot config timeMs = .ok after) : after.EpochsOrdered := by
  unfold onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    · obtain ⟨_, _, ticked⟩ := ticked
      split at ticked <;> simp only [pure, Except.pure, Except.ok.injEq] at ticked <;>
        subst ticked
      · exact updateCheckpoints_ordered ordered ordered.2
      · exact ordered

/-- The catch-up loop keeps the checkpoints ordered. -/
theorem catchUp_ordered {tickSlot : Slot} {start : Store preset fork}
    (ordered : start.EpochsOrdered) (caught : catchUp config start tickSlot = .ok after) :
    after.EpochsOrdered := by
  induction start using catchUp.induct config tickSlot with
  | _ start ih =>
    rw [catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, -, caught⟩ := caught
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, -, nextTimeMs, -, ticked, tick, caught⟩ := caught
      split at caught
      · exact ih ticked ‹_› (onTickPerSlot_ordered ordered tick) caught
      · cases caught
    · simp only [pure, Except.pure, Except.ok.injEq] at caught
      subst caught
      exact ordered

/-- A tick keeps the checkpoints ordered. -/
theorem onTick_ordered {timeMs : UInt64} (ordered : store.EpochsOrdered)
    (ticked : store.onTick config timeMs = .ok after) : after.EpochsOrdered := by
  unfold onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨tickSlot, -, caught, caughtUp, ticked⟩ := ticked
  exact onTickPerSlot_ordered (catchUp_ordered ordered caughtUp) ticked

/-- An attestation keeps the checkpoints. -/
theorem onAttestation_ordered {checks : SignatureChecks} {attestation : Attestation preset fork}
    {isFromBlock : Bool} (ordered : store.EpochsOrdered)
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    after.EpochsOrdered := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, storing, _, _, _, _, valid, _, attested⟩ := attested
  have kept : stored.EpochsOrdered := by
    unfold storeTargetCheckpointState at storing
    split at storing
    · simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst storing
      exact ordered
    · simp only [bind_ok_iff] at storing
      obtain ⟨_, _, storing⟩ := storing
      simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst storing
      exact ordered
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    exact kept
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

/-- An attester slashing keeps the checkpoints. -/
theorem onAttesterSlashing_ordered {checks : SignatureChecks}
    {slashing : AttesterSlashing preset fork} (ordered : store.EpochsOrdered)
    (slashed : store.onAttesterSlashing config checks slashing = .ok after) :
    after.EpochsOrdered := by
  unfold onAttesterSlashing at slashed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
  obtain ⟨_, _, slashed⟩ := slashed
  subst slashed
  exact ordered

/-- A block keeps the state of each block within the invariant. -/
theorem onBlock_statesHold {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    (holds : store.StatesHold) (added : store.onBlock config checks sources signed = .ok after) :
    after.StatesHold := by
  obtain same | ⟨blockRoot, -, -, -, pre, state, found, transition, states⟩ :=
    onBlock_same_or_insert added
  · subst same
    exact holds
  intro root kept keptFound
  rw [states, Std.TreeMap.getElem?_insert] at keptFound
  split at keptFound
  · cases keptFound
    exact (stateTransition_invariant (holds found) transition).1
  · exact holds keptFound

/-- A block keeps the checkpoints ordered, when each state of the store keeps the invariant. -/
theorem onBlock_ordered {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    (ordered : store.EpochsOrdered) (holds : store.StatesHold)
    (added : store.onBlock config checks sources signed = .ok after) : after.EpochsOrdered := by
  cases root : SszType.hashTreeRoot signed.message with
  | error e =>
    simp [onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [onBlock_known root known] at added
      cases added
      exact ordered
    simp only [onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, valid, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := recordBlockPtcVotes_onlyPtcVotes vote
    obtain ⟨pre, found, -, -, transition⟩ := validateOnBlock_ok valid
    have invariant := (stateTransition_invariant (holds found) transition).1
    have recordedOrdered : recorded.EpochsOrdered := by
      unfold recordBlockTimeliness at record
      simp only [bind_ok_iff, pure, Except.pure] at record
      obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
      split at record
      · simp only [bind_ok_iff, Except.ok.injEq] at record
        obtain ⟨_, _, rfl⟩ := record
        exact ordered
      · cases record
        exact ordered
    have boostedOrdered : boosted.EpochsOrdered := by
      unfold updateProposerBoostRoot at boost
      split at boost
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
      simp only [bind_ok_iff, pure_bind] at boost
      obtain ⟨_, _, _, _, _, _, boost⟩ := boost
      split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
        subst boost <;> exact recordedOrdered
    have statesHold : (boosted.updateCheckpoints state.currentJustifiedCheckpoint
        state.finalizedCheckpoint).StatesHold := by
      refine StatesHold.of_eq (store := { store with
        blocks := store.blocks.insert blockRoot signed.message
        blockStates := store.blockStates.insert blockRoot state }) ?_ ?_
      · intro root kept keptFound
        simp only [Std.TreeMap.getElem?_insert] at keptFound
        split at keptFound
        · cases keptFound
          exact invariant
        · exact holds keptFound
      · rw [updateCheckpoints_blockStates, (updateProposerBoostRoot_frame boost).2.2,
          (recordBlockTimeliness_frame record).2.2]
    exact computePulledUpTip_ordered
      (updateCheckpoints_ordered boostedOrdered (finalized_le_currentJustified invariant.ordered))
      statesHold added

end Store

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}

/-- A reachable store keeps its checkpoints ordered and its states in the invariant.

The anchor state must keep the invariant. -/
theorem Store.Reachable.ordered (anchor : Invariant anchorState)
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.EpochsOrdered ∧ store.StatesHold := by
  induction reachable with
  | anchor made =>
    obtain ⟨anchorRoot, -, -, -, justified, finalized, unrealizedJustified,
      unrealizedFinalized⟩ := getForkchoiceStore_anchor made
    obtain ⟨root, -, -, states⟩ := getForkchoiceStore_maps made
    refine ⟨?_, ?_⟩
    · unfold Store.EpochsOrdered
      rw [justified, finalized, unrealizedJustified, unrealizedFinalized]
      exact ⟨UInt64.le_refl _, UInt64.le_refl _⟩
    · intro blockRoot state found
      rw [states, Std.TreeMap.getElem?_insert] at found
      split at found
      · cases found
        exact anchor
      · simp at found
  | tick _ ticked ih =>
    exact ⟨Store.onTick_ordered ih.1 ticked,
      Store.StatesHold.of_eq ih.2 (Store.onTick_frame ticked).2.2.2⟩
  | block _ added ih =>
    exact ⟨Store.onBlock_ordered ih.1 ih.2 added, Store.onBlock_statesHold ih.2 added⟩
  | attestation _ attested ih =>
    exact ⟨Store.onAttestation_ordered ih.1 attested,
      Store.StatesHold.of_eq ih.2 (Store.onAttestation_frame attested).2.2⟩
  | attesterSlashing _ slashed ih =>
    exact ⟨Store.onAttesterSlashing_ordered ih.1 slashed,
      Store.StatesHold.of_eq ih.2 (Store.onAttesterSlashing_frame slashed).2.2⟩

/-- The finalized epoch of a reachable store is at most its justified epoch.

The anchor state must keep the invariant of the state transition. -/
theorem Store.Reachable.finalized_le_justified (anchor : Invariant anchorState)
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.finalizedCheckpoint.epoch ≤ store.justifiedCheckpoint.epoch :=
  (reachable.ordered anchor).1.1

end EthLib.Consensus
