module

public import EthLib.Consensus.ForkChoice.FastConfirmation
public import EthLib.Consensus.Proofs.ForkChoice.Reachable

/-!
# Proofs: the checkpoints of a store and its states

The finalized epoch of a reachable store is at most its justified epoch.

The same holds for the unrealized checkpoints, which become those of the store at a new epoch.

The anchor state must keep the invariant of the state transition, as a genesis state does.

Each valid block then keeps that invariant in the state after it, whose checkpoints are in order.

A block writes the checkpoints of such a state, and those it reaches at the end of its epoch.

A new epoch writes the unrealized checkpoints, which are in order too.

From Gloas, a vote of the payload committee and an envelope keep the checkpoints.

From Heze, an inclusion list keeps them too.

The state of each checkpoint of the store keeps the invariant too.

So does the state of a block pulled up to the current epoch.

Both have whole effective balances when the largest effective balances of the preset are whole.

The state of each checkpoint is the state of its block.

It is processed to the start of the epoch of the checkpoint when it is before that start.

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

/-- Each state that the store keeps for a checkpoint keeps the invariant. -/
def CheckpointStatesHold (store : Store preset fork) : Prop :=
  ∀ {checkpoint : Checkpoint} {state : BeaconState preset fork},
    store.checkpointStates[checkpoint]? = some state → Invariant state

/-- Each state that the store keeps for a checkpoint comes from the state of its block.

It is that state when that state is at the start of the epoch or later.

Otherwise it is that state with its slots processed to the start of the epoch.

The slots may run with any signature checks, as each call of the handler takes its own. -/
def CheckpointStatesFromBlocks (config : Config) (store : Store preset fork) : Prop :=
  ∀ ⦃checkpoint : Checkpoint⦄ ⦃state : BeaconState preset fork⦄,
    store.checkpointStates[checkpoint]? = some state →
      ∃ base start, store.blockStates[checkpoint.root]? = some base ∧
        computeStartSlotAtEpoch preset checkpoint.epoch = .ok start ∧
        ((start ≤ base.slot ∧ state = base) ∨
          (base.slot < start ∧ ∃ checks, processSlots config checks base start = .ok state))

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

/-- A store with the checkpoints of an ordered store is ordered. -/
private theorem EpochsOrdered.of_checkpoints (ordered : store.EpochsOrdered)
    (justified : after.justifiedCheckpoint = store.justifiedCheckpoint)
    (finalized : after.finalizedCheckpoint = store.finalizedCheckpoint)
    (unrealizedJustified : after.unrealizedJustifiedCheckpoint =
      store.unrealizedJustifiedCheckpoint)
    (unrealizedFinalized : after.unrealizedFinalizedCheckpoint =
      store.unrealizedFinalizedCheckpoint) :
    after.EpochsOrdered := by
  unfold EpochsOrdered
  rw [justified, finalized, unrealizedJustified, unrealizedFinalized]
  exact ordered

/-- The tip pulled up to the end of its epoch keeps the checkpoints ordered. -/
theorem computePulledUpTip_ordered {root : Root}
    (ordered : store.EpochsOrdered) (holds : store.StatesHold)
    (pulled : store.computePulledUpTip config root = .ok after) : after.EpochsOrdered := by
  obtain ⟨-, -, -, -, state, counted, found, countedOk, moved, which, justified, finalized,
    unrealizedJustified, unrealizedFinalized⟩ := computePulledUpTip_frame pulled
  have invariant : Invariant state := holds found
  have le := finalized_le_currentJustified
    (processJustificationAndFinalization_ordered invariant.ordered invariant.settled countedOk).1
  have unrealized := updateUnrealizedCheckpoints_ordered ordered le
  refine EpochsOrdered.of_checkpoints ?_ justified finalized unrealizedJustified
    unrealizedFinalized
  rcases which with rfl | rfl
  · exact unrealized
  · exact updateCheckpoints_ordered unrealized le

/-- A tick within a slot keeps the checkpoints ordered. -/
theorem onTickPerSlot_ordered {timeMs : UInt64} (ordered : store.EpochsOrdered)
    (ticked : store.onTickPerSlot config timeMs = .ok after) : after.EpochsOrdered := by
  obtain ⟨-, -, -, -, -, moved, which, justified, finalized, unrealizedJustified,
    unrealizedFinalized⟩ := onTickPerSlot_frame ticked
  refine EpochsOrdered.of_checkpoints ?_ justified finalized unrealizedJustified
    unrealizedFinalized
  rcases which with rfl | rfl
  · exact ordered
  · exact updateCheckpoints_ordered ordered ordered.2

/-- The catch-up loop keeps the checkpoints ordered. -/
theorem catchUp_ordered {tickSlot : Slot} {start : Store preset fork}
    (ordered : start.EpochsOrdered) (caught : catchUp config start tickSlot = .ok after) :
    after.EpochsOrdered :=
  catchUp_preserves (fun ordered tick => onTickPerSlot_ordered ordered tick) ordered caught

/-- A tick keeps the checkpoints ordered. -/
theorem onTick_ordered {timeMs : UInt64} (ordered : store.EpochsOrdered)
    (ticked : store.onTick config timeMs = .ok after) : after.EpochsOrdered := by
  obtain ⟨_, caught, -, caughtUp, ticked⟩ := onTick_ok ticked
  exact onTickPerSlot_ordered (catchUp_ordered ordered caughtUp) ticked

/-- An attestation keeps the checkpoints. -/
theorem onAttestation_ordered {checks : SignatureChecks} {attestation : Attestation preset fork}
    {isFromBlock : Bool} (ordered : store.EpochsOrdered)
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    after.EpochsOrdered := by
  obtain ⟨-, -, -, justified, finalized, unrealizedJustified, unrealizedFinalized⟩ :=
    onAttestation_frame attested
  exact ordered.of_checkpoints justified finalized unrealizedJustified unrealizedFinalized

/-- An attester slashing keeps the checkpoints. -/
theorem onAttesterSlashing_ordered {checks : SignatureChecks}
    {slashing : AttesterSlashing preset fork} (ordered : store.EpochsOrdered)
    (slashed : store.onAttesterSlashing config checks slashing = .ok after) :
    after.EpochsOrdered := by
  obtain ⟨-, -, -, justified, finalized, unrealizedJustified, unrealizedFinalized⟩ :=
    onAttesterSlashing_frame slashed
  exact ordered.of_checkpoints justified finalized unrealizedJustified unrealizedFinalized

/-- From Gloas, a vote of the payload committee keeps the checkpoints. -/
theorem onPayloadAttestationMessage_ordered {checks : SignatureChecks}
    {gloas : .glamsterdam ≤ fork} {message : PayloadAttestationMessage} {isFromBlock : Bool}
    (ordered : store.EpochsOrdered)
    (voted : store.onPayloadAttestationMessage config checks gloas message isFromBlock =
      .ok after) :
    after.EpochsOrdered := by
  obtain ⟨_, _, rfl⟩ := onPayloadAttestationMessage_onlyPtcVotes voted
  exact ordered

/-- From Gloas, an accepted envelope keeps the checkpoints. -/
theorem onExecutionPayloadEnvelope_ordered {checks : SignatureChecks}
    {sources : BlockSources preset fork} {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadEnvelope preset fork} (ordered : store.EpochsOrdered)
    (accepted : store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after) :
    after.EpochsOrdered := by
  obtain ⟨_, _, _, _, _, record, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
  obtain ⟨_, rfl⟩ := recordEnvelope_frame record
  exact ordered

/-- From Heze, an accepted inclusion list keeps the checkpoints. -/
theorem onInclusionList_ordered {checks : SignatureChecks} {heze : .hegota ≤ fork}
    {signed : SignedInclusionList} (ordered : store.EpochsOrdered)
    (accepted : store.onInclusionList config checks heze signed = .ok after) :
    after.EpochsOrdered := by
  obtain ⟨_, _, rfl⟩ := onInclusionList_ok heze accepted
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
      obtain ⟨-, -, -, -, justified, finalized, unrealizedJustified, unrealizedFinalized⟩ :=
        recordBlockTimeliness_frame record
      exact ordered.of_checkpoints justified finalized unrealizedJustified unrealizedFinalized
    have boostedOrdered : boosted.EpochsOrdered := by
      obtain ⟨-, -, -, -, justified, finalized, unrealizedJustified, unrealizedFinalized⟩ :=
        updateProposerBoostRoot_frame boost
      exact recordedOrdered.of_checkpoints justified finalized unrealizedJustified
        unrealizedFinalized
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
      · rw [updateCheckpoints_blockStates, (updateProposerBoostRoot_frame boost).2.2.1,
          (recordBlockTimeliness_frame record).2.2.1]
    exact computePulledUpTip_ordered
      (updateCheckpoints_ordered boostedOrdered (finalized_le_currentJustified invariant.ordered))
      statesHold added

/-- Replacing the checkpoints keeps the states of the checkpoints and the latest votes. -/
private theorem updateCheckpoints_checkpointStates_latestMessages
    (justified finalized : Checkpoint) :
    (store.updateCheckpoints justified finalized).checkpointStates = store.checkpointStates ∧
      (store.updateCheckpoints justified finalized).latestMessages = store.latestMessages := by
  unfold updateCheckpoints
  by_cases j : store.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.finalizedCheckpoint.epoch < finalized.epoch <;> simp [j, f]

/-- The tip pulled up to the end of its epoch keeps the checkpoint states and the latest votes. -/
private theorem computePulledUpTip_checkpointStates_latestMessages {root : Root}
    (pulled : store.computePulledUpTip config root = .ok after) :
    after.checkpointStates = store.checkpointStates ∧
      after.latestMessages = store.latestMessages := by
  unfold computePulledUpTip at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨state, -, pulledState, -, block, -, epoch, -, pulled⟩ := pulled
  split at pulled <;> simp only [pure, Except.pure, Except.ok.injEq] at pulled <;> subst pulled
  · simp [updateCheckpoints_checkpointStates_latestMessages, updateUnrealizedCheckpoints]
    split <;> split <;> simp
  · simp [updateUnrealizedCheckpoints]
    split <;> split <;> simp

/-- A tick within a slot keeps the states of the checkpoints and the latest votes. -/
private theorem onTickPerSlot_checkpointStates_latestMessages {timeMs : UInt64}
    (ticked : store.onTickPerSlot config timeMs = .ok after) :
    after.checkpointStates = store.checkpointStates ∧
      after.latestMessages = store.latestMessages := by
  unfold onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    · obtain ⟨_, _, ticked⟩ := ticked
      split at ticked <;> simp only [pure, Except.pure, Except.ok.injEq] at ticked <;>
        subst ticked
      · exact updateCheckpoints_checkpointStates_latestMessages _ _
      · exact ⟨rfl, rfl⟩

/-- The catch-up loop keeps the states of the checkpoints and the latest votes. -/
private theorem catchUp_checkpointStates_latestMessages {tickSlot : Slot}
    {start : Store preset fork} (caught : catchUp config start tickSlot = .ok after) :
    after.checkpointStates = start.checkpointStates ∧
      after.latestMessages = start.latestMessages :=
  catchUp_preserves (P := fun s => s.checkpointStates = start.checkpointStates ∧
      s.latestMessages = start.latestMessages)
    (fun same tick => by
      have step := onTickPerSlot_checkpointStates_latestMessages tick
      exact ⟨step.1.trans same.1, step.2.trans same.2⟩)
    ⟨rfl, rfl⟩ caught

/-- A tick keeps the states of the checkpoints and the latest votes. -/
theorem onTick_checkpointStates_latestMessages {timeMs : UInt64}
    (ticked : store.onTick config timeMs = .ok after) :
    after.checkpointStates = store.checkpointStates ∧
      after.latestMessages = store.latestMessages := by
  obtain ⟨_, caught, -, caughtUp, ticked⟩ := onTick_ok ticked
  have step := onTickPerSlot_checkpointStates_latestMessages ticked
  have rest := catchUp_checkpointStates_latestMessages caughtUp
  exact ⟨step.1.trans rest.1, step.2.trans rest.2⟩

/-- An attester slashing keeps the states of the checkpoints and the latest votes. -/
theorem onAttesterSlashing_checkpointStates_latestMessages {checks : SignatureChecks}
    {slashing : AttesterSlashing preset fork}
    (slashed : store.onAttesterSlashing config checks slashing = .ok after) :
    after.checkpointStates = store.checkpointStates ∧
      after.latestMessages = store.latestMessages := by
  unfold onAttesterSlashing at slashed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
  obtain ⟨_, _, slashed⟩ := slashed
  subst slashed
  exact ⟨rfl, rfl⟩

/-- A block keeps the states of the checkpoints and the latest votes. -/
theorem onBlock_checkpointStates_latestMessages {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    (added : store.onBlock config checks sources signed = .ok after) :
    after.checkpointStates = store.checkpointStates ∧
      after.latestMessages = store.latestMessages := by
  cases root : SszType.hashTreeRoot signed.message with
  | error e =>
    simp [onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [onBlock_known root known] at added
      cases added
      exact ⟨rfl, rfl⟩
    simp only [onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, valid, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := recordBlockPtcVotes_onlyPtcVotes vote
    have recordedKept : recorded.checkpointStates = store.checkpointStates ∧
        recorded.latestMessages = store.latestMessages := by
      unfold recordBlockTimeliness at record
      simp only [bind_ok_iff, pure, Except.pure] at record
      obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
      split at record
      · simp only [bind_ok_iff, Except.ok.injEq] at record
        obtain ⟨_, _, rfl⟩ := record
        exact ⟨rfl, rfl⟩
      · cases record
        exact ⟨rfl, rfl⟩
    have boostedKept : boosted.checkpointStates = recorded.checkpointStates ∧
        boosted.latestMessages = recorded.latestMessages := by
      unfold updateProposerBoostRoot at boost
      split at boost
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
      simp only [bind_ok_iff, pure_bind] at boost
      obtain ⟨_, _, _, _, _, _, boost⟩ := boost
      split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
        subst boost <;> exact ⟨rfl, rfl⟩
    have pulled := computePulledUpTip_checkpointStates_latestMessages added
    have updated := updateCheckpoints_checkpointStates_latestMessages
      (store := boosted) state.currentJustifiedCheckpoint state.finalizedCheckpoint
    exact ⟨by rw [pulled.1, updated.1, boostedKept.1, recordedKept.1],
      by rw [pulled.2, updated.2, boostedKept.2, recordedKept.2]⟩

/-- The state of a checkpoint, computed from a state within the invariant, keeps the invariant. -/
private theorem computeCheckpointState_invariant {checks : SignatureChecks} {target : Checkpoint}
    {state : BeaconState preset fork} (holds : store.StatesHold)
    (computed : store.computeCheckpointState config checks target = .ok state) :
    Invariant state := by
  unfold computeCheckpointState at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨base, found, start, -, computed⟩ := computed
  have invariant : Invariant base := holds (blockState_ok_iff.mp found)
  split at computed
  · exact (processSlots_invariant invariant (Base.mapError_ok_iff.mp computed)).1
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact invariant

/-- An attestation keeps the state of each checkpoint within the invariant. -/
private theorem onAttestation_checkpointStatesHold {checks : SignatureChecks}
    {attestation : Attestation preset fork} {isFromBlock : Bool}
    (holds : store.StatesHold) (kept : store.CheckpointStatesHold)
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    after.CheckpointStatesHold := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, storing, _, _, _, _, _, _, valid, _, attested⟩ := attested
  have storedHolds : stored.CheckpointStatesHold := by
    unfold storeTargetCheckpointState at storing
    split at storing
    · simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst storing
      exact kept
    · simp only [bind_ok_iff] at storing
      obtain ⟨state, computed, storing⟩ := storing
      simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst storing
      intro checkpoint found keptFound
      simp only [Std.TreeMap.getElem?_insert] at keptFound
      split at keptFound
      · cases keptFound
        exact computeCheckpointState_invariant holds computed
      · exact kept keptFound
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    intro checkpoint state found
    exact storedHolds found
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

/-- Two checkpoints equal in the order of checkpoints are the same checkpoint. -/
private theorem checkpoint_eq_of_compare_eq {a b : Checkpoint}
    (same : Checkpoint.compare a b = .eq) : a = b := by
  unfold Checkpoint.compare at same
  rw [Ordering.then_eq_eq, Std.LawfulEqCmp.compare_eq_iff_eq,
    Std.LawfulEqCmp.compare_eq_iff_eq] at same
  cases a
  cases b
  cases same.1
  cases same.2
  rfl

/-- The state of a checkpoint, computed by the store, comes from the state of its block. -/
private theorem computeCheckpointState_fromBlock {checks : SignatureChecks} {target : Checkpoint}
    {state : BeaconState preset fork}
    (computed : store.computeCheckpointState config checks target = .ok state) :
    ∃ base start, store.blockStates[target.root]? = some base ∧
      computeStartSlotAtEpoch preset target.epoch = .ok start ∧
      ((start ≤ base.slot ∧ state = base) ∨
        (base.slot < start ∧ ∃ checks, processSlots config checks base start = .ok state)) := by
  unfold computeCheckpointState at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨base, found, start, startOk, computed⟩ := computed
  refine ⟨base, start, blockState_ok_iff.mp found, Base.mapError_ok_iff.mp startOk, ?_⟩
  split at computed
  · exact .inr ⟨‹_›, checks, Base.mapError_ok_iff.mp computed⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact .inl ⟨UInt64.not_lt.mp ‹_›, computed.symm⟩

/-- A store with the same states of blocks and of checkpoints keeps their link. -/
private theorem CheckpointStatesFromBlocks.of_maps (holds : store.CheckpointStatesFromBlocks config)
    (states : after.blockStates = store.blockStates)
    (kept : after.checkpointStates = store.checkpointStates) :
    after.CheckpointStatesFromBlocks config := by
  intro checkpoint state found
  rw [kept] at found
  rw [states]
  exact holds found

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
      Store.StatesHold.of_eq ih.2 (Store.onAttestation_frame attested).2.2.1⟩
  | attesterSlashing _ slashed ih =>
    exact ⟨Store.onAttesterSlashing_ordered ih.1 slashed,
      Store.StatesHold.of_eq ih.2 (Store.onAttesterSlashing_frame slashed).2.2.1⟩
  | payloadAttestation _ voted ih =>
    exact ⟨Store.onPayloadAttestationMessage_ordered ih.1 voted,
      Store.StatesHold.of_eq ih.2 (onPayloadAttestationMessage_onlyPtcVotes voted).frame.2.2⟩
  | envelope _ accepted ih =>
    exact ⟨Store.onExecutionPayloadEnvelope_ordered ih.1 accepted,
      Store.StatesHold.of_eq ih.2 (Store.onExecutionPayloadEnvelope_frame accepted).2.2⟩
  | inclusionList _ accepted ih =>
    exact ⟨Store.onInclusionList_ordered ih.1 accepted,
      Store.StatesHold.of_eq ih.2 (Store.onInclusionList_frame accepted).2.2⟩

/-- A reachable store keeps the state of each checkpoint in the invariant.

The anchor state must keep the invariant. -/
theorem Store.Reachable.checkpointStatesHold (anchor : Invariant anchorState)
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.CheckpointStatesHold := by
  induction reachable with
  | anchor made =>
    obtain ⟨anchorRoot, -, states⟩ := getForkchoiceStore_checkpointStates made
    intro checkpoint state found
    rw [states, Std.TreeMap.getElem?_insert] at found
    split at found
    · cases found
      exact anchor
    · simp at found
  | tick _ ticked ih =>
    intro checkpoint state found
    exact ih (by rwa [(Store.onTick_checkpointStates_latestMessages ticked).1] at found)
  | block _ added ih =>
    intro checkpoint state found
    exact ih (by rwa [(Store.onBlock_checkpointStates_latestMessages added).1] at found)
  | attestation previous attested ih =>
    exact Store.onAttestation_checkpointStatesHold (previous.ordered anchor).2 ih attested
  | attesterSlashing _ slashed ih =>
    intro checkpoint state found
    rw [(Store.onAttesterSlashing_checkpointStates_latestMessages slashed).1] at found
    exact ih found
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih
  | envelope _ accepted ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := recordEnvelope_frame record
    exact ih
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := onInclusionList_ok ‹_› accepted
    exact ih

/-- The finalized epoch of a reachable store is at most its justified epoch.

The anchor state must keep the invariant of the state transition. -/
theorem Store.Reachable.finalized_le_justified (anchor : Invariant anchorState)
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.finalizedCheckpoint.epoch ≤ store.justifiedCheckpoint.epoch :=
  (reachable.ordered anchor).1.1

/-- The state of a block of a reachable store, pulled up to the current epoch, keeps the invariant.

The anchor state must keep the invariant of the state transition. -/
theorem Store.Reachable.getPulledUpHeadState_invariant (anchor : Invariant anchorState)
    (reachable : Store.Reachable config anchorState anchorBlock store) {head : Root}
    {state : BeaconState preset fork}
    (pulled : store.getPulledUpHeadState config head = .ok state) : Invariant state := by
  have states : store.StatesHold := (reachable.ordered anchor).2
  unfold Store.getPulledUpHeadState at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨headState, found, _, _, pulled⟩ := pulled
  have holds : Invariant headState := states (Store.blockState_ok_iff.mp found)
  split at pulled
  · simp only [bind_ok_iff] at pulled
    obtain ⟨_, _, processed⟩ := pulled
    exact (processSlots_invariant holds (Base.mapError_ok_iff.mp processed)).1
  · simp only [pure, Except.pure, Except.ok.injEq] at pulled
    subst pulled
    exact holds

/-- The state of a block of a reachable store, pulled up to the current epoch, has whole balances.

Each of its effective balances is a whole number of increments.

This is the source of balances of the votes for the target of the current epoch.

The anchor state must keep the invariant of the state transition.

The largest effective balances of the preset must be whole numbers of increments. -/
theorem Store.Reachable.getPulledUpHeadState_aligned (anchor : Invariant anchorState)
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (maxAligned : MaxEffectiveBalancesAligned preset) {head : Root}
    {state : BeaconState preset fork}
    (pulled : store.getPulledUpHeadState config head = .ok state) :
    EffectiveBalancesAligned state :=
  (reachable.getPulledUpHeadState_invariant anchor pulled).aligned maxAligned

/-- The state of a checkpoint of a reachable store has whole effective balances.

This is the source of balances of the confirmation of a block.

The anchor state must keep the invariant of the state transition.

The largest effective balances of the preset must be whole numbers of increments. -/
theorem Store.Reachable.checkpointState_aligned (anchor : Invariant anchorState)
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (maxAligned : MaxEffectiveBalancesAligned preset) {checkpoint : Checkpoint}
    {state : BeaconState preset fork} (found : store.checkpointState checkpoint = .ok state) :
    EffectiveBalancesAligned state :=
  ((reachable.checkpointStatesHold anchor) (Store.checkpointState_ok_iff.mp found)).aligned
    maxAligned

/-- Each state that a reachable store keeps for a checkpoint comes from the state of its block.

It is that state when that state is at the start of the epoch or later.

Otherwise it is that state with its slots processed to the start of the epoch. -/
theorem Store.Reachable.checkpointStatesFromBlocks
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.CheckpointStatesFromBlocks config := by
  induction reachable with
  | anchor made =>
    obtain ⟨anchorRoot, rootOk, states⟩ := getForkchoiceStore_checkpointStates made
    obtain ⟨_, rootOk', blocks, blockStates⟩ := getForkchoiceStore_maps made
    rw [rootOk, Except.ok.injEq] at rootOk'
    subst rootOk'
    intro checkpoint state found
    rw [states, Std.TreeMap.getElem?_insert] at found
    split at found
    · rename_i same
      cases found
      obtain rfl := Store.checkpoint_eq_of_compare_eq same
      have startOk := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset)
        anchorState.slot
      refine ⟨anchorState, _, by simp [blockStates], startOk, .inl ⟨?_, rfl⟩⟩
      obtain ⟨-, value⟩ := computeStartSlotAtEpoch_ok_iff.mp startOk
      rw [UInt64.le_iff_toNat_le, value, computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_mul_le_self _ _
    · simp at found
  | tick _ ticked ih =>
    exact ih.of_maps (Store.onTick_frame ticked).2.2.2
      (Store.onTick_checkpointStates_latestMessages ticked).1
  | block previous added ih =>
    rcases Store.onBlock_same_or_insert added with
      same | ⟨blockRoot, -, fresh, blocks, -, state, -, -, states⟩
    · subst same
      exact ih
    have kept := (Store.onBlock_checkpointStates_latestMessages added).1
    intro checkpoint checkpointState found
    rw [kept] at found
    obtain ⟨base, start, baseFound, rest⟩ := ih found
    refine ⟨base, start, ?_, rest⟩
    have other : blockRoot ≠ checkpoint.root := by
      rintro rfl
      rw [previous.blockState_eq_none fresh] at baseFound
      cases baseFound
    rw [states, getElem?_insert_root]
    simp only [other, ↓reduceIte]
    exact baseFound
  | attestation _ attested ih =>
    obtain ⟨-, -, states, -⟩ := Store.onAttestation_frame attested
    unfold Store.onAttestation at attested
    simp only [bind_ok_iff] at attested
    obtain ⟨_, _, stored, storing, _, _, _, _, _, _, _, _, attested⟩ := attested
    have storedFrom : stored.CheckpointStatesFromBlocks config := by
      unfold Store.storeTargetCheckpointState at storing
      split at storing
      · simp only [pure, Except.pure, Except.ok.injEq] at storing
        subst storing
        exact ih
      · simp only [bind_ok_iff] at storing
        obtain ⟨computedState, computed, storing⟩ := storing
        simp only [pure, Except.pure, Except.ok.injEq] at storing
        subst storing
        intro checkpoint state keptFound
        simp only [Std.TreeMap.getElem?_insert] at keptFound
        split at keptFound
        · rename_i same
          cases keptFound
          obtain rfl := Store.checkpoint_eq_of_compare_eq same
          exact Store.computeCheckpointState_fromBlock computed
        · exact ih keptFound
    split at attested
    · simp only [pure, Except.pure, Except.ok.injEq] at attested
      subst attested
      intro checkpoint state found
      exact storedFrom found
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested
  | attesterSlashing _ slashed ih =>
    exact ih.of_maps (Store.onAttesterSlashing_frame slashed).2.2.1
      (Store.onAttesterSlashing_checkpointStates_latestMessages slashed).1
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih
  | envelope _ accepted ih =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := recordEnvelope_frame record
    exact ih
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := onInclusionList_ok ‹_› accepted
    exact ih

end EthLib.Consensus
