module

public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
public import EthLib.Consensus.Proofs.Transition.RootLinks

/-!
# Proofs: the origin and the ancestry of the checkpoints of a store

A reachable store takes each justified or finalized checkpoint from one of three places.

It is the anchor checkpoint, the checkpoint of a state that the store holds, or that of its pull-up.

A pull-up runs justification and finalization on a held state, and the store does not keep it.

The root and the epoch of the checkpoint come together from that one place.

A checkpoint of a held state, or of its pull-up, names a block on the chain of that state's block.

That block is the ancestor of the source block at the first slot of the checkpoint's epoch.

This holds for each checkpoint after the epoch of the anchor state.

An earlier checkpoint can name a block that the store never held.

The other exception is a held state on the source chain that hashes to the zero root.

Such a state leaves the latest block header unfilled, and its next slot records the stale root.

So in one held state or its pull-up, the finalized checkpoint is on the chain of the justified one.

[Gasper] §4.1 pairs a block with an epoch, and §8.5 gives the four finalization cases.

[Gasper]: https://arxiv.org/abs/2003.03052v3
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-! ## The origin of the checkpoints of a store -/

/-- Moving the checkpoints keeps a property of each pair, when the new checkpoints have it. -/
private theorem Store.checkpointFields_of_updateCheckpoints {store : Store preset fork}
    {P Q : Checkpoint → Prop} {justified finalized : Checkpoint}
    (fields : P store.justifiedCheckpoint ∧ P store.unrealizedJustifiedCheckpoint ∧
      Q store.finalizedCheckpoint ∧ Q store.unrealizedFinalizedCheckpoint)
    (newJustified : P justified) (newFinalized : Q finalized) :
    P (store.updateCheckpoints justified finalized).justifiedCheckpoint ∧
      P (store.updateCheckpoints justified finalized).unrealizedJustifiedCheckpoint ∧
      Q (store.updateCheckpoints justified finalized).finalizedCheckpoint ∧
      Q (store.updateCheckpoints justified finalized).unrealizedFinalizedCheckpoint := by
  obtain ⟨realized, unrealized, realizedFinal, unrealizedFinal⟩ := fields
  unfold Store.updateCheckpoints
  split <;> dsimp only <;> split <;>
    exact ⟨by assumption, unrealized, by assumption, unrealizedFinal⟩

/-- Moving the unrealized checkpoints keeps a property of each pair in the same way. -/
private theorem Store.checkpointFields_of_updateUnrealizedCheckpoints {store : Store preset fork}
    {P Q : Checkpoint → Prop} {justified finalized : Checkpoint}
    (fields : P store.justifiedCheckpoint ∧ P store.unrealizedJustifiedCheckpoint ∧
      Q store.finalizedCheckpoint ∧ Q store.unrealizedFinalizedCheckpoint)
    (newJustified : P justified) (newFinalized : Q finalized) :
    P (store.updateUnrealizedCheckpoints justified finalized).justifiedCheckpoint ∧
      P (store.updateUnrealizedCheckpoints justified finalized).unrealizedJustifiedCheckpoint ∧
      Q (store.updateUnrealizedCheckpoints justified finalized).finalizedCheckpoint ∧
      Q (store.updateUnrealizedCheckpoints justified finalized).unrealizedFinalizedCheckpoint := by
  obtain ⟨realized, unrealized, realizedFinal, unrealizedFinal⟩ := fields
  unfold Store.updateUnrealizedCheckpoints
  split <;> dsimp only <;> split <;> exact ⟨realized, by assumption, realizedFinal, by assumption⟩

/-- Pulling up a tip adds only the checkpoints of its successful justification and finalization.

`P` is a property of the justified checkpoints, and `Q` one of the finalized checkpoints. -/
private theorem Store.checkpointFields_of_computePulledUpTip {config : Config}
    {store after : Store preset fork} {root : Root} {P Q : Checkpoint → Prop}
    (fields : P store.justifiedCheckpoint ∧ P store.unrealizedJustifiedCheckpoint ∧
      Q store.finalizedCheckpoint ∧ Q store.unrealizedFinalizedCheckpoint)
    (counted : ∀ (state pulled : BeaconState preset fork),
      store.blockStates[root]? = some state →
      processJustificationAndFinalization state = .ok pulled →
      P pulled.currentJustifiedCheckpoint ∧ Q pulled.finalizedCheckpoint)
    (computed : store.computePulledUpTip config root = .ok after) :
    P after.justifiedCheckpoint ∧ P after.unrealizedJustifiedCheckpoint ∧
      Q after.finalizedCheckpoint ∧ Q after.unrealizedFinalizedCheckpoint := by
  obtain ⟨-, -, -, -, state, pulled, found, processed, moved, which, movedJustified,
    movedFinalized, movedUnrealized, movedUnrealizedFinal⟩ :=
    Store.computePulledUpTip_frame computed
  obtain ⟨justified, finalized⟩ := counted state pulled found processed
  have unrealized :=
    Store.checkpointFields_of_updateUnrealizedCheckpoints fields justified finalized
  rw [movedJustified, movedFinalized, movedUnrealized, movedUnrealizedFinal]
  rcases which with rfl | rfl
  · exact unrealized
  · exact Store.checkpointFields_of_updateCheckpoints unrealized justified finalized

/-- A tick within a slot realizes only the unrealized checkpoints. -/
private theorem Store.checkpointFields_of_onTickPerSlot {config : Config}
    {store after : Store preset fork} {time : UInt64} {P Q : Checkpoint → Prop}
    (fields : P store.justifiedCheckpoint ∧ P store.unrealizedJustifiedCheckpoint ∧
      Q store.finalizedCheckpoint ∧ Q store.unrealizedFinalizedCheckpoint)
    (ticked : store.onTickPerSlot config time = .ok after) :
    P after.justifiedCheckpoint ∧ P after.unrealizedJustifiedCheckpoint ∧
      Q after.finalizedCheckpoint ∧ Q after.unrealizedFinalizedCheckpoint := by
  obtain ⟨-, -, -, -, -, moved, which, movedJustified, movedFinalized, movedUnrealized,
    movedUnrealizedFinal⟩ := Store.onTickPerSlot_frame ticked
  rw [movedJustified, movedFinalized, movedUnrealized, movedUnrealizedFinal]
  rcases which with rfl | rfl
  · exact fields
  · exact Store.checkpointFields_of_updateCheckpoints fields fields.2.1 fields.2.2.2

/-- A full tick keeps a property of each pair of checkpoints, through catch-up and its last tick.
-/
private theorem Store.checkpointFields_of_onTick {config : Config}
    {store after : Store preset fork} {time : UInt64} {P Q : Checkpoint → Prop}
    (fields : P store.justifiedCheckpoint ∧ P store.unrealizedJustifiedCheckpoint ∧
      Q store.finalizedCheckpoint ∧ Q store.unrealizedFinalizedCheckpoint)
    (ticked : store.onTick config time = .ok after) :
    P after.justifiedCheckpoint ∧ P after.unrealizedJustifiedCheckpoint ∧
      Q after.finalizedCheckpoint ∧ Q after.unrealizedFinalizedCheckpoint := by
  unfold Store.onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨slot, -, caught, catchUp, ticked⟩ := ticked
  exact Store.checkpointFields_of_onTickPerSlot (Store.catchUp_preserves
    (P := fun s => P s.justifiedCheckpoint ∧ P s.unrealizedJustifiedCheckpoint ∧
      Q s.finalizedCheckpoint ∧ Q s.unrealizedFinalizedCheckpoint)
    Store.checkpointFields_of_onTickPerSlot fields catchUp) ticked

/-- An accepted block takes new checkpoints only from held states and their pull-ups. -/
private theorem Store.checkpointFields_of_onBlock {config : Config} {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    {store after : Store preset fork} {P Q : Checkpoint → Prop}
    (fields : P store.justifiedCheckpoint ∧ P store.unrealizedJustifiedCheckpoint ∧
      Q store.finalizedCheckpoint ∧ Q store.unrealizedFinalizedCheckpoint)
    (states : ∀ (root : Root) (state : BeaconState preset fork),
      after.blockStates[root]? = some state →
      P state.currentJustifiedCheckpoint ∧ Q state.finalizedCheckpoint)
    (counts : ∀ (root : Root) (state pulled : BeaconState preset fork),
      after.blockStates[root]? = some state →
      processJustificationAndFinalization state = .ok pulled →
      P pulled.currentJustifiedCheckpoint ∧ Q pulled.finalizedCheckpoint)
    (added : store.onBlock config checks sources signed = .ok after) :
    P after.justifiedCheckpoint ∧ P after.unrealizedJustifiedCheckpoint ∧
      Q after.finalizedCheckpoint ∧ Q after.unrealizedFinalizedCheckpoint := by
  cases root : SszType.hashTreeRoot signed.message with
  | error err => simp [Store.onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [Store.onBlock_known root known] at added
      cases added
      exact fields
    simp only [Store.onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold Store.addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, -, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := Store.recordBlockPtcVotes_onlyPtcVotes vote
    -- Recording timeliness and the boost keep the checkpoints and the held states.
    obtain ⟨-, -, recordedStates, -, recordedJustified, recordedFinalized,
      recordedUnrealized, recordedUnrealizedFinal⟩ := Store.recordBlockTimeliness_frame record
    obtain ⟨-, -, boostedStates, -, boostedJustified, boostedFinalized,
      boostedUnrealized, boostedUnrealizedFinal⟩ := Store.updateProposerBoostRoot_frame boost
    have kept := (Store.computePulledUpTip_frame added).2.2.1
    have newFound : after.blockStates[blockRoot]? = some state := by
      rw [kept, Store.updateCheckpoints_blockStates, boostedStates, recordedStates]
      simp
    obtain ⟨justified, finalized⟩ := states blockRoot state newFound
    have boostedFields : P boosted.justifiedCheckpoint ∧
        P boosted.unrealizedJustifiedCheckpoint ∧ Q boosted.finalizedCheckpoint ∧
        Q boosted.unrealizedFinalizedCheckpoint := by
      rw [boostedJustified, boostedFinalized, boostedUnrealized, boostedUnrealizedFinal,
        recordedJustified, recordedFinalized, recordedUnrealized, recordedUnrealizedFinal]
      exact fields
    exact Store.checkpointFields_of_computePulledUpTip
      (Store.checkpointFields_of_updateCheckpoints boostedFields justified finalized)
      (fun s p found processed => counts blockRoot s p (kept.symm ▸ found) processed) added

/-- Each checkpoint field of a reachable store comes from the anchor, a held state or its pull-up.

The field of the state is the current justified checkpoint for the two justified fields.

It is the finalized checkpoint for the two finalized fields. -/
private theorem Store.Reachable.checkpoint_origins {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (field : BeaconState preset fork → Checkpoint) (checkpoint : Checkpoint)
    (selected : (field = (·.currentJustifiedCheckpoint) ∧
        (checkpoint = store.justifiedCheckpoint ∨
          checkpoint = store.unrealizedJustifiedCheckpoint)) ∨
      (field = (·.finalizedCheckpoint) ∧
        (checkpoint = store.finalizedCheckpoint ∨
          checkpoint = store.unrealizedFinalizedCheckpoint))) :
    (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
      checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
      (∃ (root : Root) (state : BeaconState preset fork),
        store.blockStates[root]? = some state ∧ checkpoint = field state) ∨
      ∃ (root : Root) (state pulled : BeaconState preset fork),
        store.blockStates[root]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧ checkpoint = field pulled := by
  let Origin := fun (s : Store preset fork) (field : BeaconState preset fork → Checkpoint)
      (checkpoint : Checkpoint) =>
    (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
      checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
    (∃ (root : Root) (state : BeaconState preset fork), s.blockStates[root]? = some state ∧
      checkpoint = field state) ∨
    ∃ (root : Root) (state pulled : BeaconState preset fork), s.blockStates[root]? = some state ∧
      processJustificationAndFinalization state = .ok pulled ∧ checkpoint = field pulled
  have mono {s t : Store preset fork}
      (kept : ∀ (root : Root) (state : BeaconState preset fork),
        s.blockStates[root]? = some state → t.blockStates[root]? = some state)
      {field : BeaconState preset fork → Checkpoint} {checkpoint : Checkpoint}
      (origin : Origin s field checkpoint) : Origin t field checkpoint := by
    rcases origin with anchor | ⟨root, state, found, same⟩ | ⟨root, state, pulled, found, run, same⟩
    · exact .inl anchor
    · exact .inr (.inl ⟨root, state, kept root state found, same⟩)
    · exact .inr (.inr ⟨root, state, pulled, kept root state found, run, same⟩)
  -- A handler that keeps the held states and the checkpoints keeps each origin.
  have frame {s t : Store preset fork} (states : t.blockStates = s.blockStates)
      (justified : t.justifiedCheckpoint = s.justifiedCheckpoint)
      (finalized : t.finalizedCheckpoint = s.finalizedCheckpoint)
      (unrealized : t.unrealizedJustifiedCheckpoint = s.unrealizedJustifiedCheckpoint)
      (unrealizedFinal : t.unrealizedFinalizedCheckpoint = s.unrealizedFinalizedCheckpoint)
      (origins : Origin s (·.currentJustifiedCheckpoint) s.justifiedCheckpoint ∧
        Origin s (·.currentJustifiedCheckpoint) s.unrealizedJustifiedCheckpoint ∧
        Origin s (·.finalizedCheckpoint) s.finalizedCheckpoint ∧
        Origin s (·.finalizedCheckpoint) s.unrealizedFinalizedCheckpoint) :
      Origin t (·.currentJustifiedCheckpoint) t.justifiedCheckpoint ∧
        Origin t (·.currentJustifiedCheckpoint) t.unrealizedJustifiedCheckpoint ∧
        Origin t (·.finalizedCheckpoint) t.finalizedCheckpoint ∧
        Origin t (·.finalizedCheckpoint) t.unrealizedFinalizedCheckpoint := by
    have kept : ∀ (root : Root) (state : BeaconState preset fork),
        s.blockStates[root]? = some state → t.blockStates[root]? = some state := by
      intro root state found
      rw [states]
      exact found
    rw [justified, finalized, unrealized, unrealizedFinal]
    exact ⟨mono kept origins.1, mono kept origins.2.1, mono kept origins.2.2.1,
      mono kept origins.2.2.2⟩
  have all : Origin store (·.currentJustifiedCheckpoint) store.justifiedCheckpoint ∧
      Origin store (·.currentJustifiedCheckpoint) store.unrealizedJustifiedCheckpoint ∧
      Origin store (·.finalizedCheckpoint) store.finalizedCheckpoint ∧
      Origin store (·.finalizedCheckpoint) store.unrealizedFinalizedCheckpoint := by
    clear selected
    induction reachable with
    | anchor made =>
      obtain ⟨root, hashed, -, -, justified, finalized, unrealized, unrealizedFinal⟩ :=
        getForkchoiceStore_anchor made
      exact ⟨.inl ⟨root, hashed, justified⟩, .inl ⟨root, hashed, unrealized⟩,
        .inl ⟨root, hashed, finalized⟩, .inl ⟨root, hashed, unrealizedFinal⟩⟩
    | @tick before after time reachable ticked ih =>
      have kept := (Store.onTick_frame ticked).2.2.2
      exact Store.checkpointFields_of_onTick
        ⟨mono (fun _ _ h => kept.symm ▸ h) ih.1, mono (fun _ _ h => kept.symm ▸ h) ih.2.1,
          mono (fun _ _ h => kept.symm ▸ h) ih.2.2.1, mono (fun _ _ h => kept.symm ▸ h) ih.2.2.2⟩
        ticked
    | @block before after checks sources signed reachable added ih =>
      have kept : ∀ (root : Root) (state : BeaconState preset fork),
          before.blockStates[root]? = some state → after.blockStates[root]? = some state := by
        intro root state found
        rcases Store.onBlock_same_or_insert added with same |
          ⟨newRoot, -, fresh, -, -, post, -, -, states⟩
        · exact same ▸ found
        have other : newRoot ≠ root := by
          rintro rfl
          rw [reachable.blockState_eq_none fresh] at found
          cases found
        rw [states, getElem?_insert_root]
        simpa only [other, ↓reduceIte] using found
      exact Store.checkpointFields_of_onBlock
        ⟨mono kept ih.1, mono kept ih.2.1, mono kept ih.2.2.1, mono kept ih.2.2.2⟩
        (fun root state found => ⟨.inr (.inl ⟨root, state, found, rfl⟩),
          .inr (.inl ⟨root, state, found, rfl⟩)⟩)
        (fun root state pulled found run => ⟨.inr (.inr ⟨root, state, pulled, found, run, rfl⟩),
          .inr (.inr ⟨root, state, pulled, found, run, rfl⟩)⟩)
        added
    | attestation _ attested ih =>
      obtain ⟨-, -, states, justified, finalized, unrealized, unrealizedFinal⟩ :=
        Store.onAttestation_frame attested
      exact frame states justified finalized unrealized unrealizedFinal ih
    | attesterSlashing _ slashed ih =>
      obtain ⟨-, -, states, justified, finalized, unrealized, unrealizedFinal⟩ :=
        Store.onAttesterSlashing_frame slashed
      exact frame states justified finalized unrealized unrealizedFinal ih
    | payloadAttestation _ voted ih =>
      obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes voted
      exact ih
    | envelope _ accepted ih =>
      obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok accepted
      obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
      exact ih
    | inclusionList _ accepted ih =>
      obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok ‹_› accepted
      exact ih
  rcases selected with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩
  exacts [all.1, all.2.1, all.2.2.1, all.2.2.2]

/-- Each justified store field has an anchor, held-state, or successful pulled-up origin.

The checkpoint pair is retained in full, with no timing bound. -/
theorem Store.Reachable.justified_origins {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    ∀ checkpoint, (checkpoint = store.justifiedCheckpoint ∨
      checkpoint = store.unrealizedJustifiedCheckpoint) →
      (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
        checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
      (∃ (root : Root) (state : BeaconState preset fork), store.blockStates[root]? = some state ∧
        checkpoint = state.currentJustifiedCheckpoint) ∨
      ∃ (root : Root) (state pulled : BeaconState preset fork),
        store.blockStates[root]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        checkpoint = pulled.currentJustifiedCheckpoint :=
  fun checkpoint selected => reachable.checkpoint_origins _ checkpoint (.inl ⟨rfl, selected⟩)

/-- Each finalized store field has an anchor, held-state, or successful pulled-up origin.

The checkpoint pair is retained in full, with no timing bound. -/
theorem Store.Reachable.finalized_origins {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    ∀ checkpoint, (checkpoint = store.finalizedCheckpoint ∨
      checkpoint = store.unrealizedFinalizedCheckpoint) →
      (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
        checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
      (∃ (root : Root) (state : BeaconState preset fork), store.blockStates[root]? = some state ∧
        checkpoint = state.finalizedCheckpoint) ∨
      ∃ (root : Root) (state pulled : BeaconState preset fork),
        store.blockStates[root]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧
        checkpoint = pulled.finalizedCheckpoint :=
  fun checkpoint selected => reachable.checkpoint_origins _ checkpoint (.inr ⟨rfl, selected⟩)

/-! ## The ancestry of the checkpoints of a held state -/

namespace Store

variable {store : Store preset fork}

/-- Below the slot of a block, the walk from it reaches the roots that its parent's walk reaches. -/
private theorem getAncestor_root_of_parent {root : Root} {slot : Slot}
    {block parent : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot) (below : slot < block.slot) :
    (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot =
      (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ slot := by
  rw [getAncestor_step found (UInt64.not_le.mpr below) parentFound lower]
  exact getAncestor_root _ _ _

/-- A checkpoint block is the root that the walk from a pending node reaches at the epoch start. -/
private theorem getCheckpointBlock_ok_iff {root target : Root} {epoch : Epoch} :
    store.getCheckpointBlock root epoch = .ok target ↔ ∃ start,
      computeStartSlotAtEpoch preset epoch = .ok start ∧
        (·.root) <$> store.getAncestor ⟨root, .pending⟩ start = .ok target := by
  unfold getCheckpointBlock
  cases computeStartSlotAtEpoch preset epoch with
  | error e => simp [Except.mapError, bind, Except.bind]
  | ok start =>
    cases store.getAncestor ⟨root, .pending⟩ start <;>
      simp [Except.mapError, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

/-- A pending node descends from the pending node of each root that its walk reaches.

Before Gloas the walk keeps the pending status, as each parent is pending then. -/
private theorem isAncestor_of_getAncestor_root (lower : store.ParentsBelow) {root target : Root}
    {slot : Slot}
    (walk : (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok target) :
    store.isAncestor ⟨root, .pending⟩ ⟨target, .pending⟩ = .ok true := by
  cases reached : store.getAncestor ⟨root, .pending⟩ slot with
  | error e => simp [reached, Functor.map, Except.map] at walk
  | ok node =>
    simp only [reached, Functor.map, Except.map, Except.ok.injEq] at walk
    subst walk
    by_cases gloas : .glamsterdam ≤ fork
    · obtain ⟨block, found, le⟩ := getAncestor_le reached
      have stops : store.getAncestor ⟨root, .pending⟩ block.slot = .ok node := by
        rw [getAncestor_trans le reached, getAncestor_of_le found (UInt64.le_refl _)]
      simp [isAncestor_pending gloas, block_ok_iff.mpr found, stops, bind, Except.bind, pure,
        Except.pure]
    · obtain ⟨-, origin, -⟩ := getAncestor_climbs (lower := lower) reached
      obtain ⟨nodeRoot, status⟩ := node
      have pending : status = .pending := by
        rcases origin with same | ⟨_, _, _, _, _, _, parentStatus, _⟩
        · cases same
          rfl
        · exact parentStatus.trans (parentPayloadStatus_of_lt (Nat.lt_of_not_le gloas))
      subst pending
      exact isAncestor_of_getAncestor reached

/-- A zero preimage on the chain of a parent is on the chain of its child. -/
private theorem zeroPreimage_of_parent {root : Root} {block parent : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot)
    (zero : ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
      store.blockStates[badRoot]? = some badState ∧
      SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
      (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ slot = .ok badRoot) :
    ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
      store.blockStates[badRoot]? = some badState ∧
      SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
      (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok badRoot := by
  obtain ⟨badRoot, badState, slot, badHeld, hashed, walk⟩ := zero
  by_cases below : slot < block.slot
  · exact ⟨badRoot, badState, slot, badHeld, hashed,
      (getAncestor_root_of_parent found parentFound lower below).trans walk⟩
  · -- A walk from the parent to a slot at or above the block stays at the parent.
    rw [getAncestor_of_le parentFound
      (UInt64.le_trans (UInt64.le_of_lt lower) (UInt64.not_lt.mp below))] at walk
    simp only [Functor.map, Except.map, Except.ok.injEq] at walk
    subst walk
    refine ⟨_, badState, parent.slot, badHeld, hashed, ?_⟩
    rw [getAncestor_root_of_parent found parentFound lower lower,
      getAncestor_of_le parentFound (UInt64.le_refl _)]
    rfl

/-- A root read in a transition from a held parent state is on the chain of the new block.

The read follows the cases of the recorded roots of the transition.

An older root is read in the parent state, whose own reads are on the chain of the parent.

Otherwise the root is that of the parent, or the parent state hashes to zero. -/
private theorem Linked.getAncestor_root_of_cases {orphanParent : Root}
    (linked : store.Linked orphanParent)
    {root readRoot : Root} {block : BeaconBlock preset fork} {parent : BeaconState preset fork}
    {slot : Slot} (found : store.blocks[root]? = some block)
    (parentHeld : store.blockStates[block.parentRoot]? = some parent)
    (history : getBlockRootAtSlot parent slot = .ok readRoot →
      (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ slot = .ok readRoot ∨
      ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
        store.blockStates[badRoot]? = some badState ∧
        SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
        (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ slot = .ok badRoot)
    (below : slot < block.slot)
    (cases : (slot < parent.slot ∧ getBlockRootAtSlot parent slot = .ok readRoot) ∨
      (parent.slot ≤ slot ∧ (readRoot = block.parentRoot ∨
        (SszType.hashTreeRoot parent = .ok (Vector.replicate 32 0) ∧
          SszType.hashTreeRoot parent.latestBlockHeader = .ok readRoot)))) :
    (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok readRoot ∨
      ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
        store.blockStates[badRoot]? = some badState ∧
        SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
        (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok badRoot := by
  obtain ⟨parentBlock, parentFound, parentLe⟩ := linked.stateAfter _ _ parentHeld
  have lower := linked.parentsBelow _ _ _ found parentFound
  rcases cases with ⟨-, read⟩ | ⟨atLeast, parentRoot | ⟨zero, -⟩⟩
  · rcases history read with walk | bad
    · exact .inl ((getAncestor_root_of_parent found parentFound lower below).trans walk)
    · exact .inr (zeroPreimage_of_parent found parentFound lower bad)
  · left
    rw [getAncestor_root_of_parent found parentFound lower below,
      getAncestor_of_le parentFound (UInt64.le_trans parentLe atLeast), parentRoot]
    rfl
  · right
    refine ⟨block.parentRoot, parent, parentBlock.slot, parentHeld, zero, ?_⟩
    rw [getAncestor_root_of_parent found parentFound lower lower,
      getAncestor_of_le parentFound (UInt64.le_refl _)]
    rfl

end Store

/-- A root that a held state reads after the anchor state is on the chain of its block.

Otherwise a held state on that chain hashes to zero. -/
private theorem Store.Reachable.getAncestor_root_of_blockState {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (linked : store.Linked anchorBlock.parentRoot)
    {root readRoot : Root} {state : BeaconState preset fork} {slot : Slot}
    (held : store.blockStates[root]? = some state)
    (read : getBlockRootAtSlot state slot = .ok readRoot) (later : anchorState.slot ≤ slot) :
    (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok readRoot ∨
      ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
        store.blockStates[badRoot]? = some badState ∧
        SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
        (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok badRoot := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState held
  obtain ⟨post, postOk, anchored, produced⟩ := reachable.blockStatesFromParents found
  rw [held, Option.some.injEq] at postOk
  subst post
  by_cases same : block = anchorBlock
  · -- The anchor state reads no slot from its own on.
    rw [anchored same] at read
    exact absurd later (UInt64.not_le.mpr (getBlockRootAtSlot_read read).1)
  obtain ⟨parent, checks, engine, signed, message, parentHeld, transitioned⟩ := produced same
  have below : slot < block.slot := by
    rw [← message, ← (stateTransition_slot transitioned).2]
    exact (getBlockRootAtSlot_read read).1
  refine linked.getAncestor_root_of_cases found parentHeld
    (fun parentRead => reachable.getAncestor_root_of_blockState linked parentHeld parentRead later)
    below ?_
  by_cases old : slot < parent.slot
  · exact .inl ⟨old, getBlockRootAtSlot_stateTransition_of_lt transitioned old read⟩
  · refine .inr ⟨UInt64.not_lt.mp old, ?_⟩
    rw [← message]
    exact getBlockRootAtSlot_stateTransition_cases transitioned (UInt64.not_lt.mp old) read
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- The three checkpoints of a state satisfy a predicate. -/
private def CheckpointsSatisfy (p : Checkpoint → Prop) (state : BeaconState preset fork) : Prop :=
  p state.previousJustifiedCheckpoint ∧ p state.currentJustifiedCheckpoint ∧
    p state.finalizedCheckpoint

/-- A frame keeps the three checkpoints. -/
private theorem CheckpointsSatisfy.of_frame {p : Checkpoint → Prop}
    {state after : BeaconState preset fork} (holds : CheckpointsSatisfy p state)
    (frame : Frame state after) : CheckpointsSatisfy p after := by
  simpa only [CheckpointsSatisfy, frame.previousJustified, frame.currentJustified,
    frame.finalized] using holds

/-- Justification keeps old checkpoints or selects one read from the history of the state.

A new finalized checkpoint is an old justified one, as in the four cases of [Gasper] §8.5.

[Gasper]: https://arxiv.org/abs/2003.03052v3 -/
private theorem CheckpointsSatisfy.of_processJustificationAndFinalization
    {p : Checkpoint → Prop} {state after : BeaconState preset fork}
    (holds : CheckpointsSatisfy p state)
    (reads : ∀ checkpoint,
      (checkpoint.epoch = getPreviousEpoch state ∨ checkpoint.epoch = getCurrentEpoch state) →
      getBlockRoot state checkpoint.epoch = .ok checkpoint.root → p checkpoint)
    (computed : processJustificationAndFinalization state = .ok after) :
    CheckpointsSatisfy p after := by
  have current : p after.currentJustifiedCheckpoint := by
    rcases processJustificationAndFinalization_currentJustified computed with same | ⟨recent, read⟩
    · exact same ▸ holds.2.1
    · exact reads _ recent read
  rcases processJustificationAndFinalization_ok computed with rfl | ⟨_, _, _, weighed⟩
  · exact holds
  · obtain ⟨previous, -, final, -⟩ := weighJustificationAndFinalization_checkpoints weighed
    refine ⟨previous ▸ holds.2.1, current, ?_⟩
    rcases final with same | same | same
    · exact same ▸ holds.2.2
    · exact same ▸ holds.1
    · exact same ▸ holds.2.1

/-- A slot run selects checkpoints only by reads at its intermediate states.

Each read comes with the slots before and after its state. -/
private theorem CheckpointsSatisfy.of_advanceSlots {config : Config} {p : Checkpoint → Prop}
    {state after : BeaconState preset fork} {checks : SignatureChecks} {count : ℕ}
    (holds : CheckpointsSatisfy p state)
    (reads : ∀ i, i < count → ∀ middle cached,
      advanceSlots config checks i state = .ok middle →
      advanceSlots config checks (count - i) middle = .ok after →
      processSlot middle = .ok cached → ∀ checkpoint,
      (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) →
      getBlockRoot cached checkpoint.epoch = .ok checkpoint.root → p checkpoint)
    (computed : advanceSlots config checks count state = .ok after) :
    CheckpointsSatisfy p after := by
  induction count generalizing state after with
  | zero =>
    cases Except.ok.inj computed
    exact holds
  | succ count ih =>
    have whole := computed
    simp only [EthLib.Consensus.advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, step, rest⟩ := computed
    have nextHolds : CheckpointsSatisfy p next := by
      obtain ⟨slot, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok step
      have cachedHolds := holds.of_frame (frame_processSlot cachedOk)
      have epochedHolds : CheckpointsSatisfy p epoched := by
        unfold epochIfLast at epochedOk
        split at epochedOk
        · obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
          exact (cachedHolds.of_processJustificationAndFinalization
            (reads 0 (Nat.zero_lt_succ _) state cached rfl (by simpa using whole) cachedOk)
              justifiedOk).of_frame frame.toFrame
        · cases Except.ok.inj epochedOk
          exact cachedHolds
      exact epochedHolds
    apply ih nextHolds (fun i hi middle cached run more cachedOk => ?_) rest
    refine reads (i + 1) (by omega) middle cached ?_ (by rwa [Nat.add_sub_add_right]) cachedOk
    simp only [EthLib.Consensus.advanceSlots, step, bind, Except.bind]
    exact run

/-- An epoch after the current epoch of a state starts after the slot of that state. -/
private theorem slot_le_of_getCurrentEpoch_lt {state : BeaconState preset fork} {epoch : Epoch}
    {start : Slot} (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (later : getCurrentEpoch state < epoch)
    (startOk : computeStartSlotAtEpoch preset epoch = .ok start) : state.slot ≤ start := by
  have epochLt := UInt64.lt_iff_toNat_lt.mp later
  rw [getCurrentEpoch_toNat] at epochLt
  have next := (Nat.div_lt_iff_lt_mul positive).mp epochLt
  have eq := (mulChecked_ok_iff.mp startOk).2
  exact UInt64.le_iff_toNat_le.mpr (by omega)

/-- After the anchor epoch, each checkpoint of a held state is on the chain of its block.

Otherwise a held state on that chain hashes to zero. -/
private theorem Store.Reachable.checkpointsSatisfy_of_blockState {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (linked : store.Linked anchorBlock.parentRoot)
    {root : Root} {state : BeaconState preset fork}
    (held : store.blockStates[root]? = some state) :
    CheckpointsSatisfy (fun checkpoint => checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
      store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root ∨
      ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
        store.blockStates[badRoot]? = some badState ∧
        SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
        (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok badRoot) state := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState held
  obtain ⟨post, postOk, anchored, produced⟩ := reachable.blockStatesFromParents found
  rw [held, Option.some.injEq] at postOk
  subst post
  by_cases same : block = anchorBlock
  · -- The anchor state has no checkpoint after its own epoch.
    rw [anchored same]
    have bound := UInt64.le_trans sound.settled (getPreviousEpoch_le anchorState)
    exact ⟨.inl (UInt64.le_trans sound.ordered.2 bound), .inl bound,
      .inl (UInt64.le_trans sound.ordered.1 (UInt64.le_trans sound.ordered.2 bound))⟩
  obtain ⟨parent, checks, engine, signed, message, parentHeld, transitioned⟩ := produced same
  obtain ⟨parentBlock, parentFound, -⟩ := linked.stateAfter _ _ parentHeld
  have lower := linked.parentsBelow _ _ _ found parentFound
  have bounds := stateTransition_slot transitioned
  rw [message] at bounds
  -- A checkpoint of the parent state starts no later than that state, so below the block.
  have lift : ∀ checkpoint : Checkpoint, checkpoint.epoch ≤ getCurrentEpoch parent →
      (checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
        store.getCheckpointBlock block.parentRoot checkpoint.epoch = .ok checkpoint.root ∨
        ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
          store.blockStates[badRoot]? = some badState ∧
          SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
          (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ slot = .ok badRoot) →
      checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
        store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root ∨
        ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
          store.blockStates[badRoot]? = some badState ∧
          SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
          (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok badRoot := by
    intro checkpoint early holds
    rcases holds with old | path | bad
    · exact .inl old
    · obtain ⟨start, startOk, walk⟩ := Store.getCheckpointBlock_ok_iff.mp path
      have below : start < block.slot := by
        have eq := (mulChecked_ok_iff.mp startOk).2
        have epochLe := UInt64.le_iff_toNat_le.mp early
        rw [getCurrentEpoch_toNat] at epochLe
        have scaled := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat epochLe
        have floor := Nat.div_mul_le_self parent.slot.toNat preset.SLOTS_PER_EPOCH.toNat
        have earlier := UInt64.lt_iff_toNat_lt.mp bounds.1
        exact UInt64.lt_iff_toNat_lt.mpr (by omega)
      exact .inr (.inl (Store.getCheckpointBlock_ok_iff.mpr ⟨start, startOk,
        (Store.getAncestor_root_of_parent found parentFound lower below).trans walk⟩))
    · exact .inr (.inr (Store.zeroPreimage_of_parent found parentFound lower bad))
  have parentHolds :=
    reachable.checkpointsSatisfy_of_blockState sound positive window linked parentHeld
  have invariant := (reachable.ordered sound).2 parentHeld
  have currentLe := UInt64.le_trans invariant.settled (getPreviousEpoch_le parent)
  obtain ⟨advanced, slotsOk, advancedSlot, -, blockOk, -⟩ := stateTransition_ok transitioned
  rw [message] at blockOk advancedSlot
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, run⟩ := slotsOk
  refine CheckpointsSatisfy.of_frame (CheckpointsSatisfy.of_advanceSlots
    ⟨lift _ (UInt64.le_trans invariant.ordered.2 currentLe) parentHolds.1,
      lift _ currentLe parentHolds.2.1,
      lift _ (UInt64.le_trans invariant.ordered.1 (UInt64.le_trans invariant.ordered.2 currentLe))
        parentHolds.2.2⟩ ?_ run) (frame_processBlock blockOk)
  intro i _ middle cached first rest cachedOk checkpoint recent read
  by_cases old : checkpoint.epoch ≤ getCurrentEpoch anchorState
  · exact .inl old
  -- A new checkpoint is read at an intermediate state of the transition.
  have recent' : checkpoint.epoch = getCurrentEpoch middle ∨
      checkpoint.epoch = getPreviousEpoch middle := by
    simpa only [getPreviousEpoch, getCurrentEpoch, processSlot_slot cachedOk] using recent.symm
  rw [getBlockRoot_processSlot cachedOk (slot_lt_epoch_add_historical positive window recent')]
    at read
  obtain ⟨start, startOk, read⟩ := getBlockRoot_ok_iff.mp read
  have later := slot_le_of_getCurrentEpoch_lt positive (UInt64.not_le.mp old) startOk
  have below : start < block.slot := by
    have before := UInt64.lt_iff_toNat_lt.mp (getBlockRootAtSlot_read read).1
    have moved := advanceSlots_slot _ rest
    rw [advancedSlot] at moved
    exact UInt64.lt_iff_toNat_lt.mpr (by omega)
  rcases linked.getAncestor_root_of_cases found parentHeld
      (fun parentRead =>
        reachable.getAncestor_root_of_blockState linked parentHeld parentRead later)
      below (getBlockRootAtSlot_advanceSlots_cases first rest blockOk read) with walk | bad
  · exact .inr (.inl (Store.getCheckpointBlock_ok_iff.mpr ⟨start, startOk, walk⟩))
  · exact .inr (.inr bad)
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- After the anchor epoch, a state checkpoint names its epoch boundary on the source chain.

The alternative exposes a held state on that chain whose hash is the zero sentinel. -/
theorem Store.Reachable.checkpoint_source_ancestor {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    {root : Root} {state view : BeaconState preset fork} {checkpoint : Checkpoint}
    (held : store.blockStates[root]? = some state)
    (selected : view = state ∨ processJustificationAndFinalization state = .ok view)
    (field : checkpoint = view.previousJustifiedCheckpoint ∨
      checkpoint = view.currentJustifiedCheckpoint ∨ checkpoint = view.finalizedCheckpoint)
    (afterAnchor : getCurrentEpoch anchorState < checkpoint.epoch) :
    (store.isAncestor ⟨root, .pending⟩ ⟨checkpoint.root, .pending⟩ = .ok true ∧
      store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root) ∨
    ∃ (badRoot : Root) (badState : BeaconState preset fork),
      store.blockStates[badRoot]? = some badState ∧
      SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
      store.isAncestor ⟨root, .pending⟩ ⟨badRoot, .pending⟩ = .ok true := by
  -- The anchor parent is unknown, so the store keeps its blocks and states linked.
  have linked := reachable.linked_of_unknown anchorSlot unknownParent
  suffices viewHolds : CheckpointsSatisfy (fun checkpoint =>
      checkpoint.epoch ≤ getCurrentEpoch anchorState ∨
        store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root ∨
        ∃ (badRoot : Root) (badState : BeaconState preset fork) (slot : Slot),
          store.blockStates[badRoot]? = some badState ∧
          SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
          (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok badRoot) view by
    have fieldHolds : ∀ p : Checkpoint → Prop, CheckpointsSatisfy p view → p checkpoint := by
      intro p holds
      rcases field with rfl | rfl | rfl
      exacts [holds.1, holds.2.1, holds.2.2]
    rcases fieldHolds _ viewHolds with old | path | ⟨badRoot, badState, slot, badHeld, zero, walk⟩
    · exact absurd afterAnchor (UInt64.not_lt.mpr old)
    · obtain ⟨start, -, walk⟩ := Store.getCheckpointBlock_ok_iff.mp path
      exact .inl ⟨Store.isAncestor_of_getAncestor_root linked.parentsBelow walk, path⟩
    · exact .inr ⟨badRoot, badState, badHeld, zero,
        Store.isAncestor_of_getAncestor_root linked.parentsBelow walk⟩
  have holds := reachable.checkpointsSatisfy_of_blockState sound positive window linked held
  rcases selected with rfl | pulled
  · exact holds
  -- A pull-up reads the new checkpoint in the held state itself.
  refine holds.of_processJustificationAndFinalization (fun checkpoint _ read => ?_) pulled
  by_cases old : checkpoint.epoch ≤ getCurrentEpoch anchorState
  · exact .inl old
  obtain ⟨start, startOk, read⟩ := getBlockRoot_ok_iff.mp read
  rcases reachable.getAncestor_root_of_blockState linked held read
      (slot_le_of_getCurrentEpoch_lt positive (UInt64.not_le.mp old) startOk) with walk | bad
  · exact .inr (.inl (Store.getCheckpointBlock_ok_iff.mpr ⟨start, startOk, walk⟩))
  · exact .inr (.inr bad)

/-- In one held state or its pull-up, the finalized checkpoint is on the chain of the justified one.

It is the ancestor of the current justified block at the first slot of the finalized epoch.

Checkpoints at or before the anchor epoch and a zero-hashing state are explicit alternatives. -/
theorem Store.Reachable.postState_finalized_ancestor {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (sound : Invariant anchorState)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    {root : Root} {state view : BeaconState preset fork}
    (held : store.blockStates[root]? = some state)
    (selected : view = state ∨ processJustificationAndFinalization state = .ok view) :
    view.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState ∨
    (store.isAncestor ⟨view.currentJustifiedCheckpoint.root, .pending⟩
        ⟨view.finalizedCheckpoint.root, .pending⟩ = .ok true ∧
      store.getCheckpointBlock view.currentJustifiedCheckpoint.root
        view.finalizedCheckpoint.epoch = .ok view.finalizedCheckpoint.root) ∨
    ∃ (badRoot : Root) (badState : BeaconState preset fork),
      store.blockStates[badRoot]? = some badState ∧
      SszType.hashTreeRoot badState = .ok (Vector.replicate 32 0) ∧
      store.isAncestor ⟨root, .pending⟩ ⟨badRoot, .pending⟩ = .ok true := by
  by_cases early : view.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState
  · exact .inl early
  right
  have afterF : getCurrentEpoch anchorState < view.finalizedCheckpoint.epoch :=
    UInt64.not_le.mp early
  -- The view keeps its checkpoints ordered, whether it is the held state or its pull-up.
  have holds : Invariant state := (Store.Reachable.ordered sound reachable).2 held
  have ordered : CheckpointsOrdered view := by
    rcases selected with rfl | pulled
    · exact holds.ordered
    · exact (processJustificationAndFinalization_invariant holds.ordered holds.settled pulled).1
  obtain ⟨finalizedLe, previousLe⟩ := ordered
  have epochLe : view.finalizedCheckpoint.epoch ≤ view.currentJustifiedCheckpoint.epoch :=
    UInt64.le_trans finalizedLe previousLe
  have afterJ : getCurrentEpoch anchorState < view.currentJustifiedCheckpoint.epoch := by
    have := UInt64.lt_iff_toNat_lt.mp afterF
    have := UInt64.le_iff_toNat_le.mp epochLe
    exact UInt64.lt_iff_toNat_lt.mpr (by omega)
  -- Both checkpoints lie on the chain of the same source block, or a zero-hashing state does.
  rcases reachable.checkpoint_source_ancestor sound positive window anchorSlot unknownParent held
      selected (checkpoint := view.finalizedCheckpoint) (.inr (.inr rfl)) afterF with
    ⟨-, blockF⟩ | bad
  · rcases reachable.checkpoint_source_ancestor sound positive window anchorSlot unknownParent
        held selected (checkpoint := view.currentJustifiedCheckpoint) (.inr (.inl rfl)) afterJ with
      ⟨-, blockJ⟩ | bad
    · left
      obtain ⟨startF, startedF, walkF⟩ := Store.getCheckpointBlock_ok_iff.mp blockF
      obtain ⟨startJ, startedJ, walkJ⟩ := Store.getCheckpointBlock_ok_iff.mp blockJ
      have startLe : startF ≤ startJ := by
        rw [computeStartSlotAtEpoch_ok_iff] at startedF startedJ
        rw [UInt64.le_iff_toNat_le, startedF.2, startedJ.2]
        exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp epochLe)
      obtain ⟨nodeJ, reachedJ, rootJ⟩ : ∃ node, store.getAncestor ⟨root, .pending⟩ startJ =
          .ok node ∧ node.root = view.currentJustifiedCheckpoint.root := by
        cases reached : store.getAncestor ⟨root, .pending⟩ startJ <;>
          simp_all [Functor.map, Except.map]
      -- The walk to the finalized start can stop at the justified block on the way.
      have walk : (·.root) <$> store.getAncestor ⟨view.currentJustifiedCheckpoint.root, .pending⟩
          startF = .ok view.finalizedCheckpoint.root := by
        rw [← rootJ, ← Store.getAncestor_root nodeJ .pending startF,
          ← Store.getAncestor_trans startLe reachedJ]
        exact walkF
      exact ⟨Store.isAncestor_of_getAncestor_root
          (reachable.parentsBelow anchorSlot unknownParent) walk,
        Store.getCheckpointBlock_ok_iff.mpr ⟨startF, startedF, walk⟩⟩
    · exact .inr bad
  · exact .inr bad

end EthLib.Consensus
