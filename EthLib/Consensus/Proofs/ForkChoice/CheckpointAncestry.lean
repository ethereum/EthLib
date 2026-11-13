module

public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.DirectSafety.Safety
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

The finalized checkpoint of the store is on the chain of its justified checkpoint in the same way.

Otherwise the runs to the two held states of those checkpoints bound the accountable stake.

Or their hashes show a collision or a zero root.

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
  obtain ⟨_, caught, -, catchUp, ticked⟩ := Store.onTick_ok ticked
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

/-- Two checkpoint blocks of one chain, at ordered epochs, are on one chain themselves.

The earlier block is the ancestor of the later one at the first slot of the earlier epoch. -/
private theorem getCheckpointBlock_of_le (lower : store.ParentsBelow)
    {root early late : Root} {earlyEpoch lateEpoch : Epoch} (ordered : earlyEpoch ≤ lateEpoch)
    (earlyBlock : store.getCheckpointBlock root earlyEpoch = .ok early)
    (lateBlock : store.getCheckpointBlock root lateEpoch = .ok late) :
    store.isAncestor ⟨late, .pending⟩ ⟨early, .pending⟩ = .ok true ∧
      store.getCheckpointBlock late earlyEpoch = .ok early := by
  obtain ⟨startEarly, startedEarly, walkEarly⟩ := getCheckpointBlock_ok_iff.mp earlyBlock
  obtain ⟨startLate, startedLate, walkLate⟩ := getCheckpointBlock_ok_iff.mp lateBlock
  have startLe : startEarly ≤ startLate := by
    rw [computeStartSlotAtEpoch_ok_iff] at startedEarly startedLate
    rw [UInt64.le_iff_toNat_le, startedEarly.2, startedLate.2]
    exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp ordered)
  obtain ⟨node, reached, nodeRoot⟩ : ∃ node, store.getAncestor ⟨root, .pending⟩ startLate =
      .ok node ∧ node.root = late := by
    cases reaching : store.getAncestor ⟨root, .pending⟩ startLate <;>
      simp_all [Functor.map, Except.map]
  -- The walk to the earlier start can stop at the later block on the way.
  have walk : (·.root) <$> store.getAncestor ⟨late, .pending⟩ startEarly = .ok early := by
    rw [← nodeRoot, ← getAncestor_root node .pending startEarly,
      ← getAncestor_trans startLe reached]
    exact walkEarly
  exact ⟨isAncestor_of_getAncestor_root lower walk,
    getCheckpointBlock_ok_iff.mpr ⟨startEarly, startedEarly, walk⟩⟩

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
    store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root ∨
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
    · exact .inl path
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
    blockF | bad
  · rcases reachable.checkpoint_source_ancestor sound positive window anchorSlot unknownParent
        held selected (checkpoint := view.currentJustifiedCheckpoint) (.inr (.inl rfl)) afterJ with
      blockJ | bad
    · exact .inl (Store.getCheckpointBlock_of_le (reachable.parentsBelow anchorSlot unknownParent)
        epochLe blockF blockJ)
    · exact .inr bad
  · exact .inr bad

/-! ## Runs of the held states -/

/-- The last state of a run is one of its hashed objects. -/
private theorem state_mem_hashObjects {config : Config} {checks : SignatureChecks}
    {first last : ForkedBeaconState preset} (run : Run config checks first last) :
    DirectSafety.HashObject.state last ∈ run.hashObjects := by
  cases run with
  | nil => simp [Run.hashObjects]
  | snoc pre step =>
    exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl (by simp))))

/-- Slots of one fork before its next fork extend a run with slot steps.

They add no header and keep every hashed object of the run. -/
private theorem exists_run_of_advanceSlots {config : Config} {checks : SignatureChecks}
    {g x : ForkedBeaconState preset} {bound : Nat} (pre : Run config checks g x)
    (early : ∀ next ∈ config.nextFork fork,
      bound < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    ∀ (count : Nat) {state after : BeaconState preset fork}
      (tail : Run config checks x ⟨fork, state⟩),
      advanceSlots config checks count state = .ok after → state.slot.toNat + count ≤ bound →
      ∃ next : Run config checks x ⟨fork, after⟩,
        (pre.append next).headers = (pre.append tail).headers ∧
        (pre.append tail).hashObjects ⊆ (pre.append next).hashObjects
  | 0, state, after, tail, computed, _ => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨tail, rfl, List.Subset.refl _⟩
  | count + 1, state, after, tail, computed, within => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, stepOk, rest⟩ := computed
    have slot := advanceSlot_slot stepOk
    have across : advanceSlotAcross config checks ⟨fork, state⟩ = .ok ⟨fork, middle⟩ := by
      rw [advanceSlotAcross_of_before fun next scheduled => by
        have := early next scheduled
        omega, stepOk]
      rfl
    obtain ⟨next, headers, objects⟩ :=
      exists_run_of_advanceSlots pre early count (tail.snoc (.slot across)) rest (by omega)
    refine ⟨next, headers.trans ?_, fun object member => objects ?_⟩
    · simp [Run.append, Run.headers, Step.headers]
    · simp [Run.append, Run.hashObjects, member]

/-- A held state on the chain of a held block is hashed by the run of that block.

The run hashes the state of each block that a walk from the held block reaches. -/
private theorem state_mem_hashObjects_of_isAncestor {config : Config}
    {checks : SignatureChecks} {store : Store preset fork} {g a : ForkedBeaconState preset}
    {run : Run config checks g a} {root bad : Root} {badState : BeaconState preset fork}
    (reachedHeld : ∀ (slot : Slot) (reached : Root),
      (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok reached →
      ∃ reachedState : BeaconState preset fork, store.blockStates[reached]? = some reachedState ∧
        DirectSafety.HashObject.state ⟨fork, reachedState⟩ ∈ run.hashObjects)
    (badHeld : store.blockStates[bad]? = some badState)
    (descends : store.isAncestor ⟨root, .pending⟩ ⟨bad, .pending⟩ = .ok true) :
    DirectSafety.HashObject.state ⟨fork, badState⟩ ∈ run.hashObjects := by
  -- A pending ancestor is the root that the walk reaches at the slot of its block.
  obtain ⟨slot, walk⟩ : ∃ slot : Slot,
      (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok bad := by
    unfold Store.isAncestor at descends
    cases known : store.block bad with
    | error e => simp [known, bind, Except.bind] at descends
    | ok badBlock =>
      cases walk : store.getAncestor ⟨root, .pending⟩ badBlock.slot with
      | error e => simp [known, walk, bind, Except.bind] at descends
      | ok node =>
        refine ⟨badBlock.slot, ?_⟩
        by_cases gloas : .glamsterdam ≤ fork <;>
          simp_all [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  obtain ⟨reachedState, reachedHeld', member⟩ := reachedHeld slot bad walk
  rw [badHeld, Option.some.injEq] at reachedHeld'
  exact reachedHeld' ▸ member

/-- Two held blocks whose runs share their headers up to an epoch share its checkpoint block.

The runs extend one run to the anchor, and the epoch starts at or after the anchor block. -/
private theorem getCheckpointBlock_eq_of_checkpointPath {config : Config}
    {checks : SignatureChecks} {store : Store preset fork}
    {anchorBlock : BeaconBlock preset fork} {g x a b : ForkedBeaconState preset}
    {pre : Run config checks g x} {left : Run config checks x a} {right : Run config checks x b}
    {extraLeft extraRight : List BeaconBlockHeader} {rootLeft rootRight : Root}
    {epoch : Epoch} {start : Slot} {checkpoint : Root}
    (headersLeft : (pre.append left).headers = pre.headers ++ extraLeft)
    (headersRight : (pre.append right).headers = pre.headers ++ extraRight)
    (lastLeft : ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
      (·.root) <$> store.getAncestor ⟨rootLeft, .pending⟩ slot = .ok reached ∧
      (((extraLeft.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
          SszType.hashTreeRoot anchorBlock = .ok reached) ∨
        ∃ header, (extraLeft.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
            some header ∧ SszType.hashTreeRoot header = .ok reached))
    (lastRight : ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
      (·.root) <$> store.getAncestor ⟨rootRight, .pending⟩ slot = .ok reached ∧
      (((extraRight.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
          SszType.hashTreeRoot anchorBlock = .ok reached) ∨
        ∃ header, (extraRight.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
            some header ∧ SszType.hashTreeRoot header = .ok reached))
    (startOk : computeStartSlotAtEpoch preset epoch = .ok start)
    (later : anchorBlock.slot ≤ start)
    (paths : (pre.append left).checkpointPath epoch = (pre.append right).checkpointPath epoch)
    (found : store.getCheckpointBlock rootLeft epoch = .ok checkpoint) :
    store.getCheckpointBlock rootRight epoch = .ok checkpoint := by
  have startEq := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
  -- Past the shared run to the anchor, the two runs have the same headers up to the epoch.
  have same : (extraLeft.filter fun header => header.slot.toNat ≤ start.toNat) =
      extraRight.filter fun header => header.slot.toNat ≤ start.toNat := by
    unfold Run.checkpointPath at paths
    rw [headersLeft, headersRight, List.filter_append, List.filter_append] at paths
    simpa only [startEq] using List.append_cancel_left paths
  obtain ⟨start', startOk', walkLeft⟩ := Store.getCheckpointBlock_ok_iff.mp found
  rw [startOk, Except.ok.injEq] at startOk'
  subst start'
  obtain ⟨reachedLeft, walkLeft', casesLeft⟩ := lastLeft start later
  rw [walkLeft, Except.ok.injEq] at walkLeft'
  subst reachedLeft
  obtain ⟨reachedRight, walkRight, casesRight⟩ := lastRight start later
  refine Store.getCheckpointBlock_ok_iff.mpr ⟨start, startOk, ?_⟩
  rw [walkRight, Except.ok.injEq]
  rw [← same] at casesRight
  rcases casesLeft with ⟨noneLeft, hashLeft⟩ | ⟨header, lastLeft, hashLeft⟩ <;>
    rcases casesRight with ⟨noneRight, hashRight⟩ | ⟨header', lastRight, hashRight⟩
  · exact Except.ok.inj (hashRight.symm.trans hashLeft)
  · rw [noneLeft] at lastRight
    cases lastRight
  · rw [lastLeft] at noneRight
    cases noneRight
  · rw [lastLeft, Option.some.injEq] at lastRight
    subst lastRight
    exact Except.ok.inj (hashRight.symm.trans hashLeft)

section StoreRuns

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

/-- A held state follows from the anchor state by a run whose blocks are those of its chain.

Every block of the store was imported with one set of signature checks.

No upgrade is due at any held slot, so the in-fork transition of the store is a run of steps.

The run adds the headers of the blocks on the chain to the headers of the run to the anchor.

A walk from the held block reaches a held state whose state the run hashes.

From the slot of the anchor block on, it reaches the last block of the chain at or below the slot.

That block is the anchor block when the chain has no later block at or below the slot. -/
private theorem Store.Reachable.exists_run_of_blockState {config : Config}
    {checks : SignatureChecks} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    {g : ForkedBeaconState preset}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (linked : store.Linked anchorBlock.parentRoot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    (imported : ∀ ⦃root : Root⦄ ⦃block : BeaconBlock preset fork⦄
      ⦃state : BeaconState preset fork⦄, store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ (parent : BeaconState preset fork) (engine : ExecutionEngine preset fork)
        (signed : SignedBeaconBlock preset fork), signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    {root : Root} {state : BeaconState preset fork}
    (held : store.blockStates[root]? = some state) :
    ∃ (tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩)
      (extra : List BeaconBlockHeader),
      (pre.append tail).headers = pre.headers ++ extra ∧
      (∀ (slot : Slot) (reached : Root),
        (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok reached →
        ∃ reachedState : BeaconState preset fork, store.blockStates[reached]? = some reachedState ∧
          DirectSafety.HashObject.state ⟨fork, reachedState⟩ ∈ (pre.append tail).hashObjects) ∧
      ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
        (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok reached ∧
        (((extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
            SszType.hashTreeRoot anchorBlock = .ok reached) ∨
          ∃ header, (extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
              some header ∧ SszType.hashTreeRoot header = .ok reached) := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState held
  obtain ⟨post, postOk, anchored, -⟩ := reachable.blockStatesFromParents found
  rw [held, Option.some.injEq] at postOk
  subst post
  by_cases same : block = anchorBlock
  · -- The anchor state ends the run to the anchor, and every walk from it stays at its block.
    obtain rfl := anchored same
    subst same
    refine ⟨.nil, [], by simp [Run.append], fun slot reached walk => ?_, fun slot later =>
      ⟨root, ?_, .inl ⟨by simp, reachable.root found⟩⟩⟩
    · refine ⟨state, ?_, state_mem_hashObjects (pre.append .nil)⟩
      by_cases below : block.slot ≤ slot
      · rw [Store.getAncestor_of_le found below] at walk
        cases walk
        exact held
      · -- Below the anchor block the walk needs the parent of the anchor, which the store lacks.
        obtain ⟨node, walkNode, -⟩ : ∃ node, store.getAncestor ⟨root, .pending⟩ slot = .ok node ∧
            node.root = reached := by
          cases reaching : store.getAncestor ⟨root, .pending⟩ slot <;>
            simp_all [Functor.map, Except.map]
        rw [Store.getAncestor] at walkNode
        split at walkNode
        · simp_all
        · rename_i known same
          rw [found, Option.some.injEq] at same
          subst same
          simp only [below, ↓reduceIte] at walkNode
          split at walkNode
          · simp [throw, throwThe, MonadExceptOf.throw] at walkNode
          · rename_i parentKnown
            rw [unknownParent] at parentKnown
            cases parentKnown
    · rw [Store.getAncestor_of_le found later]
      rfl
  obtain ⟨parent, engine, signed, message, parentHeld, transitioned⟩ :=
    imported found held same
  subst message
  obtain ⟨parentBlock, parentFound, -⟩ := linked.stateAfter _ _ parentHeld
  have lower := linked.parentsBelow _ _ _ found parentFound
  obtain ⟨tailP, extraP, headersP, reachedP, lastP⟩ :=
    reachable.exists_run_of_blockState linked unknownParent imported early pre parentHeld
  have bounds := stateTransition_slot transitioned
  obtain ⟨_, _, _, _, blockOk, _⟩ := stateTransition_ok transitioned
  obtain ⟨bodyRoot, bodyHashed, -⟩ := latestBlockHeader_processBlock blockOk
  have unfolded := transitioned
  simp only [stateTransition, bind_ok_iff] at unfolded
  obtain ⟨advanced, slotsOk, applied⟩ := unfolded
  have advancedSlot := (processSlots_slot slotsOk).2
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨-, -, run⟩ := slotsOk
  have bound : ∀ next ∈ config.nextFork fork,
      signed.message.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat :=
    fun next scheduled => bounds.2 ▸ early next scheduled held
  -- The slots up to the block extend the run of the parent, and the block step follows.
  obtain ⟨tailA, headersA, objectsA⟩ := exists_run_of_advanceSlots pre bound _ tailP run
    (by have := UInt64.lt_iff_toNat_lt.mp bounds.1; omega)
  have due : upgradeDue config ⟨fork, advanced⟩ = false :=
    upgradeDue_of_before fun next scheduled => advancedSlot ▸ bound next scheduled
  let header : BeaconBlockHeader := ⟨signed.message.slot, signed.message.proposerIndex,
    signed.message.parentRoot, signed.message.stateRoot, bodyRoot⟩
  have headerOk : DirectSafety.blockHeader signed.message = some header := by
    simp [DirectSafety.blockHeader, bodyHashed, Except.toOption, header]
  have headerRoot : SszType.hashTreeRoot header = .ok root :=
    (BeaconBlock.hashTreeRoot_header bodyHashed).trans (reachable.root found)
  let tail := tailA.snoc (.block engine signed due applied)
  have objects : (pre.append tailP).hashObjects ⊆ (pre.append tail).hashObjects :=
    fun object member => List.mem_append.mpr (.inl (objectsA member))
  refine ⟨tail, extraP ++ [header], ?_, fun slot reached walk => ?_, fun slot later => ?_⟩
  · show (pre.append tailA).headers ++ (DirectSafety.blockHeader signed.message).toList = _
    rw [headersA, headersP, headerOk]
    simp
  · by_cases above : signed.message.slot ≤ slot
    · rw [Store.getAncestor_of_le found above] at walk
      cases walk
      exact ⟨state, held, state_mem_hashObjects (pre.append tail)⟩
    · rw [Store.getAncestor_root_of_parent found parentFound lower (UInt64.not_le.mp above)]
        at walk
      obtain ⟨reachedState, reachedHeld, member⟩ := reachedP slot reached walk
      exact ⟨reachedState, reachedHeld, objects member⟩
  · by_cases above : signed.message.slot ≤ slot
    · refine ⟨root, by rw [Store.getAncestor_of_le found above]; rfl, .inr ⟨header, ?_, headerRoot⟩⟩
      have : header.slot.toNat ≤ slot.toNat := UInt64.le_iff_toNat_le.mp above
      simp [List.filter_append, this]
    · rw [Store.getAncestor_root_of_parent found parentFound lower (UInt64.not_le.mp above)]
      obtain ⟨reached, walk, cases⟩ := lastP slot later
      refine ⟨reached, walk, ?_⟩
      have : ¬ header.slot.toNat ≤ slot.toNat := fun le =>
        above (UInt64.le_iff_toNat_le.mpr le)
      simpa [List.filter_append, this] using cases
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1


/-- The finalized checkpoint of a store is on the chain of its justified checkpoint, or it is early.

Otherwise two runs to held states of the store bound the accountable stake, or show hash evidence.

The store is reachable from an anchor whose parent it does not hold.

A run from a genesis built from deposits reaches the anchor state.

Every block of the store was imported with one set of signature checks.

No upgrade is due at a held slot, so the in-fork transitions of the store are steps of a run.

These hypotheses are sufficient for the proof; they are not claimed to be necessary.

The first alternative puts the finalized epoch at or before the epoch of the anchor state.

The second puts the finalized checkpoint at the first slot of its epoch on the justified chain.

The third gives the runs from the anchor to the held states of the two fields.

Each field is that of its held state, or of the justification step that fork choice runs on it.

The bound is that of direct accountable safety at the anchor state.

Its drift observes the runs up to one epoch past the justified epoch.

The stake floor covers the epoch calls of every run from the anchor to a held state.

It also covers each held state up to one epoch past the justified epoch, for that step. -/
theorem Store.Reachable.finalized_ancestor_or_accountable {config : Config}
    {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork} {g : ForkedBeaconState preset}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (parameters : DirectSafety.Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    (imported : ∀ ⦃root : Root⦄ ⦃block : BeaconBlock preset fork⦄
      ⦃state : BeaconState preset fork⦄, store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ (parent : BeaconState preset fork) (engine : ExecutionEngine preset fork)
        (signed : SignedBeaconBlock preset fork), signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (enough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      ∀ tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
        DirectSafety.EnoughStake (pre.append tail) store.justifiedCheckpoint.epoch.toNat)
    (heldEnough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      (getCurrentEpoch state).toNat ≤ store.justifiedCheckpoint.epoch.toNat + 1 →
      GENESIS_EPOCH + 1 < getCurrentEpoch state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state)) :
    store.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState ∨
    (store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
        ⟨store.finalizedCheckpoint.root, .pending⟩ = .ok true ∧
      store.getCheckpointBlock store.justifiedCheckpoint.root
        store.finalizedCheckpoint.epoch = .ok store.finalizedCheckpoint.root) ∨
    ∃ (stateA stateB : BeaconState preset fork)
      (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
      (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
      (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
      (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
      (∃ rootA : Root, store.blockStates[rootA]? = some stateA) ∧
      (∃ rootB : Root, store.blockStates[rootB]? = some stateB) ∧
      va.state.finalizedCheckpoint = store.finalizedCheckpoint ∧
      vb.state.currentJustifiedCheckpoint = store.justifiedCheckpoint ∧
      (Models.stake (DirectSafety.effectiveWeight anchorState)
          (DirectSafety.activeKeys anchorState) ≤
        3 * Models.stake (DirectSafety.effectiveWeight anchorState)
          (DirectSafety.accountableKeys (pre.append left) (pre.append right)
            ⟨fork, anchorState⟩) +
        2 * max (DirectSafety.terminalDrift store.justifiedCheckpoint.epoch.toNat left va)
          (DirectSafety.terminalDrift store.justifiedCheckpoint.epoch.toNat right vb) ∨
      DirectSafety.HashEvidence ((pre.append left).hashObjects ++
        (pre.append right).hashObjects)) := by
  -- The run from genesis gives the anchor its invariant, and the parameters give the window.
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := parameters.roots
    omega
  have linked := reachable.linked_of_unknown anchorSlot unknownParent
  have lower := reachable.parentsBelow anchorSlot unknownParent
  have ordered : store.finalizedCheckpoint.epoch ≤ store.justifiedCheckpoint.epoch :=
    (Store.Reachable.ordered sound reachable).1.1
  by_cases atAnchor : store.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState
  · exact .inl atAnchor
  have afterF : getCurrentEpoch anchorState < store.finalizedCheckpoint.epoch :=
    UInt64.not_le.mp atAnchor
  have afterJ : getCurrentEpoch anchorState < store.justifiedCheckpoint.epoch :=
    UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_lt_of_le (UInt64.lt_iff_toNat_lt.mp afterF)
      (UInt64.le_iff_toNat_le.mp ordered))
  -- After the anchor epoch, a field comes from a held state or from the step on it.
  have source (field : BeaconState preset fork → Checkpoint) (checkpoint : Checkpoint)
      (after : getCurrentEpoch anchorState < checkpoint.epoch)
      (origin : (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
          checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
        (∃ (root : Root) (state : BeaconState preset fork),
          store.blockStates[root]? = some state ∧ checkpoint = field state) ∨
        ∃ (root : Root) (state pulled : BeaconState preset fork),
          store.blockStates[root]? = some state ∧
          processJustificationAndFinalization state = .ok pulled ∧ checkpoint = field pulled) :
      ∃ (root : Root) (state : BeaconState preset fork)
        (view : DirectSafety.TerminalView ⟨fork, state⟩),
        store.blockStates[root]? = some state ∧ checkpoint = field view.state ∧
        (view.state = state ∨ processJustificationAndFinalization state = .ok view.state) ∧
        view.enough store.justifiedCheckpoint.epoch.toNat := by
    rcases origin with ⟨root, -, rfl⟩ | ⟨root, state, held, rfl⟩ |
      ⟨root, state, pulled, held, ok, rfl⟩
    · exact absurd (UInt64.lt_iff_toNat_lt.mp after) (Nat.lt_irrefl _)
    · exact ⟨root, state, .realized, held, rfl, .inl rfl, trivial⟩
    · exact ⟨root, state, .pulled pulled ok, held, rfl, .inr ok,
        fun horizon later => heldEnough held horizon later⟩
  obtain ⟨rootA, stateA, va, heldA, fieldA, selectedA, terminalA⟩ :=
    source (·.finalizedCheckpoint) _ afterF (reachable.finalized_origins _ (.inl rfl))
  obtain ⟨rootB, stateB, vb, heldB, fieldB, selectedB, terminalB⟩ :=
    source (·.currentJustifiedCheckpoint) _ afterJ (reachable.justified_origins _ (.inl rfl))
  -- The runs from the anchor to the two held states.
  obtain ⟨left, extraA, headersA, reachedA, lastA⟩ :=
    reachable.exists_run_of_blockState linked unknownParent imported early pre heldA
  obtain ⟨right, extraB, headersB, reachedB, lastB⟩ :=
    reachable.exists_run_of_blockState linked unknownParent imported early pre heldB
  -- A held state on a source chain that hashes to zero is hash evidence of that chain's run.
  have evidence {state : BeaconState preset fork}
      (member : DirectSafety.HashObject.state ⟨fork, state⟩ ∈
        (pre.append left).hashObjects ++ (pre.append right).hashObjects)
      (hashed : SszType.hashTreeRoot state = .ok (Vector.replicate 32 0)) :
      DirectSafety.HashEvidence ((pre.append left).hashObjects ++
        (pre.append right).hashObjects) := by
    unfold DirectSafety.HashEvidence
    exact .inr ⟨_, member, by simp [DirectSafety.HashObject.root, hashed, Except.toOption]⟩
  by_cases paths : (pre.append left).checkpointPath store.finalizedCheckpoint.epoch =
      (pre.append right).checkpointPath store.finalizedCheckpoint.epoch
  · -- Equal paths put the finalized block of the left chain on the justified chain.
    rcases reachable.checkpoint_source_ancestor sound positive window anchorSlot unknownParent
        heldA selectedA (.inr (.inr fieldA)) afterF with blockA | ⟨bad, badState, badHeld, hashed,
        descends⟩
    · rcases reachable.checkpoint_source_ancestor sound positive window anchorSlot unknownParent
          heldB selectedB (.inr (.inl fieldB)) afterJ with blockB | ⟨bad, badState, badHeld,
          hashed, descends⟩
      · obtain ⟨start, startOk, -⟩ := Store.getCheckpointBlock_ok_iff.mp blockA
        have later : anchorBlock.slot ≤ start :=
          UInt64.le_trans anchorSlot (slot_le_of_getCurrentEpoch_lt positive afterF startOk)
        have blockBF := getCheckpointBlock_eq_of_checkpointPath headersA headersB lastA lastB
          startOk later paths blockA
        exact .inr (.inl (Store.getCheckpointBlock_of_le lower ordered blockBF blockB))
      · exact .inr (.inr ⟨stateA, stateB, left, right, va, vb, ⟨rootA, heldA⟩, ⟨rootB, heldB⟩,
          fieldA.symm, fieldB.symm, .inr (evidence (List.mem_append_right _
            (state_mem_hashObjects_of_isAncestor reachedB badHeld descends)) hashed)⟩)
    · exact .inr (.inr ⟨stateA, stateB, left, right, va, vb, ⟨rootA, heldA⟩, ⟨rootB, heldB⟩,
        fieldA.symm, fieldB.symm, .inr (evidence (List.mem_append_left _
          (state_mem_hashObjects_of_isAncestor reachedA badHeld descends)) hashed)⟩)
  · -- Different paths conflict, and direct accountable safety covers the two views.
    have conflict : DirectSafety.Conflict (pre.append left) (pre.append right)
        va.state.finalizedCheckpoint store.justifiedCheckpoint := by
      rw [← fieldA]
      simpa only [DirectSafety.Conflict, UInt64.min_def, ite_eq_left ordered] using paths
    exact .inr (.inr ⟨stateA, stateB, left, right, va, vb, ⟨rootA, heldA⟩, ⟨rootB, heldB⟩,
      fieldA.symm, fieldB.symm, DirectSafety.accountable_safety_justified_terminal pre left right
        va vb parameters genesis store.justifiedCheckpoint (enough heldA left)
        (enough heldB right) terminalA terminalB (.inr fieldB) (fieldA ▸ ordered) conflict⟩)

end StoreRuns

end EthLib.Consensus
