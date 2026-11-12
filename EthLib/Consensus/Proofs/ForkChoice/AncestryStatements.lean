module

public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints

/-!
# Statements for issue 1423

These are approval candidates, not proofs or an upstream-ready change.

The first two statements match the untimed provenance results on the fork.

An anchor checkpoint is synthesized, and a pulled-up state is not a stored post-state.

State checkpoints at or before the anchor epoch can name blocks outside the store.

The ancestry candidates therefore separate that boundary explicitly.

They retain a concrete zero-state-root witness instead of assuming hash injectivity.

Gasper Section 4.1 defines epoch boundary pairs, including repeated blocks at different epochs.

Section 8.5 gives the four finalization cases.

Source: https://arxiv.org/html/2003.03052v3
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork}

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
        checkpoint = pulled.currentJustifiedCheckpoint := by
  sorry

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
        checkpoint = pulled.finalizedCheckpoint := by
  sorry

/-- A cache entry is the anchor entry or the successful pull-up at its own key.

Unlike the two store fields, a non-anchor entry has no plain held-state alternative. -/
theorem Store.Reachable.unrealizedJustifications_origins {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {key : Root} {checkpoint : Checkpoint}
    (entry : store.unrealizedJustifications[key]? = some checkpoint) :
    (SszType.hashTreeRoot anchorBlock = .ok key ∧
      checkpoint = (⟨getCurrentEpoch anchorState, key⟩ : Checkpoint)) ∨
    ∃ (state pulled : BeaconState preset fork), store.blockStates[key]? = some state ∧
      processJustificationAndFinalization state = .ok pulled ∧
      checkpoint = pulled.currentJustifiedCheckpoint := by
  sorry

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
  sorry

/-- Within one held post-state or its pull-up, finalization precedes current justification.

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
  sorry

end EthLib.Consensus
