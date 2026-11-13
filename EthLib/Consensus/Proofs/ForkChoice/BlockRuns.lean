module

public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
public import EthLib.Consensus.Proofs.Transition.RunKept

/-!
# Proofs: the states of a store run on along its chains of blocks

In a reachable store, each block state is at or after the anchor state.

So each known block is at or after the anchor block.

This needs the anchor block not to be after the anchor state.

The walk back from a block to an earlier slot passes through blocks whose states form a run.

So the state of the ancestor that the walk reaches runs on to the state of the block.

With one setting of the signature checks, the state of a checkpoint also runs on.

It runs to the state of each block that has the checkpoint block as its ancestor.

That ancestor is taken at the start of the checkpoint epoch.

The block must be at or after that start.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork} {config : Config}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

/-- In a reachable store, each block state is at or after the anchor state. -/
theorem Store.Reachable.anchorSlot_le_of_blockState
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    {state : BeaconState preset fork} (found : store.blockStates[root]? = some state) :
    anchorState.slot ≤ state.slot := by
  induction hslot : state.slot.toNat using Nat.strong_induction_on generalizing root state with
  | _ n ih =>
  obtain ⟨block, blockFound⟩ := reachable.known_of_blockState found
  obtain ⟨kept, keptFound, isAnchor, notAnchor⟩ := reachable.blockStatesFromParents blockFound
  rw [found, Option.some.injEq] at keptFound
  subst keptFound
  by_cases same : block = anchorBlock
  · rw [isAnchor same]
    exact UInt64.le_refl _
  · obtain ⟨parentState, checks, engine, signed, -, -, parentFound, transition⟩ :=
      notAnchor same
    obtain ⟨lower, atBlock⟩ := stateTransition_slot transition
    rw [← atBlock] at lower
    exact UInt64.le_trans (ih _ (hslot ▸ UInt64.lt_iff_toNat_lt.mp lower) parentFound rfl)
      (UInt64.le_of_lt lower)

/-- In a reachable store, each known block is at or after the anchor block.

The anchor block must not be after the anchor state. -/
theorem Store.Reachable.anchorSlot_le
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block) :
    anchorBlock.slot ≤ block.slot := by
  obtain ⟨_, -, -, notAnchor⟩ := reachable.blockStatesFromParents found
  by_cases same : block = anchorBlock
  · rw [same]
    exact UInt64.le_refl _
  · obtain ⟨parentState, checks, engine, signed, -, message, parentFound, transition⟩ :=
      notAnchor same
    obtain ⟨lower, -⟩ := stateTransition_slot transition
    rw [message] at lower
    exact UInt64.le_trans anchorSlot (UInt64.le_trans
      (reachable.anchorSlot_le_of_blockState parentFound) (UInt64.le_of_lt lower))

/-- In a reachable store, a walk back from a block gives a run to its state.

The run starts at the state of the ancestor that the walk reaches.

The anchor block must not be after the anchor state. -/
theorem Store.Reachable.runKept_of_getAncestor
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {node ancestor : ForkChoiceNode} {slot : Slot} {state ancestorState : BeaconState preset fork}
    (walk : store.getAncestor node slot = .ok ancestor)
    (stateFound : store.blockStates[node.root]? = some state)
    (ancestorFound : store.blockStates[ancestor.root]? = some ancestorState) :
    RunKept ancestorState state := by
  induction node using Store.getAncestor.induct (store := store) (slot := slot)
    generalizing state with
  | case1 node notFound =>
    rw [Store.getAncestor] at walk
    split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case2 node block blockFound le =>
    rw [Store.getAncestor_of_le blockFound le, Except.ok.injEq] at walk
    subst walk
    rw [stateFound, Option.some.injEq] at ancestorFound
    exact ancestorFound ▸ RunKept.refl _
  | case3 node block blockFound above parentNotFound =>
    rw [Store.getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [blockFound, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case4 node block blockFound above parent parentFound lower ih =>
    rw [Store.getAncestor_step blockFound above parentFound lower] at walk
    obtain ⟨kept, keptFound, -, notAnchor⟩ := reachable.blockStatesFromParents blockFound
    rw [stateFound, Option.some.injEq] at keptFound
    subst keptFound
    have notAnchorBlock : block ≠ anchorBlock := by
      rintro rfl
      exact absurd (reachable.anchorSlot_le anchorSlot parentFound) (UInt64.not_le.mpr lower)
    obtain ⟨parentState, checks, engine, signed, -, -, parentStateFound, transition⟩ :=
      notAnchor notAnchorBlock
    exact (ih walk parentStateFound).trans (runKept_stateTransition transition)
  | case5 node block blockFound above parent parentFound notLower =>
    rw [Store.getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [blockFound, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk
      · simp_all
      · rename_i p same
        rw [parentFound, Option.some.injEq] at same
        subst same
        simp [notLower, throw, throwThe, MonadExceptOf.throw] at walk

/-- A walk back stays at a block at or below the slot.

Otherwise it ends at the parent of a block above the slot.

The walk to the slot of that block reaches it. -/
private theorem Store.getAncestor_last {node ancestor : ForkChoiceNode} {slot : Slot}
    {block : BeaconBlock preset fork} (found : store.blocks[node.root]? = some block)
    (walk : store.getAncestor node slot = .ok ancestor) :
    (block.slot ≤ slot ∧ ancestor = node) ∨
      ∃ child childBlock, store.blocks[child.root]? = some childBlock ∧
        childBlock.slot ≤ block.slot ∧ slot < childBlock.slot ∧
        childBlock.parentRoot = ancestor.root ∧
        store.getAncestor node childBlock.slot = .ok child := by
  induction node using Store.getAncestor.induct (store := store) (slot := slot)
    generalizing block with
  | case1 node notFound => simp_all
  | case2 node block' blockFound le =>
    rw [found, Option.some.injEq] at blockFound
    subst blockFound
    rw [Store.getAncestor_of_le found le, Except.ok.injEq] at walk
    exact .inl ⟨le, walk.symm⟩
  | case3 node block' blockFound above parentNotFound =>
    rw [Store.getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [blockFound, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case4 node block' blockFound above parent parentFound lower ih =>
    rw [found, Option.some.injEq] at blockFound
    subst blockFound
    rw [Store.getAncestor_step found above parentFound lower] at walk
    right
    rcases ih parentFound walk with ⟨-, rfl⟩ | ⟨child, childBlock, childFound, atMost, below,
        parentRoot, childWalk⟩
    · exact ⟨node, block, found, UInt64.le_refl _, UInt64.not_le.mp above, rfl,
        Store.getAncestor_of_le found (UInt64.le_refl _)⟩
    · have childLower := UInt64.lt_of_le_of_lt atMost lower
      refine ⟨child, childBlock, childFound, UInt64.le_of_lt childLower, below, parentRoot, ?_⟩
      rw [Store.getAncestor_step found (UInt64.not_le.mpr childLower) parentFound lower]
      exact childWalk
  | case5 node block' blockFound above parent parentFound notLower =>
    rw [Store.getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [blockFound, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk
      · simp_all
      · rename_i p same
        rw [parentFound, Option.some.injEq] at same
        subst same
        simp [notLower, throw, throwThe, MonadExceptOf.throw] at walk

/-- In a store built with one setting of the checks, a checkpoint state runs on to a block state.

The checkpoint block must be the ancestor of that block at the start of the epoch.

The block must be at or after that start.

The anchor block must not be after the anchor state. -/
theorem Store.ForwardReachableWith.runKept_of_checkpointState {checks : SignatureChecks}
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    {checkpoint : Checkpoint} {root : Root} {block : BeaconBlock preset fork} {start : Slot}
    {checkpointState state : BeaconState preset fork}
    (target : store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (found : store.blocks[root]? = some block)
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (atOrAfter : start ≤ block.slot)
    (checkpointFound : store.checkpointStates[checkpoint]? = some checkpointState)
    (stateFound : store.blockStates[root]? = some state) :
    RunKept checkpointState state := by
  have reachable := reached.reachable
  simp only [Store.getCheckpointBlock, bind_ok_iff, mapError_ok_iff, pure, Except.pure,
    Except.ok.injEq] at target
  obtain ⟨start', startOk', node, walk, rooted⟩ := target
  rw [startOk, Except.ok.injEq] at startOk'
  subst startOk'
  obtain ⟨base, start', baseFound, startOk', fromBlock⟩ :=
    reached.checkpointStatesFromBlocks checkpointFound
  rw [startOk, Except.ok.injEq] at startOk'
  subst startOk'
  rw [← rooted] at baseFound
  rcases fromBlock with ⟨-, rfl⟩ | ⟨below, checks', rfl, slotsOk⟩
  · exact reachable.runKept_of_getAncestor anchorSlot walk stateFound baseFound
  rcases Store.getAncestor_last found walk with ⟨le, rfl⟩ | ⟨child, childBlock, childFound,
      -, above, parentRoot, childWalk⟩
  · have := reachable.slot_le_of_blockState anchorSlot found baseFound
    exact absurd (UInt64.le_trans atOrAfter this) (UInt64.not_le.mpr below)
  obtain ⟨childState, childStateFound, -, notAnchor⟩ :=
    reached.blockStatesFromParents childFound
  have notAnchorBlock : childBlock ≠ anchorBlock := by
    rintro rfl
    have := UInt64.le_trans anchorSlot (reachable.anchorSlot_le_of_blockState baseFound)
    exact absurd (UInt64.le_trans this (UInt64.le_of_lt below)) (UInt64.not_le.mpr above)
  obtain ⟨parentState, checks', engine, signed, rfl, message, parentFound, transition⟩ :=
    notAnchor notAnchorBlock
  rw [parentRoot, baseFound, Option.some.injEq] at parentFound
  subst parentFound
  exact (runKept_of_processSlots_of_stateTransition slotsOk
      (message ▸ UInt64.le_of_lt above) transition).trans
    (reachable.runKept_of_getAncestor anchorSlot childWalk stateFound childStateFound)

end EthLib.Consensus
