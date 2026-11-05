module

public import EthLib.Consensus.ForkChoice.Store
public import EthLib.Consensus.Proofs.Time

/-!
# Proofs: the store of the fork choice

Each error of the fork choice has its own code.

A new store holds its anchor, justified and finalized, and its clock is at the anchor's slot.

The ancestor of a node at a slot is a known block at or below that slot.

A node at or below the slot is its own ancestor, so every known node descends from itself.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- Two errors with one code come from one constructor. -/
theorem ForkChoiceError.code_injective (e₁ e₂ : ForkChoiceError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Each code is one more than the index of its constructor.
  have back : ∀ e : ForkChoiceError, e.code.toNat - 1 = e.ctorIdx := by
    intro e
    cases e <;> rfl
  rw [← back e₁, ← back e₂, h]

namespace Store

variable {store : Store preset fork}

/-- From Gloas the ancestor walk is not yet specified here, so it fails. -/
theorem getAncestor_of_gloas {node : ForkChoiceNode} {slot : Slot} (gloas : .glamsterdam ≤ fork) :
    store.getAncestor node slot = .error (.forkNotYetSpecified fork) := by
  rw [getAncestor]
  simp [gloas, throw, throwThe, MonadExceptOf.throw]

/-- Before Gloas, a known node at or below the slot is its own ancestor there. -/
theorem getAncestor_of_le {node : ForkChoiceNode} {slot : Slot} {block : BeaconBlock preset fork}
    (before : fork < .glamsterdam) (found : store.blocks[node.root]? = some block)
    (le : block.slot ≤ slot) : store.getAncestor node slot = .ok node := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  rw [getAncestor]
  simp only [later, ↓reduceIte]
  split
  · simp_all
  · rename_i b same
    rw [found, Option.some.injEq] at same
    subst same
    simp [le, pure, Except.pure]

/-- The ancestor of a node at a slot is a known block at or below that slot. -/
theorem getAncestor_le {node ancestor : ForkChoiceNode} {slot : Slot}
    (walk : store.getAncestor node slot = .ok ancestor) :
    ∃ block, store.blocks[ancestor.root]? = some block ∧ block.slot ≤ slot := by
  induction node using getAncestor.induct (store := store) (slot := slot) with
  | case1 node gloas =>
    rw [getAncestor_of_gloas gloas] at walk
    cases walk
  | case2 node later found =>
    rw [getAncestor] at walk
    simp only [later, ↓reduceIte] at walk
    split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case3 node later block found le =>
    rw [getAncestor_of_le (Nat.lt_of_not_le later) found le] at walk
    cases walk
    exact ⟨block, found, le⟩
  | case4 node later block found above parentFound =>
    rw [getAncestor] at walk
    simp only [later, ↓reduceIte] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [found, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case5 node later block found above parent parentFound lower ih =>
    apply ih
    rw [getAncestor] at walk
    simp only [later, ↓reduceIte] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [found, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk
      · simp_all
      · rename_i p same
        rw [parentFound, Option.some.injEq] at same
        subst same
        simpa [lower] using walk
  | case6 node later block found above parent parentFound notLower =>
    rw [getAncestor] at walk
    simp only [later, ↓reduceIte] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [found, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk
      · simp_all
      · rename_i p same
        rw [parentFound, Option.some.injEq] at same
        subst same
        simp [notLower, throw, throwThe, MonadExceptOf.throw] at walk

/-- Before Gloas, every known node descends from itself. -/
theorem isAncestor_self {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    (before : fork < .glamsterdam) (found : store.blocks[node.root]? = some block) :
    store.isAncestor node node = .ok true := by
  have known : store.block node.root = .ok block := by
    simp [Store.block, found, pure, Except.pure]
  simp [isAncestor, known, getAncestor_of_le before found (UInt64.le_refl _), bind, Except.bind,
    pure, Except.pure]

end Store

/-- From Gloas the store is not yet specified here, so a new store fails. -/
theorem getForkchoiceStore_of_gloas {config : Config} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} (gloas : .glamsterdam ≤ fork) :
    getForkchoiceStore config anchorState anchorBlock = .error (.forkNotYetSpecified fork) := by
  simp [getForkchoiceStore, gloas, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A new store holds its anchor block and state, justified and finalized at the anchor's epoch. -/
theorem getForkchoiceStore_anchor {config : Config} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) :
    ∃ anchorRoot, SszType.hashTreeRoot anchorBlock = .ok anchorRoot ∧
      store.blocks[anchorRoot]? = some anchorBlock ∧
      store.blockStates[anchorRoot]? = some anchorState ∧
      store.justifiedCheckpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩ ∧
      store.finalizedCheckpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩ := by
  unfold getForkchoiceStore at made
  split at made
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at made
  cases stateRoot : SszType.hashTreeRoot anchorState with
  | error e => simp [stateRoot, bind, Except.bind, Except.mapError] at made
  | ok stateRoot' =>
    simp only [stateRoot, Except.mapError, bind, Except.bind] at made
    split at made
    · simp [throw, throwThe, MonadExceptOf.throw] at made
    · cases blockRoot : SszType.hashTreeRoot anchorBlock with
      | error e => simp [blockRoot] at made
      | ok anchorRoot =>
        simp only [blockRoot] at made
        cases time : computeTimeAtSlotMs config (secondsToMilliseconds anchorState.genesisTime)
            anchorState.slot with
        | error e => simp [time] at made
        | ok timeMs =>
          simp only [time, pure, Except.pure, Except.ok.injEq] at made
          subst made
          exact ⟨anchorRoot, rfl, by simp, by simp, rfl, rfl⟩

/-- A new store fails when the anchor block does not commit to the anchor state. -/
theorem getForkchoiceStore_mismatch {config : Config} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {stateRoot : Root} (before : fork < .glamsterdam)
    (root : SszType.hashTreeRoot anchorState = .ok stateRoot)
    (differ : anchorBlock.stateRoot ≠ stateRoot) :
    getForkchoiceStore config anchorState anchorBlock = .error .anchorStateMismatch := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp [getForkchoiceStore, later, root, differ, Except.mapError, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw]

/-- The clock of a new store is at the slot of the anchor state, on a chain with nonempty slots. -/
theorem getCurrentSlot_getForkchoiceStore {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork} (positive : 0 < config.SLOT_DURATION_MS)
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) :
    store.getCurrentSlot config = .ok anchorState.slot := by
  unfold getForkchoiceStore at made
  split at made
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at made
  cases stateRoot : SszType.hashTreeRoot anchorState with
  | error e => simp [stateRoot, bind, Except.bind, Except.mapError] at made
  | ok stateRoot' =>
    simp only [stateRoot, Except.mapError, bind, Except.bind] at made
    split at made
    · simp [throw, throwThe, MonadExceptOf.throw] at made
    · cases blockRoot : SszType.hashTreeRoot anchorBlock with
      | error e => simp [blockRoot] at made
      | ok anchorRoot =>
        simp only [blockRoot] at made
        cases time : computeTimeAtSlotMs config (secondsToMilliseconds anchorState.genesisTime)
            anchorState.slot with
        | error e => simp [time] at made
        | ok timeMs =>
          simp only [time, pure, Except.pure, Except.ok.injEq] at made
          subst made
          simp [Store.getCurrentSlot, computeSlotAtTimeMs_computeTimeAtSlotMs positive time,
            Except.mapError]

end EthLib.Consensus
