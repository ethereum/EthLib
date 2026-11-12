module

public import EthLib.Consensus.ForkChoice.Store
public import EthLib.Consensus.Proofs.Time

/-!
# Proofs: the store of the fork choice

Each error of the fork choice has its own code.

A new store holds its anchor, justified and finalized, and its clock is at the anchor's slot.

The ancestor of a node at a slot is a known block at or below that slot.

A node at or below the slot is its own ancestor, so every known node descends from itself.

A node that descends from a known node sits at the slot of that node or later.

The ancestor of a block at the slot of an earlier parent is the node that the block builds on.

A node descends from its ancestor at any slot.

Each node descends from its parent's pending node when the parent sits at an earlier slot.

The walk to a lower slot can stop at a higher slot on the way, and go on from there.

From Gloas the walk gives each parent an empty or full status.

It reaches the same blocks whatever the status of its start.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The order of checkpoints is transitive, as an order by epoch and then by root. -/
instance : Std.TransCmp Checkpoint.compare :=
  inferInstanceAs
    (Std.TransCmp (compareLex (compareOn Checkpoint.epoch) (compareOn Checkpoint.root)))

/-- Two errors with one code come from one constructor. -/
theorem ForkChoiceError.code_injective (e₁ e₂ : ForkChoiceError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Each code is one more than the index of its constructor.
  have back : ∀ e : ForkChoiceError, e.code.toNat - 1 = e.ctorIdx := by
    intro e
    cases e <;> rfl
  rw [← back e₁, ← back e₂, h]

/-- Before Gloas the epoch of a vote is its target epoch. -/
theorem getLatestMessageEpoch_of_lt {message : LatestMessage fork} (before : fork < .glamsterdam) :
    getLatestMessageEpoch preset message = message.epoch before := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [getLatestMessageEpoch, later, ↓reduceDIte]

/-- From Gloas the epoch of a vote is the epoch of its slot. -/
theorem getLatestMessageEpoch_of_gloas {message : LatestMessage fork}
    (gloas : .glamsterdam ≤ fork) :
    getLatestMessageEpoch preset message = computeEpochAtSlot preset (message.slot gloas) := by
  simp [getLatestMessageEpoch, gloas]

/-- Before Gloas the vote of an attestation ranks by its target epoch. -/
theorem LatestMessage.ofAttestation_rank_of_lt {attestation : Attestation preset fork}
    (before : fork < .glamsterdam) :
    (LatestMessage.ofAttestation attestation).rank = attestation.data.target.epoch := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [LatestMessage.rank, later, ↓reduceDIte]
  rfl

/-- From Gloas the vote of an attestation ranks by its slot. -/
theorem LatestMessage.ofAttestation_rank_of_gloas {attestation : Attestation preset fork}
    (gloas : .glamsterdam ≤ fork) :
    (LatestMessage.ofAttestation attestation).rank = attestation.data.slot := by
  simp [LatestMessage.rank, LatestMessage.ofAttestation, gloas]

/-- From Gloas the vote of an attestation is for the payload exactly when its index is 1. -/
theorem LatestMessage.ofAttestation_payloadPresent {attestation : Attestation preset fork}
    (gloas : .glamsterdam ≤ fork) :
    (LatestMessage.ofAttestation attestation).payloadPresent gloas = true ↔
      attestation.data.index = 1 := by
  simp [LatestMessage.ofAttestation]

namespace Store

variable {store : Store preset fork}

/-- The lookup of a block succeeds exactly when the store holds it. -/
theorem block_ok_iff {root : Root} {block : BeaconBlock preset fork} :
    store.block root = .ok block ↔ store.blocks[root]? = some block := by
  unfold Store.block
  cases store.blocks[root]? <;>
    simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

/-- Before Gloas a parent is pending. -/
theorem parentPayloadStatus_of_lt {block parent : BeaconBlock preset fork}
    (before : fork < .glamsterdam) : parentPayloadStatus block parent = .pending := by
  unfold parentPayloadStatus
  split
  · rename_i gloas
    exact absurd gloas (Nat.not_le_of_lt before)
  · rfl

/-- From Gloas a parent is empty or full, never pending. -/
theorem parentPayloadStatus_ne_pending {block parent : BeaconBlock preset fork}
    (gloas : .glamsterdam ≤ fork) : parentPayloadStatus block parent ≠ .pending := by
  simp only [parentPayloadStatus, gloas, ↓reduceDIte]
  split <;> simp

/-- A known node at or below the slot is its own ancestor there. -/
theorem getAncestor_of_le {node : ForkChoiceNode} {slot : Slot} {block : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block)
    (le : block.slot ≤ slot) : store.getAncestor node slot = .ok node := by
  rw [getAncestor]
  split
  · simp_all
  · rename_i b same
    rw [found, Option.some.injEq] at same
    subst same
    simp [le, pure, Except.pure]

/-- The walk from a known block above the slot moves to the node of its parent.

The parent node has the status of its payload as the block builds on it. -/
theorem getAncestor_step {node : ForkChoiceNode} {slot : Slot}
    {block parent : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block) (above : ¬ block.slot ≤ slot)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (parentLower : parent.slot < block.slot) :
    store.getAncestor node slot =
      store.getAncestor ⟨block.parentRoot, parentPayloadStatus block parent⟩ slot := by
  conv => lhs; rw [getAncestor]
  split
  · simp_all
  · rename_i b same
    rw [found, Option.some.injEq] at same
    subst same
    simp only [above, ↓reduceIte]
    split
    · simp_all
    · rename_i p same
      rw [parentFound, Option.some.injEq] at same
      subst same
      simp [parentLower]

/-- The ancestor of a block at the slot of its parent is the node that the block builds on.

That node is the parent with the payload status that the block gives it.

The walk may start from any node of the block.

The store must hold the parent, at an earlier slot than the block.

This identifies the parent node counted by arXiv 2405.00549v4, Definition 5. -/
theorem getAncestor_parent_of_slot_lt {node : ForkChoiceNode}
    {block parent : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot) :
    store.getAncestor node parent.slot =
      .ok ⟨block.parentRoot, parentPayloadStatus block parent⟩ := by
  rw [getAncestor_step found (UInt64.not_le.mpr lower) parentFound lower]
  exact getAncestor_of_le parentFound (UInt64.le_refl _)

/-- The root that the walk reaches does not depend on the payload status of the start.

So from Gloas the walk reaches the blocks that the earlier walk reaches. -/
theorem getAncestor_root (node : ForkChoiceNode) (status : PayloadStatus) (slot : Slot) :
    (·.root) <$> store.getAncestor node slot =
      (·.root) <$> store.getAncestor ⟨node.root, status⟩ slot := by
  conv => lhs; rw [getAncestor]
  conv => rhs; rw [getAncestor]
  repeat' split
  all_goals (simp_all [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le]; try omega)

/-- The ancestor of a node at a slot is a known block at or below that slot. -/
theorem getAncestor_le {node ancestor : ForkChoiceNode} {slot : Slot}
    (walk : store.getAncestor node slot = .ok ancestor) :
    ∃ block, store.blocks[ancestor.root]? = some block ∧ block.slot ≤ slot := by
  induction node using getAncestor.induct (store := store) (slot := slot) with
  | case1 node found =>
    rw [getAncestor] at walk
    split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case2 node block found le =>
    rw [getAncestor_of_le found le] at walk
    cases walk
    exact ⟨block, found, le⟩
  | case3 node block found above parentFound =>
    rw [getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [found, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case4 node block found above parent parentFound lower ih =>
    rw [getAncestor_step found above parentFound lower] at walk
    exact ih walk
  | case5 node block found above parent parentFound notLower =>
    rw [getAncestor] at walk
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

/-- The ancestor at a lower slot is the ancestor at that slot of the ancestor at a higher slot.

So the walk to a slot can stop at any higher slot on the way. -/
theorem getAncestor_trans {node ancestor : ForkChoiceNode} {higher lower : Slot}
    (le : lower ≤ higher) (walk : store.getAncestor node higher = .ok ancestor) :
    store.getAncestor node lower = store.getAncestor ancestor lower := by
  induction node using getAncestor.induct (store := store) (slot := higher) with
  | case1 node found =>
    rw [getAncestor] at walk
    split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case2 node block found atMost =>
    rw [getAncestor_of_le found atMost] at walk
    cases walk
    rfl
  | case3 node block found above parentFound =>
    rw [getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [found, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case4 node block found above parent parentFound parentLower ih =>
    rw [getAncestor_step found above parentFound parentLower] at walk
    -- The block is above the higher slot, so it is above the lower one, and both walks step up.
    have aboveLower : ¬ block.slot ≤ lower := fun atMost => above (UInt64.le_trans atMost le)
    rw [getAncestor_step found aboveLower parentFound parentLower]
    exact ih walk
  | case5 node block found above parent parentFound notLower =>
    rw [getAncestor] at walk
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

/-- A walk keeps its result in a store that keeps every block of this one. -/
theorem getAncestor_of_blocks {after : Store preset fork} {node ancestor : ForkChoiceNode}
    {slot : Slot}
    (blocks : ∀ {root : Root} {block : BeaconBlock preset fork},
      store.blocks[root]? = some block → after.blocks[root]? = some block)
    (walk : store.getAncestor node slot = .ok ancestor) :
    after.getAncestor node slot = .ok ancestor := by
  induction node using getAncestor.induct (store := store) (slot := slot) with
  | case1 node found =>
    rw [getAncestor] at walk
    split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case2 node block found le =>
    rw [getAncestor_of_le found le] at walk
    cases walk
    exact getAncestor_of_le (blocks found) le
  | case3 node block found above parentFound =>
    rw [getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [found, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case4 node block found above parent parentFound lower ih =>
    rw [getAncestor_step found above parentFound lower] at walk
    rw [getAncestor_step (blocks found) above (blocks parentFound) lower]
    exact ih walk
  | case5 node block found above parent parentFound notLower =>
    rw [getAncestor] at walk
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

/-- A checkpoint block stays the same in a store that keeps every block of this one. -/
theorem getCheckpointBlock_of_blocks {after : Store preset fork} {root checkpoint : Root}
    {epoch : Epoch}
    (blocks : ∀ {root : Root} {block : BeaconBlock preset fork},
      store.blocks[root]? = some block → after.blocks[root]? = some block)
    (found : store.getCheckpointBlock root epoch = .ok checkpoint) :
    after.getCheckpointBlock root epoch = .ok checkpoint := by
  simp only [getCheckpointBlock, bind, Except.bind] at found ⊢
  split at found
  · simp at found
  · rename_i start _
    split at found
    · simp at found
    · rename_i ancestor walk
      rw [getAncestor_of_blocks blocks walk]
      exact found

/-- A node descends from its ancestor at any slot.

This is the ancestry used by the empty-slot discount of arXiv 2405.00549v4, Definition 5. -/
theorem isAncestor_of_getAncestor {node ancestor : ForkChoiceNode} {slot : Slot}
    (walk : store.getAncestor node slot = .ok ancestor) :
    store.isAncestor node ancestor = .ok true := by
  obtain ⟨block, found, le⟩ := getAncestor_le walk
  have stops : store.getAncestor node block.slot = .ok ancestor := by
    rw [getAncestor_trans le walk, getAncestor_of_le found (UInt64.le_refl _)]
  by_cases gloas : .glamsterdam ≤ fork <;>
    simp [isAncestor, block_ok_iff.mpr found, stops, gloas, bind, Except.bind, pure, Except.pure]

/-- Every known node descends from itself. -/
theorem isAncestor_self {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block) :
    store.isAncestor node node = .ok true :=
  isAncestor_of_getAncestor (getAncestor_of_le found (UInt64.le_refl _))

/-- A node that descends from a known node is a known block, at the slot of that node or later. -/
theorem slot_le_of_isAncestor {node ancestor : ForkChoiceNode} {block : BeaconBlock preset fork}
    (found : store.blocks[ancestor.root]? = some block)
    (descends : store.isAncestor node ancestor = .ok true) :
    ∃ nodeBlock, store.blocks[node.root]? = some nodeBlock ∧ block.slot ≤ nodeBlock.slot := by
  have known : store.block ancestor.root = .ok block := block_ok_iff.mpr found
  simp only [isAncestor, known, bind, Except.bind] at descends
  cases walk : store.getAncestor node block.slot with
  | error e => simp [walk] at descends
  | ok r =>
    rw [walk] at descends
    obtain ⟨nodeBlock, nodeFound⟩ : ∃ nodeBlock, store.blocks[node.root]? = some nodeBlock := by
      rw [getAncestor] at walk
      split at walk
      · simp [throw, throwThe, MonadExceptOf.throw] at walk
      · rename_i b same
        exact ⟨b, same⟩
    refine ⟨nodeBlock, nodeFound, ?_⟩
    by_cases le : nodeBlock.slot ≤ block.slot
    · rw [getAncestor_of_le nodeFound le] at walk
      cases walk
      have sameRoot : node.root = ancestor.root := by
        by_cases gloas : .glamsterdam ≤ fork <;>
          simp_all [pure, Except.pure]
      rw [sameRoot, found] at nodeFound
      cases nodeFound
      exact UInt64.le_refl _
    · exact UInt64.le_of_lt (UInt64.not_le.mp le)

/-- From Gloas a node descends from a pending node when its walk reaches the same root.

The payload status of the node that the walk reaches does not matter then. -/
theorem isAncestor_pending (gloas : .glamsterdam ≤ fork) (node : ForkChoiceNode) (root : Root) :
    store.isAncestor node ⟨root, .pending⟩ = (do
      let ancestorBlock ← store.block root
      return (← store.getAncestor node ancestorBlock.slot).root == root) := by
  simp only [isAncestor, gloas, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  split
  · rfl
  · split <;> simp

/-- Each node of a block descends from the pending node of the parent of that block.

The store must hold the parent, at an earlier slot than the block.

This is the pending ancestry used by arXiv 2405.00549v4, Definition 5. -/
theorem isAncestor_pending_parent_of_slot_lt {node : ForkChoiceNode}
    {block parent : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot) :
    store.isAncestor node ⟨block.parentRoot, .pending⟩ = .ok true := by
  have walk := getAncestor_parent_of_slot_lt found parentFound lower
  have descends := isAncestor_of_getAncestor walk
  by_cases gloas : .glamsterdam ≤ fork
  · simp [isAncestor_pending gloas, block_ok_iff.mpr parentFound, walk, bind, Except.bind,
      pure, Except.pure]
  · simpa only [parentPayloadStatus_of_lt (Nat.lt_of_not_le gloas)] using descends

end Store

/-- A new store holds its anchor block and state.

Each of its checkpoints, realized or not, is the anchor block at the anchor's epoch. -/
theorem getForkchoiceStore_anchor {config : Config} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) :
    ∃ anchorRoot, SszType.hashTreeRoot anchorBlock = .ok anchorRoot ∧
      store.blocks[anchorRoot]? = some anchorBlock ∧
      store.blockStates[anchorRoot]? = some anchorState ∧
      store.justifiedCheckpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩ ∧
      store.finalizedCheckpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩ ∧
      store.unrealizedJustifiedCheckpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩ ∧
      store.unrealizedFinalizedCheckpoint = ⟨getCurrentEpoch anchorState, anchorRoot⟩ := by
  unfold getForkchoiceStore at made
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
          exact ⟨anchorRoot, rfl, by simp, by simp, rfl, rfl, rfl, rfl⟩

/-- A new store knows only its anchor block, and only the anchor state. -/
theorem getForkchoiceStore_maps {config : Config} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) :
    ∃ anchorRoot, SszType.hashTreeRoot anchorBlock = .ok anchorRoot ∧
      store.blocks =
        (∅ : Std.TreeMap Root (BeaconBlock preset fork)).insert anchorRoot anchorBlock ∧
      store.blockStates =
        (∅ : Std.TreeMap Root (BeaconState preset fork)).insert anchorRoot anchorState := by
  unfold getForkchoiceStore at made
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
          exact ⟨anchorRoot, rfl, rfl, rfl⟩

/-- A new store holds the anchor state for the checkpoint of the anchor, and no other state. -/
theorem getForkchoiceStore_checkpointStates {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) :
    ∃ anchorRoot, SszType.hashTreeRoot anchorBlock = .ok anchorRoot ∧
      store.checkpointStates =
        (∅ : Std.TreeMap Checkpoint (BeaconState preset fork) Checkpoint.compare).insert
          ⟨getCurrentEpoch anchorState, anchorRoot⟩ anchorState := by
  unfold getForkchoiceStore at made
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
          exact ⟨anchorRoot, rfl, rfl⟩

/-- The genesis time of a new store is that of the anchor state, in milliseconds.

Its clock is at the start of the slot of the anchor state. -/
theorem getForkchoiceStore_timeMs {config : Config} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) :
    store.genesisTimeMs = secondsToMilliseconds anchorState.genesisTime ∧
      computeTimeAtSlotMs config store.genesisTimeMs anchorState.slot = .ok store.timeMs := by
  unfold getForkchoiceStore at made
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
          exact ⟨rfl, time⟩

/-- A new store holds no vote, and holds the timeliness of its anchor from Gloas only.

From Gloas the anchor is timely for the attestation deadline and for the committee deadline.

It has no verified payload, and each member of the payload committee has no vote on it yet. -/
theorem getForkchoiceStore_fields {config : Config} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) :
    ∃ anchorRoot, SszType.hashTreeRoot anchorBlock = .ok anchorRoot ∧
      store.latestMessages = ∅ ∧
      store.blockTimeliness =
        (if .glamsterdam ≤ fork then (∅ : Std.TreeMap Root Bool).insert anchorRoot true else ∅) ∧
      ∀ gloas : .glamsterdam ≤ fork,
        store.ptcTimeliness gloas = (∅ : Std.TreeMap Root Bool).insert anchorRoot true ∧
        store.payloads gloas = ∅ ∧
        store.payloadTimelinessVote gloas = (∅ : Std.TreeMap Root _).insert anchorRoot
          (Vector.replicate preset.PTC_SIZE.toNat none) ∧
        store.payloadDataAvailabilityVote gloas = (∅ : Std.TreeMap Root _).insert anchorRoot
          (Vector.replicate preset.PTC_SIZE.toNat none) := by
  unfold getForkchoiceStore at made
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
          exact ⟨anchorRoot, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- A new store fails when the anchor block does not commit to the anchor state. -/
theorem getForkchoiceStore_mismatch {config : Config} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {stateRoot : Root}
    (root : SszType.hashTreeRoot anchorState = .ok stateRoot)
    (differ : anchorBlock.stateRoot ≠ stateRoot) :
    getForkchoiceStore config anchorState anchorBlock = .error .anchorStateMismatch := by
  simp [getForkchoiceStore, root, differ, Except.mapError, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw]

/-- The clock of a new store is at the slot of the anchor state, on a chain with nonempty slots. -/
theorem getCurrentSlot_getForkchoiceStore {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork} (positive : 0 < config.SLOT_DURATION_MS)
    (made : getForkchoiceStore config anchorState anchorBlock = .ok store) :
    store.getCurrentSlot config = .ok anchorState.slot := by
  unfold getForkchoiceStore at made
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
