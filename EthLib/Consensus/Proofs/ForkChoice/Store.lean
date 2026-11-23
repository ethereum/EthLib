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

Each node of a block descends from the pending node of its parent at an earlier slot.

The walk to a lower slot can stop at a higher slot on the way, and go on from there.

From Gloas the walk gives each parent an empty or full status.

It reaches the same blocks whatever the status of its start.

So at every fork, a checkpoint read goes through the checkpoint the root reads at a later epoch.
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

The store must hold the block and its parent, the parent at an earlier slot.

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

/-- From a known block above the slot, the walk does not depend on the start's payload status. -/
private theorem getAncestor_status_of_gt {root : Root} {slot : Slot}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (above : ¬ block.slot ≤ slot) (status other : PayloadStatus) :
    store.getAncestor ⟨root, status⟩ slot = store.getAncestor ⟨root, other⟩ slot := by
  conv => lhs; rw [getAncestor]
  conv => rhs; rw [getAncestor]
  repeat' split
  all_goals simp_all [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le]
  all_goals omega

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

private theorem getAncestor_transfer {receiver : Store preset fork}
    {node ancestor : ForkChoiceNode} {slot : Slot}
    (same : ∀ (r : Root) b c, store.blocks[r]? = some b → receiver.blocks[r]? = some c → b = c)
    (fromTip : Prop) [Decidable fromTip]
    (base : ¬fromTip → ∃ b, receiver.blocks[ancestor.root]? = some b)
    (parents : fromTip → ∀ (r : Root) (b p : BeaconBlock preset fork),
      store.blocks[r]? = some b → store.blocks[b.parentRoot]? = some p → slot < b.slot →
      receiver.blocks[r]? = some b → receiver.blocks[b.parentRoot]? = some p)
    (admission : ¬fromTip → ∀ (r : Root) (b p : BeaconBlock preset fork),
      store.blocks[r]? = some b → store.blocks[b.parentRoot]? = some p →
      slot < b.slot → p.slot < b.slot → receiver.blocks[b.parentRoot]? = some p →
      receiver.getAncestor ⟨b.parentRoot, parentPayloadStatus b p⟩ slot = .ok ancestor →
      receiver.blocks[r]? = some b)
    (walk : store.getAncestor node slot = .ok ancestor)
    (tip : fromTip → ∃ b, receiver.blocks[node.root]? = some b) :
    (∃ b, store.blocks[node.root]? = some b ∧ receiver.blocks[node.root]? = some b) ∧
      ∀ target, slot ≤ target →
        receiver.getAncestor node target = store.getAncestor node target := by
  induction node using getAncestor.induct (store := store) (slot := slot) with
  | case1 node found =>
    rw [getAncestor] at walk
    split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case2 node block found le =>
    rw [getAncestor_of_le found le] at walk
    cases walk
    obtain ⟨other, known⟩ := if h : fromTip then tip h else base h
    have eq := same _ block other found known
    subst other
    refine ⟨⟨block, found, known⟩, ?_⟩
    intro target higher
    rw [getAncestor_of_le found (UInt64.le_trans le higher),
      getAncestor_of_le known (UInt64.le_trans le higher)]
  | case3 node block found above parentFound =>
    rw [getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b eq
      rw [found, Option.some.injEq] at eq
      subst eq
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case4 node block found above parent parentFound lower ih =>
    rw [getAncestor_step found above parentFound lower] at walk
    have held : fromTip → receiver.blocks[node.root]? = some block := by
      intro h
      obtain ⟨b, known⟩ := tip h
      exact (same _ block b found known).symm ▸ known
    obtain ⟨⟨p, pf, pk⟩, agree⟩ := ih walk (fun h =>
      ⟨parent, parents h _ _ _ found parentFound (UInt64.not_le.mp above) (held h)⟩)
    have eq := Option.some.inj (parentFound.symm.trans pf)
    subst p
    have parentWalk : receiver.getAncestor
        ⟨block.parentRoot, parentPayloadStatus block parent⟩ slot = .ok ancestor := by
      rw [agree slot (UInt64.le_refl _), walk]
    have known := if h : fromTip then held h else
      admission h node.root block parent found parentFound
        (UInt64.not_le.mp above) lower pk parentWalk
    refine ⟨⟨block, found, known⟩, ?_⟩
    intro target higher
    by_cases le : block.slot ≤ target
    · rw [getAncestor_of_le found le, getAncestor_of_le known le]
    · rw [getAncestor_step found le parentFound lower,
        getAncestor_step known le pk lower, agree target higher]
  | case5 node block found above parent parentFound notLower =>
    rw [getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b eq
      rw [found, Option.some.injEq] at eq
      subst eq
      simp only [above, ↓reduceIte] at walk
      split at walk
      · simp_all
      · rename_i p eq
        rw [parentFound, Option.some.injEq] at eq
        subst eq
        simp [notLower, throw, throwThe, MonadExceptOf.throw] at walk

/-- Admission above a held ancestor reproduces its walk and every higher walk. -/
theorem getAncestor_of_admission {receiver : Store preset fork}
    {node ancestor : ForkChoiceNode} {slot : Slot}
    (same : ∀ (r : Root) b c, store.blocks[r]? = some b → receiver.blocks[r]? = some c → b = c)
    (base : ∃ b, receiver.blocks[ancestor.root]? = some b)
    (admission : ∀ (r : Root) (b p : BeaconBlock preset fork),
      store.blocks[r]? = some b → store.blocks[b.parentRoot]? = some p →
      slot < b.slot → p.slot < b.slot → receiver.blocks[b.parentRoot]? = some p →
      receiver.getAncestor ⟨b.parentRoot, parentPayloadStatus b p⟩ slot = .ok ancestor →
      receiver.blocks[r]? = some b)
    (walk : store.getAncestor node slot = .ok ancestor) :
    (∃ b, store.blocks[node.root]? = some b ∧ receiver.blocks[node.root]? = some b) ∧
      ∀ target, slot ≤ target →
        receiver.getAncestor node target = store.getAncestor node target :=
  getAncestor_transfer same False (fun _ => base) (fun h => h.elim) (fun _ => admission) walk
    (fun h => h.elim)

/-- Stores that agree on blocks reproduce a walk when the receiver holds its parent chain. -/
theorem getAncestor_of_parent_chain {receiver : Store preset fork}
    {node ancestor : ForkChoiceNode} {slot : Slot}
    (same : ∀ (r : Root) b c, store.blocks[r]? = some b → receiver.blocks[r]? = some c → b = c)
    (parents : ∀ (r : Root) (b p : BeaconBlock preset fork),
      store.blocks[r]? = some b → store.blocks[b.parentRoot]? = some p → slot < b.slot →
      receiver.blocks[r]? = some b → receiver.blocks[b.parentRoot]? = some p)
    (known : ∃ b, receiver.blocks[node.root]? = some b)
    (walk : store.getAncestor node slot = .ok ancestor) :
    receiver.getAncestor node slot = .ok ancestor := by
  have transferred := getAncestor_transfer same True (fun h => (h trivial).elim)
    (fun _ => parents) (fun h => (h trivial).elim) walk (fun _ => known)
  exact ((transferred.2 slot (UInt64.le_refl _)).trans walk)

/-- A walk keeps its result in a store that keeps every block of this one. -/
theorem getAncestor_of_blocks {after : Store preset fork} {node ancestor : ForkChoiceNode}
    {slot : Slot}
    (blocks : ∀ {root : Root} {block : BeaconBlock preset fork},
      store.blocks[root]? = some block → after.blocks[root]? = some block)
    (walk : store.getAncestor node slot = .ok ancestor) :
    after.getAncestor node slot = .ok ancestor := by
  obtain ⟨block, known, -⟩ := getAncestor_le walk
  have agrees : ∀ (r : Root) b c, store.blocks[r]? = some b →
      after.blocks[r]? = some c → b = c := by
    intro r b c found held
    exact Option.some.inj ((blocks found).symm.trans held)
  rw [(getAncestor_of_admission agrees ⟨block, blocks known⟩
    (fun _ _ _ found _ _ _ _ _ => blocks found) walk).2 slot (UInt64.le_refl _)]
  exact walk

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

/-- From Gloas the payload status of the head does not change whether a block is in its chain.

So a head given by its root, as a pending node, answers as the head that the fork choice finds. -/
theorem isAncestor_head_pending (gloas : .glamsterdam ≤ fork) (head : ForkChoiceNode)
    (root : Root) :
    store.isAncestor head ⟨root, .pending⟩ =
      store.isAncestor ⟨head.root, .pending⟩ ⟨root, .pending⟩ := by
  rw [isAncestor_pending gloas, isAncestor_pending gloas]
  simp only [bind, Except.bind]
  split
  · rfl
  · rename_i ancestorBlock _
    have same := getAncestor_root (store := store) head .pending ancestorBlock.slot
    revert same
    cases store.getAncestor head ancestorBlock.slot <;>
      cases store.getAncestor ⟨head.root, .pending⟩ ancestorBlock.slot <;>
      simp_all [Functor.map, Except.map, pure, Except.pure]

/-- Each node of a block descends from the pending node of the parent of that block.

The store must hold the block and its parent, the parent at an earlier slot.

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

/-- A node that descends from a known pending node walks back to its root.

The walk stops at the slot of the block of that root. -/
theorem getAncestor_of_isAncestor {node : ForkChoiceNode} {root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (descends : store.isAncestor node ⟨root, .pending⟩ = .ok true) :
    ∃ reached, store.getAncestor node block.slot = .ok reached ∧ reached.root = root := by
  simp only [isAncestor, block_ok_iff.mpr found, bind, Except.bind] at descends
  cases walk : store.getAncestor node block.slot with
  | error e => simp [walk] at descends
  | ok reached =>
    refine ⟨reached, rfl, ?_⟩
    rw [walk] at descends
    by_cases gloas : .glamsterdam ≤ fork <;> simp_all [pure, Except.pure]

/-- Before Gloas, an ancestor test is the exact walk to the ancestor's slot. -/
theorem getAncestor_of_isAncestor_of_lt {node ancestor : ForkChoiceNode}
    {block : BeaconBlock preset fork} (before : fork < .glamsterdam)
    (known : store.blocks[ancestor.root]? = some block)
    (descends : store.isAncestor node ancestor = .ok true) :
    store.getAncestor node block.slot = .ok ancestor := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [isAncestor, block_ok_iff.mpr known, notGloas, ↓reduceIte,
    bind, Except.bind] at descends
  cases walk : store.getAncestor node block.slot with
  | error error => simp [walk] at descends
  | ok found =>
    simp only [walk, pure, Except.pure, Except.ok.injEq, beq_iff_eq] at descends
    exact congrArg Except.ok descends

/-- Descent composes through a known intermediate block. -/
theorem isAncestor_trans {node middle ancestor : ForkChoiceNode}
    {middleBlock ancestorBlock : BeaconBlock preset fork}
    (middleKnown : store.blocks[middle.root]? = some middleBlock)
    (ancestorKnown : store.blocks[ancestor.root]? = some ancestorBlock)
    (upper : store.isAncestor node middle = .ok true)
    (lower : store.isAncestor middle ancestor = .ok true) :
    store.isAncestor node ancestor = .ok true := by
  obtain ⟨block, found, le⟩ := slot_le_of_isAncestor ancestorKnown lower
  rw [middleKnown, Option.some.injEq] at found
  subst block
  simp only [isAncestor, block_ok_iff.mpr middleKnown, block_ok_iff.mpr ancestorKnown, bind,
    Except.bind] at upper lower ⊢
  cases upperWalk : store.getAncestor node middleBlock.slot with
  | error e => simp [upperWalk] at upper
  | ok reached =>
  cases lowerWalk : store.getAncestor middle ancestorBlock.slot with
  | error e => simp [lowerWalk] at lower
  | ok below =>
  rw [upperWalk] at upper
  rw [lowerWalk] at lower
  rw [getAncestor_trans le upperWalk]
  -- The node reaches the middle block with some status; below its slot the status is forgotten.
  have rooted : reached.root = middle.root := by
    by_cases gloas : .glamsterdam ≤ fork <;> simp_all [pure, Except.pure]
  by_cases strict : middleBlock.slot ≤ ancestorBlock.slot
  · have same : ancestorBlock.slot = middleBlock.slot := UInt64.le_antisymm le strict
    rw [getAncestor_of_le (rooted ▸ middleKnown) (same ▸ UInt64.le_refl _)]
    rw [getAncestor_of_le middleKnown (same ▸ UInt64.le_refl _), Except.ok.injEq] at lowerWalk
    subst lowerWalk
    obtain ⟨r, s⟩ := reached
    obtain ⟨m, t⟩ := middle
    obtain ⟨a, u⟩ := ancestor
    by_cases gloas : .glamsterdam ≤ fork <;> cases s <;> cases t <;> cases u <;>
      simp_all [pure, Except.pure]
  · have walks := getAncestor_status_of_gt (store := store) (rooted ▸ middleKnown) strict
      reached.payloadStatus middle.payloadStatus
    obtain ⟨r, s⟩ := reached
    simp only at rooted walks
    subst rooted
    rw [walks, lowerWalk]
    exact lower

/-- Descent carries an ancestor's checkpoint read to a descendant above that boundary. -/
theorem getCheckpointBlock_of_isAncestor {node : ForkChoiceNode} {root checkpoint : Root}
    {block : BeaconBlock preset fork} {epoch : Epoch} {boundary : Slot}
    (known : store.blocks[root]? = some block)
    (descends : store.isAncestor node ⟨root, .pending⟩ = .ok true)
    (boundaryOk : computeStartSlotAtEpoch preset epoch = .ok boundary)
    (earlier : boundary ≤ block.slot)
    (read : store.getCheckpointBlock root epoch = .ok checkpoint) :
    store.getCheckpointBlock node.root epoch = .ok checkpoint := by
  obtain ⟨reached, walk, rooted⟩ := getAncestor_of_isAncestor known descends
  have through := getAncestor_trans earlier walk
  have rootWalk := getAncestor_root (store := store) node .pending boundary
  have reachedWalk := getAncestor_root (store := store) reached .pending boundary
  rw [rooted] at reachedWalk
  simp only [getCheckpointBlock, boundaryOk, Except.mapError, bind, Except.bind] at read ⊢
  change ((fun x => x.root) <$> store.getAncestor ⟨node.root, .pending⟩ boundary) =
    .ok checkpoint
  rw [← rootWalk, through, reachedWalk]
  exact read

/-- Before Gloas, an ancestor walk from a pending node returns a pending node. -/
theorem getAncestor_pending_of_lt {boundary : Slot} (before : fork < .glamsterdam)
    {node reached : ForkChoiceNode} (status : node.payloadStatus = .pending)
      (walk : store.getAncestor node boundary = .ok reached) :
      reached.payloadStatus = .pending := by
    induction node using getAncestor.induct (store := store) (slot := boundary) with
    | case1 node found =>
      rw [getAncestor] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
    | case2 node block found below =>
      rw [getAncestor_of_le found below] at walk
      cases walk
      exact status
    | case3 node block found above missing =>
      rw [getAncestor] at walk
      split at walk
      · simp_all
      · rename_i b eq
        rw [found, Option.some.injEq] at eq
        subst eq
        simp only [above, ↓reduceIte] at walk
        split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
    | case4 node block found above parent parentFound lower ih =>
      rw [getAncestor_step found above parentFound lower] at walk
      exact ih (parentPayloadStatus_of_lt before) walk
    | case5 node block found above parent parentFound bad =>
      rw [getAncestor] at walk
      split at walk
      · simp_all
      · rename_i b eq
        rw [found, Option.some.injEq] at eq
        subst eq
        simp only [above, ↓reduceIte] at walk
        split at walk
        · simp_all
        · rename_i p eq
          rw [parentFound, Option.some.injEq] at eq
          subst eq
          simp [bad, throw, throwThe, MonadExceptOf.throw] at walk
/-- Before Gloas, a checkpoint read walks from the root to the checkpoint at the epoch's start. -/
theorem getCheckpointBlock_walk {root checkpoint : Root} {epoch : Epoch}
    (before : fork < .glamsterdam)
    (read : store.getCheckpointBlock root epoch = .ok checkpoint) :
    ∃ boundary, computeStartSlotAtEpoch preset epoch = .ok boundary ∧
      store.getAncestor ⟨root, .pending⟩ boundary = .ok ⟨checkpoint, .pending⟩ := by
  unfold getCheckpointBlock at read
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
  obtain ⟨boundary, boundaryOk, ancestor, walk, rootEq⟩ := read
  have status := getAncestor_pending_of_lt before rfl walk
  have same : ancestor = ⟨checkpoint, .pending⟩ := by
    cases ancestor
    simp_all
  subst ancestor
  exact ⟨boundary, mapError_ok_iff.mp boundaryOk, walk⟩

/-- A checkpoint read is the root of a walk back to the first slot of the epoch, at every fork. -/
theorem getCheckpointBlock_walk_root {root checkpoint : Root} {epoch : Epoch}
    (read : store.getCheckpointBlock root epoch = .ok checkpoint) :
    ∃ start ancestor, computeStartSlotAtEpoch preset epoch = .ok start ∧
      store.getAncestor ⟨root, .pending⟩ start = .ok ancestor ∧ ancestor.root = checkpoint := by
  unfold getCheckpointBlock at read
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
  obtain ⟨start, startOk, ancestor, walk, eq⟩ := read
  exact ⟨start, ancestor, mapError_ok_iff.mp startOk, walk, eq⟩

/-- An ancestor of a tip reads the tip's checkpoint block at an epoch.

That epoch's first slot must be at or before the ancestor. -/
theorem getCheckpointBlock_of_descendant {tip below checkpoint : Root}
    {belowBlock : BeaconBlock preset fork} {epoch : Epoch} {start : Slot}
    (belowFound : store.blocks[below]? = some belowBlock)
    (descends : store.isAncestor ⟨tip, .pending⟩ ⟨below, .pending⟩ = .ok true)
    (startOk : computeStartSlotAtEpoch preset epoch = .ok start)
    (within : start ≤ belowBlock.slot)
    (read : store.getCheckpointBlock tip epoch = .ok checkpoint) :
    store.getCheckpointBlock below epoch = .ok checkpoint := by
  obtain ⟨start', ancestor, startOk', walk, rooted⟩ := getCheckpointBlock_walk_root read
  rw [startOk, Except.ok.injEq] at startOk'
  subst start'
  -- The walk to the block's slot reaches its root; below that the walks agree on roots.
  obtain ⟨reached, toBelow, reachedRoot⟩ := getAncestor_of_isAncestor belowFound descends
  rw [getAncestor_trans within toBelow] at walk
  have reachedWalk := getAncestor_root (store := store) reached .pending start
  rw [reachedRoot, walk] at reachedWalk
  simp only [getCheckpointBlock, startOk, Except.mapError, bind, Except.bind]
  change ((fun x => x.root) <$> store.getAncestor ⟨below, .pending⟩ start) = .ok checkpoint
  rw [← reachedWalk]
  simp [rooted, Functor.map, Except.map]

/-- A successful checkpoint read names a held ancestor at or before its epoch boundary. -/
theorem isAncestor_of_getCheckpointBlock {root checkpoint : Root} {epoch : Epoch}
    (read : store.getCheckpointBlock root epoch = .ok checkpoint) :
    ∃ boundary block, computeStartSlotAtEpoch preset epoch = .ok boundary ∧
      store.blocks[checkpoint]? = some block ∧ block.slot ≤ boundary ∧
      store.isAncestor ⟨root, .pending⟩ ⟨checkpoint, .pending⟩ = .ok true := by
  by_cases gloas : .glamsterdam ≤ fork
  · -- From Gloas the walk reaches the checkpoint block, and a pending ancestor accepts any status.
    obtain ⟨boundary, ancestor, boundaryOk, walk, rfl⟩ := getCheckpointBlock_walk_root read
    obtain ⟨block, held, le⟩ := getAncestor_le walk
    have stops : store.getAncestor ⟨root, .pending⟩ block.slot = .ok ancestor := by
      rw [getAncestor_trans le walk, getAncestor_of_le held (UInt64.le_refl _)]
    exact ⟨boundary, block, boundaryOk, held, le, by
      simp [isAncestor_pending gloas, block_ok_iff.mpr held, stops, bind, Except.bind, pure,
        Except.pure]⟩
  obtain ⟨boundary, boundaryOk, walk⟩ := getCheckpointBlock_walk (Nat.lt_of_not_le gloas) read
  obtain ⟨block, held, le⟩ := getAncestor_le walk
  exact ⟨boundary, block, boundaryOk, held, le, isAncestor_of_getAncestor walk⟩

/-- A checkpoint read at an epoch goes through the checkpoint at any later epoch.

The read of the root at the later epoch names the block that the earlier read starts from. -/
theorem getCheckpointBlock_trans {root through : Root} {high low : Epoch}
    (read : store.getCheckpointBlock root high = .ok through) (le : low ≤ high) :
    store.getCheckpointBlock root low = store.getCheckpointBlock through low := by
  unfold getCheckpointBlock at read
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at read
  obtain ⟨boundary, boundaryOk, walkedNode, walked, rfl⟩ := read
  have boundaryOk := mapError_ok_iff.mp boundaryOk
  have boundaryNat := computeStartSlotAtEpoch_ok_iff.mp boundaryOk
  obtain ⟨lowSlot, lowOk⟩ : ∃ s, computeStartSlotAtEpoch preset low = .ok s := by
    refine ⟨low * preset.SLOTS_PER_EPOCH, computeStartSlotAtEpoch_ok_iff.mpr ⟨?_, ?_⟩⟩
    · have := UInt64.le_iff_toNat_le.mp le
      have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat this
      omega
    · rw [UInt64.toNat_mul, Nat.mod_eq_of_lt]
      have := UInt64.le_iff_toNat_le.mp le
      have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat this
      omega
  have below : lowSlot ≤ boundary := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [(computeStartSlotAtEpoch_ok_iff.mp lowOk).2, boundaryNat.2]
    exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp le)
  -- The walk at the lower slot goes through the node reached, whatever its payload status.
  have through' := getAncestor_trans below walked
  have rootWalk := getAncestor_root (store := store) walkedNode .pending lowSlot
  simp only [getCheckpointBlock, lowOk, Except.mapError, bind, Except.bind]
  change (·.root) <$> store.getAncestor ⟨root, .pending⟩ lowSlot =
    (·.root) <$> store.getAncestor ⟨walkedNode.root, .pending⟩ lowSlot
  rw [through', rootWalk]

/-- A checkpoint read at an ancestor holds at each descendant.

The ancestor is in the checkpoint's epoch or a later one. -/
theorem getCheckpointBlock_of_ancestor_epoch {root above checkpoint : Root}
    {aboveBlock : BeaconBlock preset fork}
    (aboveFound : store.blocks[above]? = some aboveBlock)
    (descends : store.isAncestor ⟨root, .pending⟩ ⟨above, .pending⟩ = .ok true) {epoch : Epoch}
    (le : epoch.toNat ≤ (computeEpochAtSlot preset aboveBlock.slot).toNat)
    (read : store.getCheckpointBlock above epoch = .ok checkpoint) :
    store.getCheckpointBlock root epoch = .ok checkpoint := by
  obtain ⟨boundary, -, boundaryOk, -, -, -⟩ := isAncestor_of_getCheckpointBlock read
  exact getCheckpointBlock_of_isAncestor aboveFound descends boundaryOk
    (computeStartSlotAtEpoch_le_of_epoch_le boundaryOk le) read

/-- A checkpoint read names a held block in the checkpoint's epoch or before.

That block reads itself as the checkpoint block of the epoch. -/
theorem getCheckpointBlock_self
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) {root checkpoint : Root} {epoch : Epoch}
    (read : store.getCheckpointBlock root epoch = .ok checkpoint) :
    ∃ block : BeaconBlock preset fork, store.blocks[checkpoint]? = some block ∧
      (computeEpochAtSlot preset block.slot).toNat ≤ epoch.toNat ∧
      store.getCheckpointBlock checkpoint epoch = .ok checkpoint := by
  obtain ⟨boundary, block, boundaryOk, found, le, -⟩ := isAncestor_of_getCheckpointBlock read
  have epochEq := computeEpochAtSlot_computeStartSlotAtEpoch
    (UInt64.lt_iff_toNat_lt.mpr positive) boundaryOk
  refine ⟨block, found, ?_, ?_⟩
  · rw [← epochEq]
    exact epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp le)
  · rw [← getCheckpointBlock_trans read (UInt64.le_refl _)]
    exact read

/-- The store's epoch is the epoch of its slot. -/
theorem getCurrentStoreEpoch_eq {config : Config} {slot : Slot} {epoch : Epoch}
    (slotOk : store.getCurrentSlot config = .ok slot)
    (epochOk : store.getCurrentStoreEpoch config = .ok epoch) :
    epoch = computeEpochAtSlot preset slot := by
  simpa [getCurrentStoreEpoch, slotOk, bind, Except.bind, pure, Except.pure]
    using epochOk.symm

/-- A walk from a node reaches, from the pending node of its root, a node with the same root. -/
theorem getAncestor_pending_root {node ancestor : ForkChoiceNode} {slot : Slot}
    (walk : store.getAncestor node slot = .ok ancestor) :
    ∃ reached, store.getAncestor ⟨node.root, .pending⟩ slot = .ok reached ∧
      reached.root = ancestor.root := by
  have same := getAncestor_root (store := store) node .pending slot
  rw [walk] at same
  cases pendingWalk : store.getAncestor ⟨node.root, .pending⟩ slot with
  | error e => simp [pendingWalk, Functor.map, Except.map] at same
  | ok reached =>
    simp only [pendingWalk, Functor.map, Except.map, Except.ok.injEq] at same
    exact ⟨reached, rfl, same.symm⟩

/-- A pending walk that reaches a known root at its slot is a descent to its pending node. -/
theorem isAncestor_of_getAncestor_root {root : Root} {node reached : ForkChoiceNode}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (pending : node.payloadStatus = .pending)
    (walk : store.getAncestor node block.slot = .ok reached) (rootEq : reached.root = root) :
    store.isAncestor node ⟨root, .pending⟩ = .ok true := by
  by_cases gloas : .glamsterdam ≤ fork
  · simp [isAncestor_pending gloas, block_ok_iff.mpr found, walk, rootEq, bind, Except.bind,
      pure, Except.pure]
  have status := getAncestor_pending_of_lt (Nat.lt_of_not_le gloas) pending walk
  have same : reached = ⟨root, .pending⟩ := by
    cases reached
    simp_all
  exact same ▸ isAncestor_of_getAncestor walk

/-- A checkpoint read on a head above a block is above the block.

The block must be at or before the first slot of the checkpoint's epoch. -/
theorem isAncestor_of_getCheckpointBlock_above
    {head root checkpoint : Root} {rootBlock : BeaconBlock preset fork} {epoch : Epoch}
    (rootKnown : store.blocks[root]? = some rootBlock)
    (supports : store.isAncestor ⟨head, .pending⟩ ⟨root, .pending⟩ = .ok true)
    (read : store.getCheckpointBlock head epoch = .ok checkpoint)
    (blockLe : rootBlock.slot.toNat ≤ epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    store.isAncestor ⟨checkpoint, .pending⟩ ⟨root, .pending⟩ = .ok true := by
  obtain ⟨boundary, ancestor, boundaryOk, boundaryWalk, rooted⟩ :=
    getCheckpointBlock_walk_root read
  have blockBelow : rootBlock.slot ≤ boundary := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [(computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2]
    exact blockLe
  -- The head's walk to the block passes the checkpoint's node, whatever its payload status.
  obtain ⟨reached, headWalk, reachedRoot⟩ := getAncestor_of_isAncestor rootKnown supports
  have through := getAncestor_trans blockBelow boundaryWalk
  rw [headWalk] at through
  obtain ⟨pendingReached, pendingWalk, pendingRoot⟩ := getAncestor_pending_root through.symm
  rw [rooted] at pendingWalk
  exact isAncestor_of_getAncestor_root rootKnown rfl pendingWalk (pendingRoot.trans reachedRoot)

/-- The root of the ancestor of a successful descent test is held. -/
theorem held_of_isAncestor {node ancestor : ForkChoiceNode}
    (descends : store.isAncestor node ancestor = .ok true) :
    ∃ block, store.blocks[ancestor.root]? = some block := by
  unfold isAncestor at descends
  obtain ⟨b, ok, -⟩ := bind_ok_iff.mp descends
  exact ⟨b, block_ok_iff.mp ok⟩

/-- Two pending ancestors of one head are comparable. -/
theorem comparable_of_ancestors {head : ForkChoiceNode} {a b : Root}
    {aBlock bBlock : BeaconBlock preset fork}
    (aKnown : store.blocks[a]? = some aBlock) (bKnown : store.blocks[b]? = some bBlock)
    (ha : store.isAncestor head ⟨a, .pending⟩ = .ok true)
    (hb : store.isAncestor head ⟨b, .pending⟩ = .ok true) :
    store.isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true ∨
      store.isAncestor ⟨b, .pending⟩ ⟨a, .pending⟩ = .ok true := by
  obtain ⟨ra, aw, aRoot⟩ := getAncestor_of_isAncestor aKnown ha
  obtain ⟨rb, bw, bRoot⟩ := getAncestor_of_isAncestor bKnown hb
  rcases UInt64.le_total bBlock.slot aBlock.slot with le | le
  · left
    have walk := (getAncestor_trans le aw).symm.trans bw
    obtain ⟨reached, pendingWalk, reachedRoot⟩ := getAncestor_pending_root walk
    rw [aRoot] at pendingWalk
    exact isAncestor_of_getAncestor_root bKnown rfl pendingWalk (reachedRoot.trans bRoot)
  · right
    have walk := (getAncestor_trans le bw).symm.trans aw
    obtain ⟨reached, pendingWalk, reachedRoot⟩ := getAncestor_pending_root walk
    rw [bRoot] at pendingWalk
    exact isAncestor_of_getAncestor_root aKnown rfl pendingWalk (reachedRoot.trans aRoot)

/-- Two blocks above each other are the same block. -/
theorem eq_of_isAncestor_antisymm
    {a b : Root} {aBlock bBlock : BeaconBlock preset fork}
    (aFound : store.blocks[a]? = some aBlock) (bFound : store.blocks[b]? = some bBlock)
    (up : store.isAncestor ⟨a, .pending⟩ ⟨b, .pending⟩ = .ok true)
    (down : store.isAncestor ⟨b, .pending⟩ ⟨a, .pending⟩ = .ok true) : a = b := by
  obtain ⟨aBlock', aFound', le⟩ := slot_le_of_isAncestor bFound up
  rw [aFound, Option.some.injEq] at aFound'
  subst aBlock'
  obtain ⟨bBlock', bFound', ge⟩ := slot_le_of_isAncestor aFound down
  rw [bFound, Option.some.injEq] at bFound'
  subst bBlock'
  obtain ⟨reached, walk, rooted⟩ := getAncestor_of_isAncestor bFound up
  rw [getAncestor_of_le aFound ge, Except.ok.injEq] at walk
  rw [← rooted, ← walk]

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
    getForkchoiceStore config anchorState anchorBlock =
      .error (.anchorStateMismatch anchorBlock.stateRoot stateRoot) := by
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
