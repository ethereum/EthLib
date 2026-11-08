module

public import EthLib.Consensus.ForkChoice.Head
public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Proofs.ForkChoice.Store

/-!
# Proofs: the head of the fork choice

Before Gloas the children of a node are the known blocks whose parent is the node's block.

From Gloas a pending node has its empty node as a child, and its full node once it is verified.

From Gloas an empty or full node has the blocks that build on its payload status as children.

The choice among weighted children returns one of them, and none of them is above it.

A payload decision is the empty or the full node of a block from the previous slot.

Such a node weighs nothing.

Any other node weighs its votes in the justified state when the boost does not apply.

The boost applies after a parent older than the previous slot, and after a parent that is not weak.

The head has no child among the viable nodes, so the walk stops only at a leaf.

The head descends from the justified block, at every fork.

From Gloas the walk from any known node reaches a descendant of that node.

A viable node with children has a viable child, so from Gloas the head is never a pending node.

From Gloas, let a block of the previous slot have a verified payload and both its nodes viable.

The walk then takes the full node exactly when the payload extends.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

/-- The heavier of two weighted nodes is at least as large as the first. -/
theorem heavier_ge_left (a b : WeightedNode) :
    (compareWeighted (heavier a b) a).isGE := by
  unfold heavier
  split
  · rename_i lt
    rw [Std.OrientedCmp.eq_swap (cmp := compareWeighted), lt]
    rfl
  · rw [Std.ReflCmp.compare_self (cmp := compareWeighted)]
    rfl

/-- The heavier of two weighted nodes is at least as large as the second. -/
theorem heavier_ge_right (a b : WeightedNode) :
    (compareWeighted (heavier a b) b).isGE := by
  unfold heavier
  split
  · rw [Std.ReflCmp.compare_self (cmp := compareWeighted)]
    rfl
  · rename_i notLt
    revert notLt
    cases compareWeighted a b <;> simp

/-- The heavier of two weighted nodes is one of them. -/
theorem heavier_eq (a b : WeightedNode) : heavier a b = a ∨ heavier a b = b := by
  unfold heavier
  split <;> simp

/-- Folding the choice over a list returns an element of the list. -/
theorem foldl_heavier_mem (first : WeightedNode) (rest : List WeightedNode) :
    rest.foldl heavier first ∈ first :: rest := by
  induction rest generalizing first with
  | nil => simp
  | cons x rest ih =>
    rw [List.foldl_cons]
    have := ih (heavier first x)
    simp only [List.mem_cons] at this ⊢
    rcases heavier_eq first x with same | same <;> rw [same] at this ⊢
    · rcases this with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · rcases this with h | h
      · exact .inr (.inl h)
      · exact .inr (.inr h)

/-- No element of the list is above the result of the fold. -/
theorem foldl_heavier_ge (first : WeightedNode) (rest : List WeightedNode) :
    ∀ x ∈ first :: rest, (compareWeighted (rest.foldl heavier first) x).isGE := by
  induction rest generalizing first with
  | nil =>
    intro x mem
    rw [List.mem_singleton.mp mem, List.foldl_nil,
      Std.ReflCmp.compare_self (cmp := compareWeighted)]
    rfl
  | cons y rest ih =>
    intro x mem
    have step := ih (heavier first y)
    rw [List.foldl_cons]
    simp only [List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · exact Std.TransCmp.isGE_trans (step _ List.mem_cons_self) (heavier_ge_left _ _)
    · exact Std.TransCmp.isGE_trans (step _ List.mem_cons_self) (heavier_ge_right _ _)
    · exact step x (List.mem_cons_of_mem _ mem)

/-- The choice returns the node of an element of the list, and no element is above it. -/
theorem chooseHeaviest_some {weighted : List WeightedNode} {chosen : ForkChoiceNode}
    (found : chooseHeaviest weighted = some chosen) :
    ∃ key, (chosen, key) ∈ weighted ∧ ∀ x ∈ weighted, (compareWeighted (chosen, key) x).isGE := by
  cases weighted with
  | nil => cases found
  | cons first rest =>
    simp only [chooseHeaviest, Option.some.injEq] at found
    subst found
    exact ⟨_, foldl_heavier_mem first rest, foldl_heavier_ge first rest⟩

/-- The choice returns none only on the empty list. -/
theorem chooseHeaviest_eq_none {weighted : List WeightedNode} :
    chooseHeaviest weighted = none ↔ weighted = [] := by
  cases weighted <;> simp [chooseHeaviest]

namespace Store

variable {config : Config} {store : Store preset fork}

/-- The lookup of the state of a checkpoint succeeds exactly when the store holds it. -/
theorem checkpointState_ok_iff {checkpoint : Checkpoint} {state : BeaconState preset fork} :
    store.checkpointState checkpoint = .ok state ↔
      store.checkpointStates[checkpoint]? = some state := by
  unfold checkpointState
  cases store.checkpointStates[checkpoint]? <;>
    simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

/-- Before Gloas a vote supports the pending node of its block. -/
theorem getSupportedNode_of_lt {message : LatestMessage fork} (before : fork < .glamsterdam) :
    store.getSupportedNode message = .ok ⟨message.root, .pending⟩ := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp [getSupportedNode, later, pure, Except.pure]

/-- From Gloas a vote from the slot of its known block supports the pending node of the block. -/
theorem getSupportedNode_of_same_slot {message : LatestMessage fork}
    {block : BeaconBlock preset fork} (gloas : .glamsterdam ≤ fork)
    (found : store.blocks[message.root]? = some block)
    (notLater : message.slot gloas ≤ block.slot) :
    store.getSupportedNode message = .ok ⟨message.root, .pending⟩ := by
  simp [getSupportedNode, gloas, Store.block, found, UInt64.not_lt.mpr notLater, bind, Except.bind,
    pure, Except.pure]

/-- From Gloas a vote from a later slot than its known block supports the full or the empty node.

It is full when the vote says that the payload is present. -/
theorem getSupportedNode_of_lt_slot {message : LatestMessage fork}
    {block : BeaconBlock preset fork} (gloas : .glamsterdam ≤ fork)
    (found : store.blocks[message.root]? = some block) (later : block.slot < message.slot gloas) :
    store.getSupportedNode message =
      .ok ⟨message.root, if message.payloadPresent gloas then .full else .empty⟩ := by
  simp [getSupportedNode, gloas, Store.block, found, later, bind, Except.bind, pure, Except.pure]

/-- From Gloas a vote for a block the store does not hold supports no node. -/
theorem getSupportedNode_of_unknown {message : LatestMessage fork} (gloas : .glamsterdam ≤ fork)
    (missing : store.blocks[message.root]? = none) :
    store.getSupportedNode message = .error (.unknownBlock message.root) := by
  simp [getSupportedNode, gloas, Store.block, missing, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- Before Gloas the children of a node are the pending nodes of the known blocks built on it.

The parent root of each such block is the root of the node. -/
theorem mem_getNodeChildren {node child : ForkChoiceNode} {children : List ForkChoiceNode}
    (before : fork < .glamsterdam) (found : store.getNodeChildren node = .ok children) :
    child ∈ children ↔ child.payloadStatus = .pending ∧
      ∃ block, store.blocks[child.root]? = some block ∧ block.parentRoot = node.root := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [getNodeChildren, later, false_and, ↓reduceDIte, ↓reduceIte, pure, Except.pure,
    Except.ok.injEq] at found
  subst found
  obtain ⟨root, status⟩ := child
  simp only [List.mem_map, List.mem_filter, Prod.exists,
    Std.TreeMap.mem_toList_iff_getElem?_eq_some, decide_eq_true_eq, ForkChoiceNode.mk.injEq]
  constructor
  · rintro ⟨r, block, ⟨found, parent⟩, rfl, rfl⟩
    exact ⟨rfl, block, found, parent⟩
  · rintro ⟨rfl, block, found, parent⟩
    exact ⟨root, block, ⟨found, parent⟩, rfl, rfl⟩

/-- From Gloas the children of a pending node are its empty node, then its full node.

The full node is there only when the store has verified the payload. -/
theorem getNodeChildren_of_pending {node : ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (pending : node.payloadStatus = .pending) :
    store.getNodeChildren node = .ok (⟨node.root, .empty⟩ ::
      if store.isPayloadVerified gloas node.root then [⟨node.root, .full⟩] else []) := by
  simp [getNodeChildren, gloas, pending, pure, Except.pure]

/-- From Gloas the children of an empty or full node are the pending nodes of known blocks.

Each of these blocks has the node's block as parent, and builds on the node's payload status. -/
theorem mem_getNodeChildren_of_gloas {node child : ForkChoiceNode}
    {children : List ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (notPending : node.payloadStatus ≠ .pending)
    (found : store.getNodeChildren node = .ok children) :
    child ∈ children ↔ child.payloadStatus = .pending ∧
      ∃ block parent, store.blocks[child.root]? = some block ∧ block.parentRoot = node.root ∧
        store.blocks[node.root]? = some parent ∧
        parentPayloadStatus block parent = node.payloadStatus := by
  simp only [getNodeChildren, gloas, notPending, and_false, ↓reduceDIte, true_and] at found
  obtain ⟨root, status⟩ := child
  split at found
  · rw [bind_ok_iff] at found
    obtain ⟨parent, parentOk, found⟩ := found
    rw [block_ok_iff] at parentOk
    simp only [pure, Except.pure, Except.ok.injEq] at found
    subst found
    simp only [List.mem_filterMap, List.mem_filter, Prod.exists,
      Std.TreeMap.mem_toList_iff_getElem?_eq_some, decide_eq_true_eq]
    constructor
    · rintro ⟨r, block, ⟨blockFound, parentRoot⟩, choice⟩
      split at choice
      · cases choice
        exact ⟨rfl, block, parent, blockFound, parentRoot, parentOk, ‹_›⟩
      · cases choice
    · rintro ⟨rfl, block, other, blockFound, parentRoot, otherFound, built⟩
      rw [parentOk, Option.some.injEq] at otherFound
      subst otherFound
      exact ⟨root, block, ⟨blockFound, parentRoot⟩, by simp [built]⟩
  · -- No block builds on the node's block, so the node has no child.
    rename_i nonempty
    have empty : (store.blocks.toList.filter fun (_, block) =>
        decide (block.parentRoot = node.root)) = [] := by
      simp only [List.isEmpty_eq_false_iff, Bool.not_eq_true'] at nonempty
      exact Classical.byContradiction nonempty
    simp only [empty, List.map_nil, pure, Except.pure, Except.ok.injEq] at found
    subst found
    simp only [List.not_mem_nil, false_iff, not_and, not_exists]
    intro _ block _ blockFound parentRoot
    have built : (root, block) ∈ store.blocks.toList.filter fun (_, block) =>
        decide (block.parentRoot = node.root) :=
      List.mem_filter.mpr ⟨Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr blockFound,
        by simp [parentRoot]⟩
    rw [empty] at built
    cases built

/-- Before Gloas and without a boost, the weight of a node is its votes in the justified state. -/
theorem getWeight_of_no_boost {node : ForkChoiceNode} (before : fork < .glamsterdam)
    (noBoost : store.proposerBoostRoot = Vector.replicate 32 0) :
    store.getWeight config node =
      store.checkpointState store.justifiedCheckpoint >>= store.getAttestationScore node := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp [getWeight, later, noBoost]

/-- From Gloas the empty and the full node of a block from the previous slot weigh nothing. -/
theorem getWeight_of_payloadDecision {node : ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (decision : store.isPreviousSlotPayloadDecision config node = .ok true) :
    store.getWeight config node = .ok 0 := by
  simp [getWeight, gloas, decision, bind, Except.bind, pure, Except.pure]

/-- From Gloas the weight of a node is its votes in the justified state, without the boost.

The node must not be a payload decision of the previous slot. -/
theorem getWeight_of_not_boost {node : ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (decision : store.isPreviousSlotPayloadDecision config node = .ok false)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false) :
    store.getWeight config node =
      store.checkpointState store.justifiedCheckpoint >>= store.getAttestationScore node := by
  simp only [getWeight, gloas, ↓reduceIte, ↓reduceDIte, decision, noBoost, bind, Except.bind]
  cases store.checkpointState store.justifiedCheckpoint with
  | error e => rfl
  | ok state =>
    cases score : store.getAttestationScore node state <;> simp [score, pure, Except.pure]

/-- The slot after a slot below the last one. -/
private theorem nextSlot_toNat {slot : Slot} (fits : slot.toNat + 1 < 2 ^ 64) :
    (slot + 1).toNat = slot.toNat + 1 := by
  rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt fits]

/-- The checked step to the next slot succeeds below the last slot. -/
private theorem nextSlot_ok {slot : Slot} (fits : slot.toNat + 1 < 2 ^ 64) :
    (Uint64.addChecked slot 1).mapError ForkChoiceError.arith = .ok (slot + 1) := by
  rw [mapError_ok_iff, Uint64.addChecked_ok_iff, nextSlot_toNat fits]
  exact ⟨fits, rfl⟩

/-- Without a boosted block the boost does not apply. -/
theorem shouldApplyProposerBoost_of_zero (gloas : .glamsterdam ≤ fork)
    (noBoost : store.proposerBoostRoot = Vector.replicate 32 0) :
    store.shouldApplyProposerBoost config gloas = .ok false := by
  simp [shouldApplyProposerBoost, noBoost, pure, Except.pure]

/-- The boost applies when the parent is older than the slot before the boosted block. -/
theorem shouldApplyProposerBoost_of_old_parent {block parent : BeaconBlock preset fork}
    (gloas : .glamsterdam ≤ fork) (boosted : store.proposerBoostRoot ≠ Vector.replicate 32 0)
    (found : store.blocks[store.proposerBoostRoot]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (old : parent.slot.toNat + 1 < block.slot.toNat) :
    store.shouldApplyProposerBoost config gloas = .ok true := by
  have fits : parent.slot.toNat + 1 < 2 ^ 64 := Nat.lt_trans old block.slot.toNat_lt
  have older : parent.slot + 1 < block.slot := by
    rw [UInt64.lt_iff_toNat_lt, nextSlot_toNat fits]
    exact old
  simp [shouldApplyProposerBoost, boosted, Store.block, found, parentFound, nextSlot_ok fits,
    older, bind, Except.bind, pure, Except.pure]

/-- The boost applies when the parent of the boosted block is not weak.

The parent is at most one slot older than the boosted block. -/
theorem shouldApplyProposerBoost_of_not_weak {block parent : BeaconBlock preset fork}
    (gloas : .glamsterdam ≤ fork) (boosted : store.proposerBoostRoot ≠ Vector.replicate 32 0)
    (found : store.blocks[store.proposerBoostRoot]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (recent : block.slot.toNat ≤ parent.slot.toNat + 1) (fits : parent.slot.toNat + 1 < 2 ^ 64)
    (notWeak : store.isHeadWeak config block.parentRoot = .ok false) :
    store.shouldApplyProposerBoost config gloas = .ok true := by
  have notOlder : ¬ parent.slot + 1 < block.slot := by
    rw [UInt64.lt_iff_toNat_lt, nextSlot_toNat fits]
    omega
  simp [shouldApplyProposerBoost, boosted, Store.block, found, parentFound, nextSlot_ok fits,
    notOlder, notWeak, bind, Except.bind, pure, Except.pure]

/-- A weighed node is the node, its weight and its tiebreaker. -/
theorem weighNode_ok_iff {node : ForkChoiceNode} {weighed : WeightedNode} :
    store.weighNode config node = .ok weighed ↔ weighed.1 = node ∧
      store.getWeight config node = .ok weighed.2.1 ∧
      store.tiebreaker config node = .ok weighed.2.2 := by
  obtain ⟨n, w, t⟩ := weighed
  unfold weighNode
  cases store.getWeight config node <;> cases store.tiebreaker config node <;>
    simp [bind, Except.bind, pure, Except.pure, eq_comm]

/-- The heaviest child is computed from the weighted children among the given nodes. -/
theorem heaviestChild_eq {nodes : List ForkChoiceNode} {node : ForkChoiceNode}
    {result : Option ForkChoiceNode} (found : store.heaviestChild config nodes node = .ok result) :
    ∃ children weighted, store.getNodeChildren node = .ok children ∧
      (children.filter (· ∈ nodes)).mapM (store.weighNode config) = .ok weighted ∧
      chooseHeaviest weighted = result := by
  unfold heaviestChild at found
  cases hc : store.getNodeChildren node with
  | error e => simp [hc, bind, Except.bind] at found
  | ok children =>
    simp only [hc, bind, Except.bind] at found
    cases hw : (children.filter (· ∈ nodes)).mapM (store.weighNode config) with
    | error e => simp [hw] at found
    | ok weighted =>
      simp only [hw, pure, Except.pure, Except.ok.injEq] at found
      exact ⟨children, weighted, rfl, hw, found⟩

/-- The walk stops at a node with no child among the given nodes. -/
theorem getHeadFrom_leaf {nodes : List ForkChoiceNode} {start head : ForkChoiceNode}
    (walk : store.getHeadFrom config nodes start = .ok head) :
    ∃ children, store.getNodeChildren head = .ok children ∧ ∀ child ∈ children, child ∉ nodes := by
  induction start using getHeadFrom.induct store with
  | _ start ih =>
    rw [getHeadFrom] at walk
    cases found : store.heaviestChild config nodes start with
    | error e => simp [found, bind, Except.bind] at walk
    | ok result =>
      obtain ⟨children, weighted, hc, hw, choice⟩ := heaviestChild_eq found
      cases result with
      | none =>
        simp [found, bind, Except.bind, pure, Except.pure] at walk
        subst walk
        rw [chooseHeaviest_eq_none] at choice
        subst choice
        have empty := List.length_eq_zero_iff.mp (mapM_ok_length hw).symm
        refine ⟨children, hc, fun child mem inNodes => ?_⟩
        have : child ∈ children.filter (· ∈ nodes) := List.mem_filter.mpr ⟨mem, by simpa⟩
        rw [empty] at this
        cases this
      | some child =>
        simp only [found, bind, Except.bind] at walk
        split at walk
        · exact ih child ‹_› walk
        · cases walk

/-- The walk returns its starting node or one of the given nodes. -/
theorem getHeadFrom_mem {nodes : List ForkChoiceNode} {start head : ForkChoiceNode}
    (walk : store.getHeadFrom config nodes start = .ok head) : head = start ∨ head ∈ nodes := by
  induction start using getHeadFrom.induct store with
  | _ start ih =>
    rw [getHeadFrom] at walk
    cases found : store.heaviestChild config nodes start with
    | error e => simp [found, bind, Except.bind] at walk
    | ok result =>
      cases result with
      | none =>
        simp [found, bind, Except.bind, pure, Except.pure] at walk
        exact .inl walk.symm
      | some child =>
        simp only [found, bind, Except.bind] at walk
        split at walk
        · rcases ih child ‹_› walk with same | mem
          · obtain ⟨children, weighted, -, hw, choice⟩ := heaviestChild_eq found
            obtain ⟨key, mem, -⟩ := chooseHeaviest_some choice
            rw [same]
            obtain ⟨source, member, pair⟩ := mapM_ok_mem hw _ mem
            obtain ⟨rfl, -⟩ := weighNode_ok_iff.mp pair
            exact Or.inr (of_decide_eq_true (List.mem_filter.mp member).2)
          · exact .inr mem
        · cases walk

/-- A nonempty list of viable nodes holds the node it starts from. -/
theorem filterNodeTree_self {node : ForkChoiceNode} {nodes : List ForkChoiceNode}
    (walk : store.filterNodeTree config node = .ok nodes) (nonempty : nodes ≠ []) :
    node ∈ nodes := by
  rw [filterNodeTree, bind_ok_iff] at walk
  obtain ⟨children, -, walk⟩ := walk
  split at walk
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at walk
    obtain ⟨isViable, -, rfl⟩ := walk
    cases isViable
    · exact absurd rfl nonempty
    · exact List.mem_singleton_self _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at walk
    obtain ⟨viable, -, rfl⟩ := walk
    split
    · exact absurd (by simp_all) nonempty
    · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- A viable node that has children has a viable child. -/
theorem filterNodeTree_child :
    ∀ {node : ForkChoiceNode} {nodes : List ForkChoiceNode},
      store.filterNodeTree config node = .ok nodes →
      ∀ n ∈ nodes, ∀ {children : List ForkChoiceNode}, store.getNodeChildren n = .ok children →
        children ≠ [] → ∃ child ∈ children, child ∈ nodes := by
  intro node
  induction hrank : store.nodeRank node using Nat.strongRecOn generalizing node with
  | _ rank ih =>
  intro nodes walk n mem nChildren nChildrenOk nonempty
  rw [filterNodeTree, bind_ok_iff] at walk
  obtain ⟨children, childrenOk, walk⟩ := walk
  by_cases empty : children.isEmpty
  · simp only [empty, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at walk
    obtain ⟨isViable, -, rfl⟩ := walk
    cases isViable
    · cases mem
    · rw [List.mem_singleton.mp mem, childrenOk, Except.ok.injEq] at nChildrenOk
      subst nChildrenOk
      exact absurd (List.isEmpty_iff.mp empty) nonempty
  simp only [empty, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at walk
  obtain ⟨viable, viableOk, rfl⟩ := walk
  have someViable : viable ≠ [] := fun none => by simp [none] at mem
  simp only [List.isEmpty_iff, someViable, ↓reduceIte] at mem ⊢
  -- Each node below a child of the start is a viable node of the start.
  have below : ∀ x ∈ viable, ∃ child ∈ children, ∃ nodesBelow,
      store.nodeRank child < store.nodeRank node ∧
      store.filterNodeTree config child = .ok nodesBelow ∧ x ∈ nodesBelow ∧
      ∀ y ∈ nodesBelow, y ∈ viable := by
    intro x hx
    obtain ⟨child, childMem, nodesBelow, belowOk, xMem⟩ := (mem_of_flatMapM_ok viableOk x).mp hx
    split at belowOk
    · rename_i lowerRank
      refine ⟨child, childMem, nodesBelow, lowerRank, belowOk, xMem, fun y hy => ?_⟩
      exact (mem_of_flatMapM_ok viableOk y).mpr ⟨child, childMem, nodesBelow, by
        simp [lowerRank, belowOk], hy⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at belowOk
  rcases List.mem_append.mp mem with mem | same
  · obtain ⟨child, -, nodesBelow, lowerRank, belowOk, nMem, lift⟩ := below n mem
    obtain ⟨c, cMem, cIn⟩ :=
      ih _ (hrank ▸ lowerRank) rfl belowOk n nMem nChildrenOk nonempty
    exact ⟨c, cMem, List.mem_append_left _ (lift c cIn)⟩
  · -- The start has a viable child, which leads its own viable nodes.
    rw [List.mem_singleton.mp same, childrenOk, Except.ok.injEq] at nChildrenOk
    subst nChildrenOk
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ someViable
    obtain ⟨child, childMem, nodesBelow, -, belowOk, xMem, lift⟩ := below x hx
    have childIn := filterNodeTree_self belowOk (List.ne_nil_of_mem xMem)
    exact ⟨child, childMem, List.mem_append_left _ (lift child childIn)⟩

/-- From Gloas, when no node is viable, the head is the empty node of the justified block. -/
theorem getHead_of_empty (gloas : .glamsterdam ≤ fork)
    (tree : store.getFilteredNodeTree config = .ok []) :
    store.getHead config = .ok ⟨store.justifiedCheckpoint.root, .empty⟩ := by
  simp [getHead, tree, gloas, bind, Except.bind, pure, Except.pure]

/-- From Gloas the children of the empty node of a block can be computed.

This holds when the viable nodes below the pending node of that block can be computed. -/
theorem getNodeChildren_empty_ok {node : ForkChoiceNode} {nodes : List ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork) (pending : node.payloadStatus = .pending)
    (walk : store.filterNodeTree config node = .ok nodes) :
    ∃ children, store.getNodeChildren ⟨node.root, .empty⟩ = .ok children := by
  rw [filterNodeTree, getNodeChildren_of_pending gloas pending, bind_ok_iff] at walk
  obtain ⟨_, same, walk⟩ := walk
  rw [Except.ok.injEq] at same
  subst same
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at walk
  obtain ⟨_, viable, -⟩ := walk
  rw [List.flatMapM_cons, bind_ok_iff] at viable
  obtain ⟨_, below, -⟩ := viable
  split at below
  · rw [filterNodeTree, bind_ok_iff] at below
    obtain ⟨children, childrenOk, -⟩ := below
    exact ⟨children, childrenOk⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at below

/-- Before Gloas, the walk from a known pending node ends at a node that descends from it.

The walk from the end node back to the slot of the start reaches the start. -/
theorem getAncestor_getHeadFrom (before : fork < .glamsterdam) {nodes : List ForkChoiceNode}
    {start head : ForkChoiceNode} (walk : store.getHeadFrom config nodes start = .ok head)
    (pending : start.payloadStatus = .pending) {startBlock : BeaconBlock preset fork}
    (found : store.blocks[start.root]? = some startBlock) :
    store.getAncestor head startBlock.slot = .ok start := by
  induction start using getHeadFrom.induct store generalizing startBlock with
  | _ start ih =>
    rw [getHeadFrom] at walk
    cases chosen : store.heaviestChild config nodes start with
    | error e => simp [chosen, bind, Except.bind] at walk
    | ok result =>
      cases result with
      | none =>
        simp [chosen, bind, Except.bind, pure, Except.pure] at walk
        subst walk
        exact getAncestor_of_le found (UInt64.le_refl _)
      | some child =>
        simp only [chosen, bind, Except.bind] at walk
        split at walk
        · rename_i lower
          -- The chosen node is a child of the start: a pending node whose parent is the start.
          obtain ⟨children, weighted, hc, hw, choice⟩ := heaviestChild_eq chosen
          obtain ⟨key, mem, -⟩ := chooseHeaviest_some choice
          obtain ⟨source, member, pair⟩ := mapM_ok_mem hw _ mem
          obtain ⟨rfl, -⟩ := weighNode_ok_iff.mp pair
          obtain ⟨childPending, childBlock, childFound, parent⟩ :=
            (mem_getNodeChildren before hc).mp (List.mem_filter.mp member).1
          -- A lower rank between two pending nodes is a higher slot.
          have higher : startBlock.slot < childBlock.slot := by
            dsimp only at childPending childFound
            simp only [nodeRank, childFound, found, childPending, pending, ↓reduceIte] at lower
            have := childBlock.slot.toNat_lt
            have := startBlock.slot.toNat_lt
            rw [UInt64.lt_iff_toNat_lt]
            omega
          have upper := ih child lower walk childPending childFound
          rw [getAncestor_trans (UInt64.le_of_lt higher) upper,
            getAncestor_step childFound (UInt64.not_le.mpr higher) (parent ▸ found) higher,
            parentPayloadStatus_of_lt before, parent, ← pending,
            getAncestor_of_le found (UInt64.le_refl _)]
        · cases walk

/-- A node whose viable subtree can be computed is a known block.

An unknown node has no voting source, and no child can rank below it. -/
theorem filterNodeTree_known {node : ForkChoiceNode} {nodes : List ForkChoiceNode}
    (walk : store.filterNodeTree config node = .ok nodes) :
    ∃ block, store.blocks[node.root]? = some block := by
  cases found : store.blocks[node.root]? with
  | some block => exact ⟨block, rfl⟩
  | none =>
  exfalso
  rw [filterNodeTree, bind_ok_iff] at walk
  obtain ⟨children, -, walk⟩ := walk
  cases children with
  | nil =>
    simp only [List.isEmpty_nil, ↓reduceIte, bind_ok_iff] at walk
    obtain ⟨_, viable, -⟩ := walk
    simp only [isViableLeaf, getVotingSource, Store.block, found, bind_ok_iff] at viable
    simp [throw, throwThe, MonadExceptOf.throw] at viable
  | cons child rest =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at walk
    obtain ⟨_, viable, -⟩ := walk
    rw [List.flatMapM_cons, bind_ok_iff] at viable
    obtain ⟨_, below, -⟩ := viable
    simp [nodeRank, found, throw, throwThe, MonadExceptOf.throw] at below

/-- Before Gloas, the head descends from the justified checkpoint block. -/
theorem isAncestor_getHead (before : fork < .glamsterdam) {head : ForkChoiceNode}
    (found : store.getHead config = .ok head) :
    store.isAncestor head ⟨store.justifiedCheckpoint.root, .pending⟩ = .ok true := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  unfold getHead at found
  cases tree : store.getFilteredNodeTree config with
  | error e => simp [tree, bind, Except.bind] at found
  | ok nodes =>
    -- The walk from the justified node succeeded, so its block is known.
    obtain ⟨justifiedBlock, justifiedFound⟩ := filterNodeTree_known tree
    simp only [tree, bind, Except.bind, later, false_and, ↓reduceIte] at found
    have walked := getAncestor_getHeadFrom before found rfl justifiedFound
    simp [isAncestor, block_ok_iff.mpr justifiedFound, walked, later, bind, Except.bind, pure,
      Except.pure]

/-- From Gloas, the walk from a known node ends at a node that descends from it.

From a pending start, the walk back to the slot of the start reaches a node of the same block.

From an empty or full start, the walk back to the slot of the start reaches the start itself. -/
theorem getAncestor_getHeadFrom_of_gloas (gloas : .glamsterdam ≤ fork)
    {nodes : List ForkChoiceNode} {start head : ForkChoiceNode}
    (walk : store.getHeadFrom config nodes start = .ok head)
    {startBlock : BeaconBlock preset fork}
    (found : store.blocks[start.root]? = some startBlock) :
    ∃ ancestor, store.getAncestor head startBlock.slot = .ok ancestor ∧
      ancestor.root = start.root ∧
      (ancestor.payloadStatus = start.payloadStatus ∨ start.payloadStatus = .pending) := by
  induction start using getHeadFrom.induct store generalizing startBlock with
  | _ start ih =>
    rw [getHeadFrom] at walk
    cases chosen : store.heaviestChild config nodes start with
    | error e => simp [chosen, bind, Except.bind] at walk
    | ok result =>
      cases result with
      | none =>
        simp [chosen, bind, Except.bind, pure, Except.pure] at walk
        subst walk
        exact ⟨start, getAncestor_of_le found (UInt64.le_refl _), rfl, .inl rfl⟩
      | some child =>
        simp only [chosen, bind, Except.bind] at walk
        split at walk
        · rename_i lower
          obtain ⟨children, weighted, hc, hw, choice⟩ := heaviestChild_eq chosen
          obtain ⟨key, mem, -⟩ := chooseHeaviest_some choice
          obtain ⟨source, member, pair⟩ := mapM_ok_mem hw _ mem
          have same : source = child := (weighNode_ok_iff.mp pair).1.symm
          subst same
          have childMem := (List.mem_filter.mp member).1
          by_cases pending : start.payloadStatus = .pending
          · -- A pending node steps to its empty or its full node on the same block.
            rw [getNodeChildren_of_pending gloas pending, Except.ok.injEq] at hc
            subst hc
            have sameRoot : source.root = start.root := by
              split at childMem
              · rcases List.mem_cons.mp childMem with rfl | memFull
                · rfl
                · rw [List.mem_singleton.mp memFull]
              · rw [List.mem_singleton.mp childMem]
            obtain ⟨ancestor, walked, rootEq, -⟩ := ih source lower walk (sameRoot ▸ found)
            exact ⟨ancestor, walked, rootEq.trans sameRoot, .inr pending⟩
          · -- An empty or full node steps to the pending node of a block built on it.
            obtain ⟨childPending, childBlock, parentBlock, childFound, parent, parentFound,
              built⟩ := (mem_getNodeChildren_of_gloas gloas pending hc).mp childMem
            rw [found, Option.some.injEq] at parentFound
            subst parentFound
            have higher : startBlock.slot < childBlock.slot := by
              simp only [nodeRank, childFound, found, childPending, pending, ↓reduceIte] at lower
              have := childBlock.slot.toNat_lt
              have := startBlock.slot.toNat_lt
              rw [UInt64.lt_iff_toNat_lt]
              omega
            obtain ⟨ancestor, upper, rootEq, -⟩ := ih source lower walk childFound
            have step : store.getAncestor head startBlock.slot = .ok start := by
              rw [getAncestor_trans (UInt64.le_of_lt higher) upper,
                getAncestor_step (rootEq ▸ childFound) (UInt64.not_le.mpr higher)
                  (parent ▸ found) higher,
                built, parent, getAncestor_of_le found (UInt64.le_refl _)]
            exact ⟨start, step, rfl, .inl rfl⟩
        · cases walk

/-- From Gloas, the walk from a known node ends at a descendant of that node. -/
theorem isAncestor_getHeadFrom_of_gloas (gloas : .glamsterdam ≤ fork)
    {nodes : List ForkChoiceNode} {start head : ForkChoiceNode}
    (walk : store.getHeadFrom config nodes start = .ok head)
    {startBlock : BeaconBlock preset fork}
    (found : store.blocks[start.root]? = some startBlock) :
    store.isAncestor head start = .ok true := by
  obtain ⟨ancestor, walked, rootEq, statusOk⟩ :=
    getAncestor_getHeadFrom_of_gloas gloas walk found
  rcases statusOk with statusEq | pending
  · simp [isAncestor, block_ok_iff.mpr found, walked, gloas, rootEq, statusEq, bind, Except.bind,
      pure, Except.pure]
  · simp [isAncestor, block_ok_iff.mpr found, walked, gloas, rootEq, pending, bind, Except.bind,
      pure, Except.pure]

/-- From Gloas, the head descends from the justified checkpoint block. -/
theorem isAncestor_getHead_of_gloas (gloas : .glamsterdam ≤ fork) {head : ForkChoiceNode}
    (found : store.getHead config = .ok head) :
    store.isAncestor head ⟨store.justifiedCheckpoint.root, .pending⟩ = .ok true := by
  unfold getHead at found
  cases tree : store.getFilteredNodeTree config with
  | error e => simp [tree, bind, Except.bind] at found
  | ok nodes =>
    obtain ⟨justifiedBlock, justifiedFound⟩ := filterNodeTree_known tree
    dsimp only at justifiedFound
    simp only [tree, bind, Except.bind] at found
    split at found
    · simp only [pure, Except.pure, Except.ok.injEq] at found
      subst found
      have self := getAncestor_of_le (node := ⟨store.justifiedCheckpoint.root, .empty⟩)
        justifiedFound (UInt64.le_refl _)
      simp [isAncestor, block_ok_iff.mpr justifiedFound, self, gloas, bind, Except.bind, pure,
        Except.pure]
    · exact isAncestor_getHeadFrom_of_gloas gloas found justifiedFound

/-- At every fork, the head descends from the justified checkpoint block. -/
theorem isAncestor_getHead_all {head : ForkChoiceNode}
    (found : store.getHead config = .ok head) :
    store.isAncestor head ⟨store.justifiedCheckpoint.root, .pending⟩ = .ok true := by
  by_cases gloas : .glamsterdam ≤ fork
  · exact isAncestor_getHead_of_gloas gloas found
  · exact isAncestor_getHead (Nat.lt_of_not_le gloas) found

/-- The head has no child among the viable nodes. -/
theorem getHead_leaf {head : ForkChoiceNode} (found : store.getHead config = .ok head) :
    ∃ nodes children, store.getFilteredNodeTree config = .ok nodes ∧
      store.getNodeChildren head = .ok children ∧ ∀ child ∈ children, child ∉ nodes := by
  unfold getHead at found
  cases tree : store.getFilteredNodeTree config with
  | error e => simp [tree, bind, Except.bind] at found
  | ok nodes =>
    simp only [tree, bind, Except.bind] at found
    split at found
    · rename_i empty
      simp only [pure, Except.pure, Except.ok.injEq] at found
      subst found
      obtain ⟨children, childrenOk⟩ := getNodeChildren_empty_ok empty.1 rfl tree
      exact ⟨nodes, children, rfl, childrenOk, fun _ _ inNodes => by
        simp [List.isEmpty_iff.mp empty.2] at inNodes⟩
    · obtain ⟨children, childrenOk, leaf⟩ := getHeadFrom_leaf found
      exact ⟨nodes, children, rfl, childrenOk, leaf⟩

/-- From Gloas the head is never a pending node. -/
theorem getHead_ne_pending {head : ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (found : store.getHead config = .ok head) : head.payloadStatus ≠ .pending := by
  intro pending
  unfold getHead at found
  cases tree : store.getFilteredNodeTree config with
  | error e => simp [tree, bind, Except.bind] at found
  | ok nodes =>
    simp only [tree, bind, Except.bind] at found
    split at found
    · simp only [pure, Except.pure, Except.ok.injEq] at found
      subst found
      cases pending
    · rename_i notEmpty
      have nonempty : nodes ≠ [] := fun nil => notEmpty ⟨gloas, by simp [nil]⟩
      -- The head is a viable node: the justified block leads a nonempty list of viable nodes.
      have headIn : head ∈ nodes := by
        rcases getHeadFrom_mem found with rfl | mem
        · exact filterNodeTree_self tree nonempty
        · exact mem
      obtain ⟨children, childrenOk, leaf⟩ := getHeadFrom_leaf found
      have someChild : children ≠ [] := by
        rw [getNodeChildren_of_pending gloas pending, Except.ok.injEq] at childrenOk
        simp [← childrenOk]
      obtain ⟨child, childMem, childIn⟩ :=
        filterNodeTree_child tree head headIn childrenOk someChild
      exact leaf child childMem childIn

/-- From Gloas the empty and the full node of a block from the previous slot are a decision. -/
theorem isPreviousSlotPayloadDecision_of_previous {root : Root} {status : PayloadStatus}
    {block : BeaconBlock preset fork} {next : Slot}
    (found : store.blocks[root]? = some block) (nextOk : Uint64.addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next) (decided : status ≠ .pending) :
    store.isPreviousSlotPayloadDecision config ⟨root, status⟩ = .ok true := by
  cases status <;>
    simp_all [isPreviousSlotPayloadDecision, Store.block, Except.mapError, bind, Except.bind,
      pure, Except.pure]

/-- From Gloas, a verified block from the previous slot with both nodes among the viable ones.

The walk then takes its full node exactly when the payload extends, and its empty node otherwise.

Both nodes weigh nothing and have the same root, so the tiebreaker decides. -/
theorem heaviestChild_of_previousSlot {gloas : .glamsterdam ≤ fork}
    {nodes : List ForkChoiceNode} {root : Root} {block : BeaconBlock preset fork} {next : Slot}
    {extend : Bool} (found : store.blocks[root]? = some block)
    (nextOk : Uint64.addChecked block.slot 1 = .ok next)
    (current : store.getCurrentSlot config = .ok next)
    (verified : store.isPayloadVerified gloas root = true)
    (emptyIn : ⟨root, .empty⟩ ∈ nodes) (fullIn : ⟨root, .full⟩ ∈ nodes)
    (extendOk : store.shouldExtendPayload config gloas root = .ok extend) :
    store.heaviestChild config nodes ⟨root, .pending⟩ =
      .ok (some ⟨root, if extend then .full else .empty⟩) := by
  have emptyDecision := isPreviousSlotPayloadDecision_of_previous (status := .empty) found nextOk
    current (by decide)
  have fullDecision := isPreviousSlotPayloadDecision_of_previous (status := .full) found nextOk
    current (by decide)
  have emptyWeighed : store.weighNode config ⟨root, .empty⟩ = .ok (⟨root, .empty⟩, 0, 1) :=
    weighNode_ok_iff.mpr ⟨rfl, getWeight_of_payloadDecision gloas emptyDecision, by
      simp [tiebreaker, gloas, getPayloadStatusTiebreaker, emptyDecision, bind, Except.bind,
        pure, Except.pure]⟩
  have fullWeighed : store.weighNode config ⟨root, .full⟩ =
      .ok (⟨root, .full⟩, 0, if extend then 2 else 0) :=
    weighNode_ok_iff.mpr ⟨rfl, getWeight_of_payloadDecision gloas fullDecision, by
      cases extend <;> simp [tiebreaker, gloas, getPayloadStatusTiebreaker, fullDecision,
        extendOk, bind, Except.bind, pure, Except.pure]⟩
  unfold heaviestChild
  rw [getNodeChildren_of_pending gloas rfl]
  simp only [verified, ite_true, List.filter_cons, emptyIn, fullIn, decide_true,
    List.filter_nil, List.mapM_cons, List.mapM_nil, emptyWeighed, fullWeighed, bind,
    Except.bind, pure, Except.pure]
  -- The tiebreakers compare as numbers: 1 is above 0 and below 2.
  have above : compare (1 : UInt8) 0 = .gt := rfl
  have below : compare (1 : UInt8) 2 = .lt := rfl
  cases extend <;> simp [chooseHeaviest, heavier, compareWeighted, compareLex, compareOn,
    Std.ReflCmp.compare_self, above, below]

end Store

end EthLib.Consensus
